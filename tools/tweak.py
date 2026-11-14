#!/usr/bin/env python3
"""Ground TWEAK (Chapman 1985, §2.2-2.3 and appendix B), executable.

Semantics as in Tweak/Ground/*.lean and tools/mtc_check.py: literals (atom, sign); a step
asserts its postconditions and denies their negations; necessary truth is decided by the
ground modal truth criterion (proved equivalent in Tweak.Ground.mtc_iff).

The goal-achievement procedure is the paper's diagram (p. 11) without variables, so without
separation:  establish p at s with an existing situation (initial, or a step not necessarily
after s) or a new step, constraining it before s; then for each clobberer C either promote
(s < C) or add a white knight W (existing or new) with C < W < s.  The top level chooses an
unachieved goal and applies the procedure; search is breadth-first over plans (p. 13).

Experiments:
  1. The Sussman anomaly: TWEAK finds the three-step plan of p. 17.
  2. Completeness, empirically (the correctness/completeness theorem, p. 13): on random small
     ground domains, TWEAK (bounded breadth-first search) finds a plan exactly when brute-force
     linear search finds a solution.  (Bounds: plan steps <= 4.)
  3. The outcomes lemma's looping problem (p. 44): the search space keeps growing.

Run: python3 tools/tweak.py
"""
import itertools, random
from collections import deque

def neg(l): return (l[0], not l[1])

class Plan:
    """steps[0] is the finish step (pre = goals); others are template ids.
    order: frozenset of (a, b), transitively closed, a before b."""
    def __init__(self, steps, order):
        self.steps, self.order = steps, order
    def key(self):
        return (self.steps, self.order)

def close(order):
    order = set(order)
    while True:
        new = {(a, d) for (a, b) in order for (c, d) in order if b == c} - order
        if not new: return frozenset(order)
        order |= new

def add_before(plan, a, b):
    if a == b or (b, a) in plan.order: return None
    if (a, b) in plan.order: return plan
    return Plan(plan.steps, close(plan.order | {(a, b)}))

def add_step(plan, tid):
    i = len(plan.steps)
    return Plan(plan.steps + (tid,), close(plan.order | {(i, 0)})), i

class Domain:
    def __init__(self, templates, init, goals):
        self.T, self.init, self.goals = templates, set(init), list(goals)
    def pre(self, plan, i): return self.goals if i == 0 else self.T[plan.steps[i]][0]
    def post(self, plan, i): return set() if i == 0 else set(self.T[plan.steps[i]][1])

def clobberers(D, plan, s, p):
    n, lt = len(plan.steps), plan.order
    out = []
    for c in range(n):
        if c != s and (s, c) not in lt and neg(p) in D.post(plan, c):
            if not any((c, w) in lt and (w, s) in lt and p in D.post(plan, w) for w in range(n)):
                out.append(c)
    return out

def nec_true(D, plan, s, p):
    est = p in D.init or any((t, s) in plan.order and p in D.post(plan, t)
                             for t in range(len(plan.steps)))
    return est and not clobberers(D, plan, s, p)

def unachieved(D, plan):
    return [(p, s) for s in range(len(plan.steps)) for p in D.pre(plan, s)
            if not nec_true(D, plan, s, p)]

def declobber(D, plan, s, p, max_steps):
    cl = clobberers(D, plan, s, p)
    if not cl:
        yield plan; return
    c = cl[0]
    q = add_before(plan, s, c)                      # promotion
    if q: yield from declobber(D, q, s, p, max_steps)
    for w in range(1, len(plan.steps)):             # white knight, existing
        if w != c and w != s and p in D.post(plan, w):
            q = add_before(plan, c, w)
            q = q and add_before(q, w, s)
            if q: yield from declobber(D, q, s, p, max_steps)
    if len(plan.steps) - 1 < max_steps:             # white knight, new
        for tid, (_, post) in enumerate(D.T):
            if p in post:
                q, w = add_step(plan, tid)
                q = add_before(q, c, w)
                q = q and add_before(q, w, s)
                if q: yield from declobber(D, q, s, p, max_steps)

def achieve(D, plan, p, s, max_steps):
    cands = []
    if p in D.init: cands.append(plan)              # establisher: initial situation
    for t in range(1, len(plan.steps)):             # simple establishment
        if t != s and p in D.post(plan, t):
            q = add_before(plan, t, s)
            if q: cands.append(q)
    if len(plan.steps) - 1 < max_steps:             # step addition
        for tid, (_, post) in enumerate(D.T):
            if p in post:
                q, t = add_step(plan, tid)
                q = add_before(q, t, s)
                if q: cands.append(q)
    for q in cands:
        yield from declobber(D, q, s, p, max_steps)

def tweak(D, max_steps=4, max_plans=200000, all_goals=True):
    """Breadth-first search over plans. Returns (plan or None, plans examined, exhausted?)."""
    start = Plan((None,), frozenset())
    seen, queue, count = {start.key()}, deque([start]), 0
    while queue:
        plan = queue.popleft(); count += 1
        goals = unachieved(D, plan)
        if not goals: return plan, count, False
        if count > max_plans: return None, count, False
        for (p, s) in (goals if all_goals else goals[:1]):
            for q in achieve(D, plan, p, s, max_steps):
                if q.key() not in seen:
                    seen.add(q.key()); queue.append(q)
    return None, count, True

def linearize(plan):
    n = len(plan.steps)
    for perm in itertools.permutations(range(1, n)):
        pos = {x: i for i, x in enumerate(perm)}; pos[0] = n
        if all(pos[a] < pos[b] for (a, b) in plan.order): return perm

def run_linear(D, seq):
    st = set(D.init)
    for tid in seq:
        pre, post = D.T[tid]
        if not all(q in st for q in pre): return None
        st = {l for l in st if neg(l) not in set(post)} | set(post)
    return st

def linear_solution(D, max_len):
    for k in range(max_len + 1):
        for seq in itertools.product(range(len(D.T)), repeat=k):
            st = run_linear(D, seq)
            if st is not None and all(g in st for g in D.goals): return seq
    return None

# ---------------------------------------------------------------- the Sussman anomaly
def sussman():
    blocks = ['a', 'b', 'c']
    T, names = [], []
    for x, y, z in itertools.permutations(blocks + ['table'], 3):
        if x == 'table' or y == 'table': continue
        T.append(([(('on', x, z), True), (('clear', x), True), (('clear', y), True)],
                  [(('on', x, y), True), (('on', x, z), False), (('clear', y), False),
                   (('clear', z), True)]))
        names.append(f'puton {x} {y}')
    for x, z in itertools.permutations(blocks, 2):
        T.append(([(('on', x, z), True), (('clear', x), True)],
                  [(('on', x, 'table'), True), (('on', x, z), False), (('clear', z), True)]))
        names.append(f'newtower {x}')
    init = [(('on', 'c', 'a'), True), (('on', 'a', 'table'), True), (('on', 'b', 'table'), True),
            (('clear', 'c'), True), (('clear', 'b'), True)]
    goals = [(('on', 'a', 'b'), True), (('on', 'b', 'c'), True)]
    return Domain(T, init, goals), names

def random_domain(rng, atoms=3, ntemp=4):
    lits = [(a, b) for a in range(atoms) for b in (True, False)]
    T = []
    for _ in range(ntemp):
        pre = [l for l in lits if rng.random() < 0.2]
        pre = [l for l in pre if neg(l) not in pre]
        post = []
        for a in range(atoms):
            r = rng.random()
            if r < 0.25: post.append((a, True))
            elif r < 0.5: post.append((a, False))
        T.append((pre, post))
    init = [(a, rng.random() < 0.5) for a in range(atoms)]
    goals = [l for l in lits if rng.random() < 0.25]
    goals = [l for l in goals if neg(l) not in goals] or [lits[0]]
    return Domain(T, init, goals)

def main():
    D, names = sussman()
    plan, count, _ = tweak(D, max_steps=3)
    order = linearize(plan)
    print("1. Sussman anomaly: plan found after examining", count, "plans:",
          [names[plan.steps[i]] for i in order])

    rng = random.Random(802)
    agree = disagree = solvable = 0
    for trial in range(300):
        D = random_domain(rng)
        lin = linear_solution(D, 4)
        plan, count, exhausted = tweak(D, max_steps=4, max_plans=20000)
        found = plan is not None
        if found:  # soundness: some completion is a solution
            seq = [plan.steps[i] for i in linearize(plan)]
            st = run_linear(D, seq)
            assert st is not None and all(g in st for g in D.goals)
        solvable += lin is not None
        if found == (lin is not None): agree += 1
        else:
            disagree += 1
            print("   disagreement:", D.T, D.init, D.goals, lin, found, count, exhausted)
    print(f"2. completeness, empirically: TWEAK and linear search agree on {agree} of "
          f"{agree + disagree} random domains ({solvable} solvable in <= 4 steps); every plan found is a solution")

    init = [('g', False), ('h', False)]; goals = [('g', True), ('h', True)]
    T = [([('h', False)], [('g', True)]), ([('g', False)], [('h', True)])]
    D = Domain(T, init, goals)
    for k in (2, 4, 8):
        plan, count, exhausted = tweak(D, max_steps=k, max_plans=10**6)
        print(f"3a. looping problem as printed (p. 44), plans of <= {k} steps: found={plan is not None}, "
              f"plans examined={count}, space exhausted={exhausted}")
    T = [([], [('g', True), ('h', False)]), ([], [('h', True), ('g', False)])]
    D = Domain(T, init, goals)
    for k in (2, 4, 6, 8):
        plan, count, exhausted = tweak(D, max_steps=k, max_plans=10**6)
        print(f"3b. operators g,~h and h,~g, plans of <= {k} steps: found={plan is not None}, "
              f"plans examined={count}, space exhausted={exhausted}")

if __name__ == "__main__":
    main()
