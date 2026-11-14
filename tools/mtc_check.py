#!/usr/bin/env python3
"""Python prototype of the ground (variable-free) TWEAK plan semantics, with the same
semantics as Tweak/Ground/*.lean.

  * A literal is (atom, positive?).  A situation is a set of literals.
  * Executing a step: out = {l in in | neg l not in post} | post   (Chapman p. 6).
  * A partial plan: steps 0..n-1, constraints (a, b) meaning a before b, an initial situation.
    lt = transitive closure of the constraints.  A completion is a linear extension.
  * p is necessarily (possibly) true at the input situation of step s if it is in the state
    reached by running the prefix before s in every (some) completion.

Checks:
  1. The ground modal truth criterion (necessary truth) agrees with brute force on random plans.
  2. The "simple" criterion (establisher with no possibly-intervening denier) is sufficient but
     not necessary, even without variables; the witness used in Tweak/Ground/Examples.lean.
  3. The possible-truth criterion obtained by "switching the modalities" (p. 9) is not sound:
     the witness used in Tweak/Ground/Examples.lean; and how often it fails on random plans.

Run: python3 tools/mtc_check.py
"""
import itertools, random

def neg(l): return (l[0], not l[1])

def apply(state, post):
    post = set(post)
    return {l for l in state if neg(l) not in post} | post

def closure(n, cons):
    lt = set(cons)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(lt):
            for (c, d) in list(lt):
                if b == c and (a, d) not in lt:
                    lt.add((a, d)); changed = True
    return lt

def completions(n, lt):
    for perm in itertools.permutations(range(n)):
        pos = {x: i for i, x in enumerate(perm)}
        if all(pos[a] < pos[b] for (a, b) in lt):
            yield perm

def state_before(init, posts, perm, s):
    st = set(init)
    for x in perm:
        if x == s: return st
        st = apply(st, posts[x])
    raise ValueError

def nec_true(init, posts, lt, n, s, p):
    return all(p in state_before(init, posts, c, s) for c in completions(n, lt))

def poss_true(init, posts, lt, n, s, p):
    return any(p in state_before(init, posts, c, s) for c in completions(n, lt))

def mtc(init, posts, lt, n, s, p):
    """Chapman's necessary truth criterion, ground: an establisher (the initial situation, or a
    step necessarily before s asserting p) and, for every step possibly before s denying p, a
    white knight necessarily between it and s asserting p."""
    est = p in init or any((t, s) in lt and p in posts[t] for t in range(n))
    for c in range(n):
        if c != s and (s, c) not in lt and neg(p) in posts[c]:
            if not any((c, w) in lt and (w, s) in lt and p in posts[w] for w in range(n)):
                return False
    return est

def simple(init, posts, lt, n, s, p):
    """The sufficient-but-not-necessary criterion of p. 8: a necessary establisher t with no
    step possibly between t and s possibly denying p."""
    def ok_after(t):  # t = None: initial situation
        for c in range(n):
            if c == s or c == t or (s, c) in lt or neg(p) not in posts[c]: continue
            if t is not None and (c, t) in lt: continue
            return False
        return True
    if p in init and ok_after(None): return True
    return any((t, s) in lt and p in posts[t] and ok_after(t) for t in range(n))

def switched(init, posts, lt, n, s, p):
    """'Switch the modalities' (p. 9): an establisher possibly before s possibly asserting p,
    and for every step necessarily before s denying p a step possibly between it and s
    asserting p."""
    est = p in init or any(t != s and (s, t) not in lt and p in posts[t] for t in range(n))
    for c in range(n):
        if (c, s) in lt and neg(p) in posts[c]:
            if not any(w != c and w != s and (w, c) not in lt and (s, w) not in lt and p in posts[w]
                       for w in range(n)):
                return False
    return est

def random_plan(rng, n, atoms=2):
    lits = [(a, b) for a in range(atoms) for b in (True, False)]
    posts = []
    for _ in range(n):
        post = set()
        for a in range(atoms):
            r = rng.random()
            if r < 0.3: post.add((a, True))
            elif r < 0.6: post.add((a, False))
        posts.append(post)
    order = list(range(n)); rng.shuffle(order)
    cons = {(order[i], order[j]) for i in range(n) for j in range(i + 1, n) if rng.random() < 0.3}
    init = {(a, rng.random() < 0.5) for a in range(atoms)}
    return init, posts, closure(n, cons)

def main():
    rng = random.Random(1985)
    trials = sw_bad = simple_miss = 0
    for _ in range(4000):
        n = rng.randint(1, 6)
        init, posts, lt = random_plan(rng, n)
        for s in range(n):
            for p in [(0, True), (0, False), (1, True)]:
                trials += 1
                nt = nec_true(init, posts, lt, n, s, p)
                assert nt == mtc(init, posts, lt, n, s, p), (init, posts, lt, s, p)
                if simple(init, posts, lt, n, s, p): assert nt
                elif nt: simple_miss += 1
                pt = poss_true(init, posts, lt, n, s, p)
                if pt: assert switched(init, posts, lt, n, s, p)   # switched is necessary
                elif switched(init, posts, lt, n, s, p): sw_bad += 1
    print(f"1. ground MTC == brute-force necessary truth on {trials} random queries")
    print(f"   simple criterion missed {simple_miss} necessary truths; "
          f"switched criterion claimed {sw_bad} false possible truths")

    # 2. White knights needed without variables. Steps: 0 A asserts p, 1 B asserts p,
    #    2 C denies p, 3 D denies p, 4 S. C<A, D<B, all < S.
    P = (0, True)
    posts = [{P}, {P}, {neg(P)}, {neg(P)}, set()]
    lt = closure(5, {(2, 0), (3, 1)} | {(i, 4) for i in range(4)})
    print("2. white-knight witness: nec_true =", nec_true(set(), posts, lt, 5, 4, P),
          " mtc =", mtc(set(), posts, lt, 5, 4, P), " simple =", simple(set(), posts, lt, 5, 4, P))

    # 3. Switched possible-truth criterion unsound. 0 A asserts p, 1 B asserts p, 2 C denies,
    #    3 D denies, 4 S; A<D, B<C, all < S.
    lt = closure(5, {(0, 3), (1, 2)} | {(i, 4) for i in range(4)})
    print("3. switched-criterion witness: poss_true =", poss_true(set(), posts, lt, 5, 4, P),
          " switched =", switched(set(), posts, lt, 5, 4, P),
          " nec_true(~p) =", nec_true(set(), posts, lt, 5, 4, neg(P)))

if __name__ == "__main__":
    main()
