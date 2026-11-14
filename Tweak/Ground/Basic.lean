/-!
# Ground TWEAK: propositions, steps, execution

Chapman (1985), *Planning for Conjunctive Goals*, MIT AI-TR-802, §2.1 (pp. 5–7) and §A.1
(pp. 38–39). Page numbers are the report's.

This file is the variable-free ("ground") tier: every element of every proposition is a
constant, so codesignation is equality and `Lit α` stands for a proposition with its content
abstracted to an atom `α`. SIMPLIFIED: variables and codesignation constraints are not modeled
here (postulate P2 in `notes/POSTULATES.md`); they come in a later tier.

* A proposition is an atom, negated or not (postulate P1, p. 5).
* A situation is a set of propositions (p. 6), here a list read as a set.
* Executing a step: "the output situation is just the input situation minus any propositions
  denied by the step, plus any propositions asserted by the step" (postulate P3, p. 6).
* A complete plan is a total order on steps (p. 5), here a list.

The headline result is Chapman's *truth criterion for complete plans* (p. 39), proved as
`Tweak.Ground.mem_run_iff`, and his *time's arrow lemma* (p. 38), `run_append`.
-/

set_option linter.unusedSectionVars false

namespace Tweak.Ground

/-- **A proposition** (postulate P1, p. 5): a content, here an atom, negated or not. -/
structure Lit (α : Type) where
  atom : α
  pos : Bool
  deriving DecidableEq, Repr

variable {α : Type}

/-- The negation of a proposition: same content, the other sign (p. 5). -/
def Lit.neg (l : Lit α) : Lit α := ⟨l.atom, !l.pos⟩

@[simp] theorem Lit.neg_neg (l : Lit α) : l.neg.neg = l := by
  cases l; simp [Lit.neg]

theorem Lit.neg_ne (l : Lit α) : l.neg ≠ l := by
  cases l with
  | mk a b => cases b <;> simp [Lit.neg]

variable [DecidableEq α]

/-- **A step** (p. 5): finitely many preconditions and postconditions. -/
structure Step (α : Type) where
  pre : List (Lit α)
  post : List (Lit α)
  deriving Repr

/-- A step *asserts* `p` if `p` is among its postconditions; it *denies* `p` if it asserts the
negation of `p` (p. 6). -/
def Step.Asserts (x : Step α) (p : Lit α) : Prop := p ∈ x.post
def Step.Denies (x : Step α) (p : Lit α) : Prop := p.neg ∈ x.post

instance (x : Step α) (p : Lit α) : Decidable (x.Asserts p) := by unfold Step.Asserts; infer_instance
instance (x : Step α) (p : Lit α) : Decidable (x.Denies p) := by unfold Step.Denies; infer_instance

/-- **Well-formed** steps: "It's illegal for a proposition to be both asserted and denied in a
situation" (p. 6), so no step asserts and denies the same proposition. -/
def Step.WF (x : Step α) : Prop := ∀ p, x.Asserts p → ¬ x.Denies p

/-- **Execution of a step** (postulate P3, p. 6): the input situation minus what the step
denies, plus what it asserts. -/
def apply (st : List (Lit α)) (x : Step α) : List (Lit α) :=
  st.filter (fun l => decide (l.neg ∉ x.post)) ++ x.post

theorem mem_apply {st : List (Lit α)} {x : Step α} {p : Lit α} :
    p ∈ apply st x ↔ x.Asserts p ∨ (p ∈ st ∧ ¬ x.Denies p) := by
  simp [apply, Step.Asserts, Step.Denies, List.mem_filter]
  constructor
  · rintro (⟨h1, h2⟩ | h) <;> simp_all
  · rintro (h | ⟨h1, h2⟩) <;> simp_all

/-- **Execution of a complete plan** from a situation: the steps in order (p. 6). The steps are
given as indices `l` into a step table `st`, so that plans may repeat a step template. -/
def run {ι : Type} (st : ι → Step α) (init : List (Lit α)) (l : List ι) : List (Lit α) :=
  l.foldl (fun s i => apply s (st i)) init

variable {ι : Type} (st : ι → Step α) (init : List (Lit α))

@[simp] theorem run_nil : run st init [] = init := rfl

/-- **Time's arrow** (p. 38): what holds after a prefix of a plan depends only on that prefix;
running the rest continues from there. In the list formulation this is definitional. -/
theorem run_append (l₁ l₂ : List ι) : run st init (l₁ ++ l₂) = run st (run st init l₁) l₂ := by
  simp [run, List.foldl_append]

@[simp] theorem run_snoc (l : List ι) (i : ι) :
    run st init (l ++ [i]) = apply (run st init l) (st i) := by
  simp [run]

/-- Induction from the right end of a list. -/
theorem snoc_induction {β : Type} {P : List β → Prop} (nil : P [])
    (snoc : ∀ l x, P l → P (l ++ [x])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x r ih => simpa using snoc _ x ih

/-- **The truth criterion for complete plans** (Chapman p. 39): `p` is true after a complete
plan iff it is asserted somewhere — in the initial situation, or by a step — and no later step
denies it. A theorem about the execution model P3, with no idealization. -/
theorem mem_run_iff (p : Lit α) (l : List ι) :
    p ∈ run st init l ↔
      (p ∈ init ∧ ∀ i ∈ l, ¬ (st i).Denies p) ∨
      ∃ a i b, l = a ++ i :: b ∧ (st i).Asserts p ∧ ∀ j ∈ b, ¬ (st j).Denies p := by
  induction l using snoc_induction with
  | nil =>
    simp only [run_nil, List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · exact Or.inl
    · rintro (h | ⟨a, i, b, h, -⟩)
      · exact h
      · simp at h
  | snoc l x ih =>
    rw [run_snoc, mem_apply, ih]
    constructor
    · rintro (hx | ⟨hl, hd⟩)
      · exact Or.inr ⟨l, x, [], rfl, hx, by simp⟩
      · rcases hl with ⟨hi, hn⟩ | ⟨a, i, b, rfl, ha, hn⟩
        · left
          refine ⟨hi, fun j hj => ?_⟩
          rcases List.mem_append.1 hj with hj | hj
          · exact hn j hj
          · simp at hj; subst hj; exact hd
        · right
          refine ⟨a, i, b ++ [x], by simp, ha, fun j hj => ?_⟩
          rcases List.mem_append.1 hj with hj | hj
          · exact hn j hj
          · simp at hj; subst hj; exact hd
    · rintro (⟨hi, hn⟩ | ⟨a, i, b, hab, ha, hn⟩)
      · right
        exact ⟨Or.inl ⟨hi, fun j hj => hn j (by simp [hj])⟩, hn x (by simp)⟩
      · -- the asserting step is `x` itself, or lies in `l`
        rcases List.append_eq_append_iff.1 hab.symm with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
        · -- `l = a ++ c` and `i :: b = c ++ [x]`
          cases c with
          | nil =>
            simp at hc2
            obtain ⟨rfl, -⟩ := hc2
            exact Or.inl ha
          | cons c0 cs =>
            simp at hc2
            obtain ⟨rfl, rfl⟩ := hc2
            right
            refine ⟨Or.inr ⟨a, _, cs, hc1, ha, fun j hj => hn j (by simp [hj])⟩,
              hn x (by simp)⟩
        · -- `a = l ++ c` and `[x] = c ++ i :: b`: so `c = []`, `i = x`
          cases c with
          | nil =>
            simp at hc2
            obtain ⟨rfl, -⟩ := hc2
            exact Or.inl ha
          | cons c0 cs => simp at hc2

/-- Only an asserted proposition is ever true: `p` holds after a plan only if it held
initially or some step of the plan asserts it. -/
theorem mem_run_source {p : Lit α} {l : List ι} (h : p ∈ run st init l) :
    p ∈ init ∨ ∃ i ∈ l, (st i).Asserts p := by
  rcases (mem_run_iff st init p l).1 h with ⟨hi, -⟩ | ⟨a, i, b, rfl, ha, -⟩
  · exact Or.inl hi
  · exact Or.inr ⟨i, by simp, ha⟩

/-- **A sufficient condition for truth after a complete plan**, the form used in the modal
truth criterion: an assertion exists, and every step that denies `p` is followed by a step that
asserts it. -/
theorem mem_run_of_covered {p : Lit α} :
    ∀ (l : List ι), (p ∈ init ∨ ∃ i ∈ l, (st i).Asserts p) →
      (∀ a i b, l = a ++ i :: b → (st i).Denies p → ∃ w ∈ b, (st w).Asserts p) →
      p ∈ run st init l := by
  intro l
  induction l using snoc_induction with
  | nil =>
    intro hest _
    rcases hest with h | ⟨i, hi, -⟩
    · exact h
    · simp at hi
  | snoc l x ih =>
    intro hest hcov
    rw [run_snoc, mem_apply]
    by_cases hx : (st x).Asserts p
    · exact Or.inl hx
    by_cases hd : (st x).Denies p
    · obtain ⟨w, hw, -⟩ := hcov l x [] rfl hd
      simp at hw
    refine Or.inr ⟨ih ?_ ?_, hd⟩
    · rcases hest with h | ⟨i, hi, ha⟩
      · exact Or.inl h
      · rcases List.mem_append.1 hi with hi | hi
        · exact Or.inr ⟨i, hi, ha⟩
        · simp at hi; subst hi; exact absurd ha hx
    · intro a i b hab hdi
      obtain ⟨w, hw, ha⟩ := hcov a i (b ++ [x]) (by simp [hab]) hdi
      rcases List.mem_append.1 hw with hw | hw
      · exact ⟨w, hw, ha⟩
      · simp at hw; subst hw; exact absurd ha hx

/-- A situation is **consistent** if it does not contain a proposition and its negation (p. 7:
"input and output situations must be consistent sets of propositions"). -/
def Consistent (s : List (Lit α)) : Prop := ∀ p, p ∈ s → p.neg ∉ s

/-- Execution preserves consistency when steps are well-formed. -/
theorem consistent_run (hwf : ∀ i, (st i).WF) (hinit : Consistent init) :
    ∀ l, Consistent (run st init l) := by
  intro l
  induction l using snoc_induction with
  | nil => simpa using hinit
  | snoc l x ih =>
    intro p hp hnp
    rw [run_snoc, mem_apply] at hp hnp
    simp only [Step.Denies, Lit.neg_neg] at hp hnp
    rcases hp with hp | ⟨hp, hnd⟩ <;> rcases hnp with hnp | ⟨hnp, hnd'⟩
    · exact hwf x p hp hnp
    · exact hnd' hp
    · exact hnd hnp
    · exact ih p hp hnp

end Tweak.Ground
