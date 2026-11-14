import Tweak.Ground.Plan

/-!
# The modal truth criterion, ground

Chapman (1985), §2.1, pp. 8–9; proof in §A.1, pp. 41–43.

> **Modal truth criterion**: A proposition p is necessarily true in a situation s iff two
> conditions hold: there is a situation t equal or necessarily previous to s in which p is
> necessarily asserted; and for every step C possibly before s and every proposition q possibly
> codesignating with p which C denies, there is a step W necessarily between C and s which
> asserts r, a proposition such that r and p codesignate whenever p and q codesignate. (p. 9)

Without variables, codesignation is identity, so "q possibly codesignating with p" is `q = p`
and "r and p codesignate whenever p and q codesignate" is `r = p`. The situations in which
something is asserted are the initial situation and the output situations of steps (input
situations assert nothing; appendix B, `necessarily-asserted-in?`). "Possibly before s" is
`c ≠ s ∧ ¬ s < c`, and "necessarily before" is the order (`necBefore_iff`).

* `mtc_iff`: the criterion is necessary and sufficient for necessary truth, given well-formed
  steps. Sufficiency needs no hypothesis.
* `switched_of_possTrue`: the criterion with "all the modalities switched", which the paper
  offers as the criterion for possible truth (p. 9), is a *necessary* condition for possible
  truth. `Tweak.Ground.Examples.switched_not_sufficient` shows that it is not sufficient.
-/

set_option linter.unusedSectionVars false

namespace Tweak.Ground

variable {α : Type} [DecidableEq α] {n : Nat} (P : PPlan α n)

/-- **An establisher** (p. 9): the initial situation asserts `p`, or a step necessarily before
`s` asserts it. -/
def Establisher (s : Fin n) (p : Lit α) : Prop :=
  p ∈ P.init ∨ ∃ t, P.Lt t s ∧ (P.step t).Asserts p

/-- **A clobberer** of `p` at `s` (p. 9): a step possibly before `s` that denies `p` and has no
white knight, i.e. no step necessarily between it and `s` asserting `p`. -/
def Clobberer (s : Fin n) (p : Lit α) (c : Fin n) : Prop :=
  c ≠ s ∧ ¬ P.Lt s c ∧ (P.step c).Denies p ∧
    ¬ ∃ w, P.Lt c w ∧ P.Lt w s ∧ (P.step w).Asserts p

instance (s : Fin n) (p : Lit α) (c : Fin n) : Decidable (Clobberer P s p c) := by
  unfold Clobberer; infer_instance

/-- **The modal truth criterion** for necessary truth, ground (p. 9). -/
def MTC (s : Fin n) (p : Lit α) : Prop :=
  Establisher P s p ∧ ∀ c, ¬ Clobberer P s p c

instance (s : Fin n) (p : Lit α) : Decidable (MTC P s p) := by
  unfold MTC Establisher Clobberer; infer_instance

/-- **Sufficiency** (p. 43, "the last case"): an establisher and no clobberer make `p`
necessarily true. Postulates P3, P4; no idealization. -/
theorem necTrue_of_mtc {s : Fin n} {p : Lit α} (h : MTC P s p) : NecTrue P s p := by
  intro L hL l₁ l₂ hL12
  have hpw := hL.prefix_pairwise hL12
  apply mem_run_of_covered P.step P.init l₁
  · rcases h.1 with h0 | ⟨t, hts, ht⟩
    · exact Or.inl h0
    · exact Or.inr ⟨t, hL.mem_prefix_of_lt hL12 hts, ht⟩
  · intro a i b hab hd
    have hi : i ∈ l₁ := by simp [hab]
    have hne : i ≠ s := fun e => hL.not_mem_prefix hL12 (e ▸ hi)
    have hwk : ∃ w, P.Lt i w ∧ P.Lt w s ∧ (P.step w).Asserts p :=
      Classical.byContradiction fun hno =>
        h.2 i ⟨hne, hL.not_lt_of_mem_prefix hL12 hi, hd, hno⟩
    obtain ⟨w, hiw, hws, hw⟩ := hwk
    refine ⟨w, ?_, hw⟩
    have hw1 := hL.mem_prefix_of_lt hL12 hws
    rw [hab] at hw1 hpw
    rcases List.mem_append.1 hw1 with hwa | hwb
    · exact absurd hiw ((List.pairwise_append.1 hpw).2.2 w hwa i (by simp))
    · rcases List.mem_cons.1 hwb with rfl | hwb
      · simp [PPlan.Lt, P.irrefl] at hiw
      · exact hwb

/-- No establisher: every completion that puts all steps not necessarily before `s` after it
falsifies `p` (p. 42). -/
theorem not_necTrue_of_not_establisher {s : Fin n} {p : Lit α} (hE : ¬ Establisher P s p) :
    ¬ NecTrue P s p := by
  intro h
  let f : Fin n → Nat := fun x => if P.Lt x s then 0 else if x = s then 1 else 2
  have hf : ∀ a b, P.Lt a b → f a ≤ f b := by
    intro a b hab
    by_cases hb : P.Lt b s
    · have ha : P.Lt a s := P.trans _ _ _ hab hb
      simp [f, PPlan.Lt, ha]
    · by_cases hbs : b = s
      · subst hbs; simp [f, PPlan.Lt, hab]
      · have : f b = 2 := by simp [f, PPlan.Lt, hb, hbs]
        have : f a ≤ 2 := by simp only [f, PPlan.Lt]; split <;> (try split) <;> omega
        omega
  obtain ⟨L, hL, hs⟩ := exists_completion_rank P f hf
  obtain ⟨l₁, l₂, hL12⟩ := hL.split s
  have hfs : f s = 1 := by simp [f, PPlan.Lt, P.irrefl]
  have huniq : ∀ x, f x = f s → x = s := by
    intro x hx
    rw [hfs] at hx
    simp only [f, PPlan.Lt] at hx
    split at hx
    · omega
    · split at hx
      · assumption
      · omega
  rcases mem_run_source P.step P.init (h L hL l₁ l₂ hL12) with h0 | ⟨i, hi, ha⟩
  · exact hE (Or.inl h0)
  · have := (hL.mem_prefix_iff_rank hs hL12 huniq i).1 hi
    rw [hfs] at this
    have hi0 : P.Lt i s := by
      simp only [f, PPlan.Lt] at this
      split at this
      · assumption
      · split at this <;> omega
    exact hE (Or.inr ⟨i, hi0, ha⟩)

/-- A clobberer: the completion that puts `c` before `s`, every step possibly after `s` after
it, every step possibly before `c` before it, falsifies `p` (p. 42). Uses well-formedness of
`c` (it does not also assert `p`). -/
theorem not_necTrue_of_clobberer {s : Fin n} {p : Lit α} {c : Fin n}
    (hc : Clobberer P s p c) (hwf : (P.step c).WF) : ¬ NecTrue P s p := by
  obtain ⟨hcs, hsc, hcd, hnowk⟩ := hc
  intro h
  -- ranks: before c (0), c (1), necessarily between c and s (2), s (3), after (4)
  let f : Fin n → Nat := fun x =>
    if x = c then 1 else if x = s then 3 else if P.Lt c x ∧ P.Lt x s then 2
    else if P.Lt x s ∨ P.Lt x c then 0 else 4
  have tr := P.trans
  have ir : ∀ a, ¬ P.Lt a a := fun a => by simp [PPlan.Lt, P.irrefl]
  have hf : ∀ a b, P.Lt a b → f a ≤ f b := by
    intro a b hab
    have hle4 : ∀ x, f x ≤ 4 := by
      intro x; simp only [f, PPlan.Lt]; split <;> (try split) <;> (try split) <;> (try split) <;> omega
    by_cases hbc : b = c
    · subst hbc
      have hac : a ≠ b := fun e => ir a (e ▸ hab)
      have has : a ≠ s := fun e => hsc (e ▸ hab)
      have hna : ¬ (P.Lt b a ∧ P.Lt a s) := fun ⟨h1, _⟩ => ir b (tr _ _ _ h1 hab)
      have : f a = 0 := by simp [f, PPlan.Lt, hac, has, hna, hab]
      omega
    by_cases hbs : b = s
    · subst hbs
      by_cases hac : a = c
      · subst hac
        have hfa : f a = 1 := by simp [f]
        have hfb : f b = 3 := by simp [f, hcs.symm]
        omega
      have hfa : f a ≤ 2 := by
        simp only [f, PPlan.Lt, hac, ite_false]
        have has : a ≠ b := fun e => ir a (e ▸ hab)
        simp only [has, ite_false]
        split
        · omega
        · simp [hab]
      have : f b = 3 := by simp [f, PPlan.Lt, hcs.symm]
      omega
    by_cases hbm : P.Lt c b ∧ P.Lt b s
    · have hfb : f b = 2 := by simp [f, PPlan.Lt, hbc, hbs, hbm]
      by_cases hac : a = c
      · subst hac
        have : f a = 1 := by simp [f]
        omega
      have has : a ≠ s := fun e => ir s (tr _ _ _ (e ▸ hab) hbm.2)
      have : P.Lt a s := tr _ _ _ hab hbm.2
      have hfa : f a ≤ 2 := by
        simp only [f, PPlan.Lt, hac, has, ite_false]
        split
        · omega
        · simp [this]
      omega
    by_cases hb0 : P.Lt b s ∨ P.Lt b c
    · have hfb : f b = 0 := by simp [f, PPlan.Lt, hbc, hbs, hbm, hb0]
      have hac : a ≠ c := by
        rintro rfl
        rcases hb0 with h1 | h1
        · exact hbm ⟨hab, h1⟩
        · exact ir a (tr _ _ _ hab h1)
      have has : a ≠ s := by
        rintro rfl
        rcases hb0 with h1 | h1
        · exact ir a (tr _ _ _ hab h1)
        · exact hsc (tr _ _ _ hab h1)
      have ham : ¬ (P.Lt c a ∧ P.Lt a s) := by
        rintro ⟨h1, h2⟩
        rcases hb0 with h3 | h3
        · exact hbm ⟨tr _ _ _ h1 hab, h3⟩
        · exact ir c (tr _ _ _ h1 (tr _ _ _ hab h3))
      have ha0 : P.Lt a s ∨ P.Lt a c := by
        rcases hb0 with h3 | h3
        · exact Or.inl (tr _ _ _ hab h3)
        · exact Or.inr (tr _ _ _ hab h3)
      have : f a = 0 := by simp [f, PPlan.Lt, hac, has, ham, ha0]
      omega
    · have : f b = 4 := by simp [f, PPlan.Lt, hbc, hbs, hbm, hb0]
      have := hle4 a
      omega
  obtain ⟨L, hL, hs⟩ := exists_completion_rank P f hf
  obtain ⟨l₁, l₂, hL12⟩ := hL.split s
  have hfs : f s = 3 := by simp [f, PPlan.Lt, hcs.symm]
  have hfc : f c = 1 := by simp [f, PPlan.Lt]
  have huniq : ∀ x, f x = f s → x = s := by
    intro x hx
    rw [hfs] at hx
    simp only [f, PPlan.Lt] at hx
    split at hx
    · omega
    · split at hx
      · assumption
      · split at hx <;> (try split at hx) <;> omega
  have hmem := fun x => hL.mem_prefix_iff_rank hs hL12 huniq x
  have hc1 : c ∈ l₁ := (hmem c).2 (by omega)
  rcases (mem_run_iff P.step P.init p l₁).1 (h L hL l₁ l₂ hL12) with ⟨-, hn⟩ | ⟨a, i, b, hab, ha, hn⟩
  · exact hn c hc1 hcd
  · have hi1 : i ∈ l₁ := by simp [hab]
    have hfi : f i < 3 := by have := (hmem i).1 hi1; omega
    by_cases hic : i = c
    · subst hic; exact hwf p ha hcd
    by_cases him : P.Lt c i ∧ P.Lt i s
    · exact hnowk ⟨i, him.1, him.2, ha⟩
    have his : i ≠ s := fun e => by rw [e] at hfi; omega
    have hfi04 : f i = 0 ∨ f i = 4 := by
      simp only [f, hic, his, him, ite_false]; split <;> simp
    have hfi0 : f i ≤ 0 := by omega
    -- `c` comes after `i` in the completion, so it is in `b` and denies `p`
    have hcb : c ∈ b := by
      have hc1' := hc1
      rw [hab] at hc1'
      rcases List.mem_append.1 hc1' with hca | hcb
      · have hpf := (List.pairwise_append.1 (hL12 ▸ hs)).1
        rw [hab] at hpf
        have := (List.pairwise_append.1 hpf).2.2 c hca i (by simp)
        omega
      · rcases List.mem_cons.1 hcb with e | hcb
        · exact absurd e.symm hic
        · exact hcb
    exact hn c hcb hcd

/-- **The modal truth criterion, ground** (Chapman p. 9, proof pp. 41–43): with well-formed
steps, `p` is necessarily true in the input situation of `s` iff it has an establisher and no
clobberer. Postulates P1, P3, P4; the ground restriction is SIMPLIFIED (no codesignation). -/
theorem mtc_iff (hwf : ∀ i, (P.step i).WF) (s : Fin n) (p : Lit α) :
    NecTrue P s p ↔ MTC P s p := by
  constructor
  · intro h
    refine ⟨Classical.byContradiction fun hE => not_necTrue_of_not_establisher P hE h, ?_⟩
    intro c hc
    exact not_necTrue_of_clobberer P hc (hwf c) h
  · exact necTrue_of_mtc P

/-- Necessary truth is decidable in polynomial time: it is the criterion (p. 9, "It runs in
time polynomial in the number of steps"). The polynomial bound itself is not formalized. -/
def decNecTrue (hwf : ∀ i, (P.step i).WF) (s : Fin n) (p : Lit α) : Decidable (NecTrue P s p) :=
  decidable_of_iff _ (mtc_iff P hwf s p).symm

/-- **The criterion "with all the modalities switched"** (p. 9), ground: an establisher
possibly before `s` that possibly asserts `p`, and for every step necessarily before `s` that
denies `p`, a step possibly between it and `s` that asserts `p`. -/
def SwitchedMTC (s : Fin n) (p : Lit α) : Prop :=
  (p ∈ P.init ∨ ∃ t, t ≠ s ∧ ¬ P.Lt s t ∧ (P.step t).Asserts p) ∧
    ∀ c, P.Lt c s → (P.step c).Denies p →
      ∃ w, w ≠ c ∧ w ≠ s ∧ ¬ P.Lt w c ∧ ¬ P.Lt s w ∧ (P.step w).Asserts p

instance (s : Fin n) (p : Lit α) : Decidable (SwitchedMTC P s p) := by
  unfold SwitchedMTC; infer_instance

/-- **The switched criterion is necessary for possible truth.** Postulates P3, P4.
Its converse fails (`Examples.switched_not_sufficient`). -/
theorem switched_of_possTrue (hwf : ∀ i, (P.step i).WF) {s : Fin n} {p : Lit α}
    (h : PossTrue P s p) : SwitchedMTC P s p := by
  obtain ⟨L, l₁, l₂, hL, hL12, hp⟩ := h
  have hpw := hL.prefix_pairwise hL12
  rcases (mem_run_iff P.step P.init p l₁).1 hp with ⟨h0, hn⟩ | ⟨a, i, b, hab, ha, hn⟩
  · refine ⟨Or.inl h0, fun c hcs hcd => ?_⟩
    exact absurd hcd (hn c (hL.mem_prefix_of_lt hL12 hcs))
  · have hi : i ∈ l₁ := by simp [hab]
    have his : i ≠ s := fun e => hL.not_mem_prefix hL12 (e ▸ hi)
    refine ⟨Or.inr ⟨i, his, hL.not_lt_of_mem_prefix hL12 hi, ha⟩, fun c hcs hcd => ?_⟩
    have hc := hL.mem_prefix_of_lt hL12 hcs
    rw [hab] at hc hpw
    rcases List.mem_append.1 hc with hca | hcb
    · refine ⟨i, ?_, his, (List.pairwise_append.1 hpw).2.2 c hca i (by simp), ?_, ha⟩
      · rintro rfl; exact hwf _ p ha hcd
      · exact hL.not_lt_of_mem_prefix hL12 hi
    · rcases List.mem_cons.1 hcb with rfl | hcb
      · exact absurd hcd (hwf _ p ha)
      · exact absurd hcd (hn c hcb)

end Tweak.Ground
