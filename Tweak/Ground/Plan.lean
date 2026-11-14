import Tweak.Ground.Basic

/-!
# Ground TWEAK: incomplete plans and their completions

Chapman (1985), §2.1, pp. 5–6, and the lemmas of §A.1, p. 40.

An incomplete plan's time order is "simply a partial order on steps" (p. 5); a *completion* is
"any total order O on the same set of steps such that sCt implies sOt" (p. 5). Something is
*necessarily* so if it holds in every completion and *possibly* so if in some (p. 5).

Here the partial order is given already closed (a strict partial order `before`); TWEAK's
constraint maintenance, which closes a set of posted constraints, is not modeled. The
situations of a plan are named by steps: "the input situation of `s`" is the situation just
before `s`. SIMPLIFIED: the final situation is the input situation of a step after every other
step (a "finish" step with no postconditions); the initial situation is the plan's `init`.

Results:
* `exists_completion_rank`: given any ranking of steps monotone in the time order, some
  completion lists the steps in order of rank. From it come Chapman's *completion lemma*
  (`exists_completion`, p. 40) and his *temporal consistency lemma* (p. 40) in the form the
  proofs use, and the syntactic reading of "necessarily before" (`necBefore_iff`).
-/

set_option linter.unusedSectionVars false

namespace Tweak.Ground

variable {α : Type} [DecidableEq α]

/-- **A finite type of step names**, listed without repetition. -/
class Enum (σ : Type) where
  elems : List σ
  nodup : elems.Nodup
  complete : ∀ x, x ∈ elems

instance (n : Nat) : Enum (Fin n) := ⟨List.finRange n, List.nodup_finRange n, List.mem_finRange⟩

instance Enum.decForall {σ : Type} [Enum σ] (P : σ → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (∀ x ∈ Enum.elems, P x) ⟨fun h x => h x (Enum.complete x), fun h x _ => h x⟩

instance Enum.decExists {σ : Type} [Enum σ] (P : σ → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (∃ x ∈ Enum.elems, P x)
    ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, Enum.complete x, h⟩⟩

/-- **An incomplete ground plan** with steps named by `σ` (postulate P4, p. 5): an initial situation, a
table of steps, and a strict partial order on them. -/
structure PPlan (α : Type) (σ : Type) where
  init : List (Lit α)
  step : σ → Step α
  before : σ → σ → Bool
  irrefl : ∀ a, before a a = false
  trans : ∀ a b c, before a b = true → before b c = true → before a c = true

variable {σ : Type} [DecidableEq σ] [Enum σ] (P : PPlan α σ)

/-- `a` is necessarily before `b` in the time order. -/
abbrev PPlan.Lt (a b : σ) : Prop := P.before a b = true

/-- **A completion** (p. 5): a total order on all the steps extending the partial order, as a
list. -/
structure Completion (L : List (σ)) : Prop where
  nodup : L.Nodup
  complete : ∀ a, a ∈ L
  respects : L.Pairwise (fun x y => ¬ P.Lt y x)

/-- **Necessary truth** (p. 5): `p` holds in the input situation of `s` in every completion. -/
def NecTrue (s : σ) (p : Lit α) : Prop :=
  ∀ L, Completion P L → ∀ l₁ l₂, L = l₁ ++ s :: l₂ → p ∈ run P.step P.init l₁

/-- **Possible truth** (p. 5): `p` holds in the input situation of `s` in some completion. -/
def PossTrue (s : σ) (p : Lit α) : Prop :=
  ∃ L l₁ l₂, Completion P L ∧ L = l₁ ++ s :: l₂ ∧ p ∈ run P.step P.init l₁

section Sorting

variable {β : Type} [DecidableEq β] (R : β → β → Prop)

/-- Every nonempty finite set under a strict partial order has a minimal element. -/
theorem exists_minimal (irr : ∀ a, ¬ R a a) (tr : ∀ a b c, R a b → R b c → R a c) :
    ∀ xs : List β, xs ≠ [] → ∃ m ∈ xs, ∀ y ∈ xs, ¬ R y m := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _
    by_cases hr : rest = []
    · subst hr
      exact ⟨a, by simp, fun y hy => by simp at hy; subst hy; exact irr _⟩
    obtain ⟨m, hm, hmin⟩ := ih hr
    by_cases ham : R a m
    · refine ⟨a, by simp, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact irr _
      · exact fun hya => hmin y hy (tr _ _ _ hya ham)
    · refine ⟨m, by simp [hm], fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ham
      · exact hmin y hy

/-- **Topological sorting**: every finite set under a strict partial order can be listed so
that no element precedes one below it. -/
theorem exists_sorted (irr : ∀ a, ¬ R a a) (tr : ∀ a b c, R a b → R b c → R a c) :
    ∀ (k : Nat) (xs : List β), xs.length = k →
      ∃ ys : List β, ys.Perm xs ∧ ys.Pairwise (fun x y => ¬ R y x) := by
  intro k
  induction k with
  | zero =>
    intro xs h
    exact ⟨[], by simp_all, List.Pairwise.nil⟩
  | succ k ih =>
    intro xs h
    have hne : xs ≠ [] := by intro h'; simp [h'] at h
    obtain ⟨m, hm, hmin⟩ := exists_minimal R irr tr xs hne
    obtain ⟨ys, hp, hs⟩ := ih (xs.erase m) (by rw [List.length_erase_of_mem hm]; omega)
    refine ⟨m :: ys, ((List.perm_cons_erase hm).trans (List.Perm.cons m hp.symm)).symm, ?_⟩
    refine List.pairwise_cons.2 ⟨fun y hy => ?_, hs⟩
    exact hmin y (List.mem_of_mem_erase (hp.mem_iff.1 hy))

end Sorting

/-- **Ranked completions**: for any ranking of the steps that never decreases along the time
order, some completion lists the steps in order of rank. Each construction in Chapman's proof
of the modal truth criterion ("put after s every step possibly after s", p. 42) is a choice of
ranking. -/
theorem exists_completion_rank (f : σ → Nat) (hf : ∀ a b, P.Lt a b → f a ≤ f b) :
    ∃ L, Completion P L ∧ L.Pairwise (fun x y => f x ≤ f y) := by
  let R : σ → σ → Prop := fun x y => f x < f y ∨ (f x = f y ∧ P.Lt x y)
  have irr : ∀ a, ¬ R a a := by
    intro a h
    rcases h with h | ⟨-, h⟩
    · omega
    · simp [PPlan.Lt, P.irrefl] at h
  have tr : ∀ a b c, R a b → R b c → R a c := by
    intro a b c h1 h2
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, P.trans _ _ _ h1 h2⟩
  obtain ⟨L, hp, hs⟩ := exists_sorted R irr tr _ (Enum.elems) rfl
  refine ⟨L, ⟨hp.nodup_iff.2 Enum.nodup, fun a => hp.mem_iff.2 (Enum.complete a),
    hs.imp ?_⟩, hs.imp ?_⟩
  · intro x y hxy hlt
    apply hxy
    have := hf _ _ hlt
    by_cases h : f y < f x
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hlt⟩
  · intro x y hxy
    by_cases h : f y < f x
    · exact absurd (Or.inl h) hxy
    · omega

/-- **Completion lemma** (p. 40, ground): every incomplete plan has a completion. -/
theorem exists_completion : ∃ L, Completion P L := by
  obtain ⟨L, h, -⟩ := exists_completion_rank P (fun _ => 0) (fun _ _ _ => Nat.le_refl _)
  exact ⟨L, h⟩

variable {P}

/-- Every step appears in a completion, so a completion splits around it. -/
theorem Completion.split {L : List (σ)} (h : Completion P L) (s : σ) :
    ∃ l₁ l₂, L = l₁ ++ s :: l₂ := List.append_of_mem (h.complete s)

theorem Completion.not_mem_prefix {L l₁ l₂ : List (σ)} {s : σ} (h : Completion P L)
    (hL : L = l₁ ++ s :: l₂) : s ∉ l₁ := by
  intro hs
  have := (List.nodup_append.1 (hL ▸ h.nodup)).2.2 s hs s (by simp)
  exact this rfl

theorem Completion.prefix_pairwise {L l₁ l₂ : List (σ)} {s : σ} (h : Completion P L)
    (hL : L = l₁ ++ s :: l₂) : l₁.Pairwise (fun x y => ¬ P.Lt y x) :=
  (List.pairwise_append.1 (hL ▸ h.respects)).1

/-- A step in the prefix before `s` is not necessarily after `s`. -/
theorem Completion.not_lt_of_mem_prefix {L l₁ l₂ : List (σ)} {s x : σ}
    (h : Completion P L) (hL : L = l₁ ++ s :: l₂) (hx : x ∈ l₁) : ¬ P.Lt s x :=
  (List.pairwise_append.1 (hL ▸ h.respects)).2.2 x hx s (by simp)

/-- A step necessarily before `s` lies in the prefix before `s`. -/
theorem Completion.mem_prefix_of_lt {L l₁ l₂ : List (σ)} {s x : σ}
    (h : Completion P L) (hL : L = l₁ ++ s :: l₂) (hx : P.Lt x s) : x ∈ l₁ := by
  have hxL := h.complete x
  rw [hL] at hxL
  rcases List.mem_append.1 hxL with hx1 | hx2
  · exact hx1
  · rcases List.mem_cons.1 hx2 with rfl | hx2
    · simp [PPlan.Lt, P.irrefl] at hx
    · have := (List.pairwise_cons.1 (List.pairwise_append.1 (hL ▸ h.respects)).2.1).1 x hx2
      exact absurd hx this

/-- In a completion sorted by a ranking in which `s` alone has its rank, the prefix before `s`
is exactly the steps of lower rank. -/
theorem Completion.mem_prefix_iff_rank {L l₁ l₂ : List (σ)} {s : σ} {f : σ → Nat}
    (h : Completion P L) (hf : L.Pairwise (fun x y => f x ≤ f y)) (hL : L = l₁ ++ s :: l₂)
    (huniq : ∀ x, f x = f s → x = s) (x : σ) : x ∈ l₁ ↔ f x < f s := by
  have hp := List.pairwise_append.1 (hL ▸ hf)
  constructor
  · intro hx
    have h1 := hp.2.2 x hx s (by simp)
    have h2 : x ≠ s := fun e => h.not_mem_prefix hL (e ▸ hx)
    have := mt (huniq x) h2
    omega
  · intro hx
    have hxL := h.complete x
    rw [hL] at hxL
    rcases List.mem_append.1 hxL with hx1 | hx2
    · exact hx1
    · rcases List.mem_cons.1 hx2 with rfl | hx2
      · omega
      · have := (List.pairwise_cons.1 hp.2.1).1 x hx2
        omega

/-- **"Necessarily before" is the time order** (p. 5): `a` precedes `b` in every completion
iff `a` is before `b` in the partial order. So Chapman's modalities on the time order are
decidable without enumerating completions. -/
theorem necBefore_iff (P : PPlan α σ) (a b : σ) (hab : a ≠ b) :
    (∀ L, Completion P L → ∀ l₁ l₂, L = l₁ ++ b :: l₂ → a ∈ l₁) ↔ P.Lt a b := by
  constructor
  · intro h
    refine Classical.byContradiction fun hlt => ?_
    -- rank: everything at or below `b` first, the rest after
    let f : σ → Nat := fun x => if P.Lt x b ∨ x = b then 0 else 1
    have hf : ∀ x y, P.Lt x y → f x ≤ f y := by
      intro x y hxy
      by_cases hy : P.Lt y b ∨ y = b
      · have : P.Lt x b := by
          rcases hy with hy | rfl
          · exact P.trans _ _ _ hxy hy
          · exact hxy
        have h1 : f x = 0 := by simp [f, this]
        omega
      · have h1 : f y = 1 := by simp only [f]; exact (ite_eq_right_iff.2 (fun h => absurd h hy))
        have h2 : f x ≤ 1 := by simp only [f]; split <;> omega
        omega
    obtain ⟨L, hL, hs⟩ := exists_completion_rank P f hf
    obtain ⟨l₁, l₂, hL12⟩ := hL.split b
    have ha := h L hL l₁ l₂ hL12
    have h1 := (List.pairwise_append.1 (hL12 ▸ hs)).2.2 a ha b (by simp)
    have hfa : f a = 1 := by simp [f, hlt, hab]
    have hfb : f b = 0 := by simp [f]
    omega
  · intro hlt L hL l₁ l₂ hL12
    exact hL.mem_prefix_of_lt hL12 hlt

end Tweak.Ground
