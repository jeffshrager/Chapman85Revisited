import Tweak.Ground.Problem

/-!
# The intractability theorem: conditional actions

Chapman (1985), §3.2.1 p. 23; proof in §A.5, pp. 45–46.

> **Intractability theorem**: The problem of determining whether a proposition is necessarily
> true in a nonlinear plan whose action representation is sufficiently strong to represent
> conditional actions, dependency of effects on input situations, or derived side effects is
> NP-hard. (p. 23)

The proof (credited to Stan Rosenschein) reduces the validity of a propositional formula in
disjunctive normal form to necessary truth in a plan with *conditional steps*: "A conditional
step is always applicable, but has two sets of postconditions, the if-true and the if-false
postconditions. The if-true postconditions hold in the output situation if all the
preconditions were satisfied in the input situation; otherwise the if-false postconditions
hold." (p. 45)

The construction, for a DNF formula over atoms `p₁ … p_m` with clauses `1 … k`:
* each `pᵢ` is a proposition, false initially; a step `Sᵢ` makes it true;
* a conditional step `Cⱼ` per clause, whose preconditions are the clause's literals, asserts
  `satisfied` if they hold;
* a flag `checking`, false initially, made true by `K` and false by `U`, with `K` before every
  `Cⱼ` and every `Cⱼ` before `U`; the `Sᵢ` are conditional on `checking`, asserting
  `satisfied` if it holds;
* `satisfied` is false initially; the question is whether it is necessarily true in the final
  situation.

`reduction_correct` proves: `satisfied` is necessarily true at the end iff the formula is
valid. That is the correctness of the reduction; its polynomial size is evident from the
construction (`m + k + 3` steps) and is not formalized.

**Reinterpretation.** Validity of DNF formulas is coNP-complete, so the reduction is a
many-one reduction from a coNP-complete problem: necessary truth with conditional actions is
*coNP-hard*. "NP-hard", the paper's word, holds under polynomial-time Turing reductions; under
many-one reductions it is the complement, whether `satisfied` is possibly false, that is
NP-hard (not formalized).

Effects that depend on the input situation are modeled directly (`eff : σ → situation →
postconditions`); a conditional step is one such effect. SIMPLIFIED: derived side effects
(deductive closure) are not modeled.
-/

set_option linter.unusedSectionVars false

namespace Tweak.Extended

open Tweak.Ground

variable {α : Type} [DecidableEq α] {ι : Type}

/-- **Execution with situation-dependent effects**: each step's postconditions are computed
from its input situation; the frame rule of P3 is unchanged. -/
def xrun (eff : ι → List (Lit α) → List (Lit α)) (init : List (Lit α)) (l : List ι) :
    List (Lit α) :=
  l.foldl (fun s i => apply s ⟨[], eff i s⟩) init

variable (eff : ι → List (Lit α) → List (Lit α)) (init : List (Lit α))

@[simp] theorem xrun_nil : xrun eff init [] = init := rfl

theorem xrun_append (l₁ l₂ : List ι) :
    xrun eff init (l₁ ++ l₂) = xrun eff (xrun eff init l₁) l₂ := by
  simp [xrun, List.foldl_append]

@[simp] theorem xrun_snoc (l : List ι) (x : ι) :
    xrun eff init (l ++ [x]) = apply (xrun eff init l) ⟨[], eff x (xrun eff init l)⟩ := by
  simp [xrun]

theorem split_snoc {l a b : List ι} {x i : ι} (h : l ++ [x] = a ++ i :: b) :
    (a = l ∧ i = x ∧ b = []) ∨ ∃ b', l = a ++ i :: b' ∧ b = b' ++ [x] := by
  rcases List.append_eq_append_iff.1 h.symm with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
  · cases c with
    | nil => simp at hc2; exact Or.inl ⟨by simpa using hc1.symm, hc2.1, hc2.2⟩
    | cons c0 cs =>
      simp at hc2
      obtain ⟨rfl, rfl⟩ := hc2
      exact Or.inr ⟨cs, hc1, rfl⟩
  · cases c with
    | nil => simp at hc2; exact Or.inl ⟨by simpa using hc1, hc2.1.symm, hc2.2⟩
    | cons c0 cs => simp at hc2

/-- **Where a true proposition came from** (the truth criterion for complete plans, p. 39,
with situation-dependent effects, in the direction the proofs use): either it was initially
true and never actually denied, or some step actually asserted it and no later step actually
denied it. -/
theorem xrun_source {p : Lit α} :
    ∀ l, p ∈ xrun eff init l →
      (p ∈ init ∧ ∀ a i b, l = a ++ i :: b → p.neg ∉ eff i (xrun eff init a)) ∨
      ∃ a i b, l = a ++ i :: b ∧ p ∈ eff i (xrun eff init a) ∧
        ∀ c j d, b = c ++ j :: d → p.neg ∉ eff j (xrun eff init (a ++ i :: c)) := by
  intro l
  induction l using snoc_induction with
  | nil =>
    intro h
    exact Or.inl ⟨h, fun a i b hab => by simp at hab⟩
  | snoc l x ih =>
    intro h
    rw [xrun_snoc, mem_apply] at h
    rcases h with hx | ⟨hl, hd⟩
    · exact Or.inr ⟨l, x, [], rfl, hx, fun c j d h => by simp at h⟩
    · have hd' : p.neg ∉ eff x (xrun eff init l) := hd
      rcases ih hl with ⟨h0, hn⟩ | ⟨a, i, b, hab, ha, hn⟩
      · refine Or.inl ⟨h0, fun a i b hab => ?_⟩
        rcases split_snoc hab with ⟨rfl, rfl, rfl⟩ | ⟨b', hl', -⟩
        · exact hd'
        · exact hn a i b' hl'
      · refine Or.inr ⟨a, i, b ++ [x], by simp [hab], ha, fun c j d hcd => ?_⟩
        rcases split_snoc hcd with ⟨rfl, rfl, rfl⟩ | ⟨d', hb', -⟩
        · rw [← hab]; exact hd'
        · exact hn c j d' hb'

/-- Truth persists while no step can deny it. -/
theorem xrun_keep {p : Lit α} {init' : List (Lit α)} (h : p ∈ init') :
    ∀ l : List ι, (∀ j ∈ l, ∀ st, p.neg ∉ eff j st) → p ∈ xrun eff init' l := by
  intro l
  induction l using snoc_induction with
  | nil => intro _; exact h
  | snoc l x ih =>
    intro hn
    rw [xrun_snoc, mem_apply]
    exact Or.inr ⟨ih (fun j hj => hn j (by simp [hj])), hn x (by simp) _⟩

/-- A step asserts a proposition; no later step can deny it; it holds afterwards. -/
theorem xrun_after {p : Lit α} {a b : List ι} {i : ι} (h : p ∈ eff i (xrun eff init a))
    (hn : ∀ j ∈ b, ∀ st, p.neg ∉ eff j st) : p ∈ xrun eff init (a ++ i :: b) := by
  have : a ++ i :: b = (a ++ [i]) ++ b := by simp
  rw [this, xrun_append]
  refine xrun_keep (eff := eff) ?_ b hn
  rw [xrun_snoc, mem_apply]
  exact Or.inl h

/-! ## Positions in a list -/

section Pos
variable {σ : Type} [DecidableEq σ]

/-- The position of `x` in a list (its length if absent). -/
def pos : List σ → σ → Nat
  | [], _ => 0
  | y :: l, x => if y = x then 0 else pos l x + 1

theorem pos_lt_of_mem {x : σ} : ∀ {a : List σ} (l : List σ), x ∈ a → pos (a ++ l) x < a.length
  | [], _, h => by simp at h
  | y :: a, l, h => by
    simp only [List.cons_append, pos, List.length_cons]
    split
    · omega
    · have : x ∈ a := by
        rcases List.mem_cons.1 h with rfl | h
        · contradiction
        · exact h
      have := pos_lt_of_mem l this
      omega

theorem pos_of_not_mem {x : σ} : ∀ {a : List σ} (l : List σ), x ∉ a →
    pos (a ++ l) x = a.length + pos l x
  | [], _, _ => by simp
  | y :: a, l, h => by
    simp only [List.cons_append, pos, List.length_cons]
    have hy : y ≠ x := fun e => h (by simp [e])
    simp only [hy, ↓reduceIte]
    rw [pos_of_not_mem l (fun hx => h (by simp [hx]))]
    omega

/-- Membership in the prefix before `y` is having a smaller position. -/
theorem mem_prefix_iff_pos {L a b : List σ} {y : σ} (hL : L = a ++ y :: b) (hy : y ∉ a)
    (x : σ) (hx : x ∈ L) : x ∈ a ↔ pos L x < pos L y := by
  subst hL
  rw [pos_of_not_mem _ hy]
  simp only [pos, ↓reduceIte]
  constructor
  · intro h; have := pos_lt_of_mem (y :: b) h; omega
  · intro h
    refine Classical.byContradiction fun hxa => ?_
    rw [pos_of_not_mem _ hxa] at h
    omega

end Pos

/-! ## The reduction -/

variable {m k : Nat}

/-- Propositions of the constructed plan: the formula's atoms, `satisfied`, `checking`. -/
inductive RA (m : Nat) | v (i : Fin m) | sat | chk
  deriving DecidableEq

/-- Steps of the constructed plan: `Sᵢ`, `K`, `Cⱼ`, `U`, and the final step `F`. -/
inductive RS (m k : Nat) | S (i : Fin m) | K | C (j : Fin k) | U | F
  deriving DecidableEq

theorem nodup_map {β γ : Type} {f : β → γ} (hf : ∀ a b, f a = f b → a = b) {l : List β}
    (h : l.Nodup) : (l.map f).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  exact h.imp fun hab e => hab (hf _ _ e)

instance : Enum (RS m k) where
  elems := (List.finRange m).map RS.S ++ RS.K :: ((List.finRange k).map RS.C ++ [RS.U, RS.F])
  nodup := by
    rw [List.nodup_append, List.nodup_cons, List.nodup_append]
    refine ⟨nodup_map (fun a b h => by cases h; rfl) (List.nodup_finRange m),
      ⟨by simp, nodup_map (fun a b h => by cases h; rfl) (List.nodup_finRange k), by simp,
        by simp⟩, ?_⟩
    intro a ha b hb
    simp at ha hb
    obtain ⟨i, rfl⟩ := ha
    rcases hb with rfl | ⟨j, rfl⟩ | rfl | rfl <;> simp
  complete := by intro x; cases x <;> simp

/-- The time order: `K < Cⱼ < U`, `K < U`, everything before `F`; the `Sᵢ` otherwise free. -/
def rbefore : RS m k → RS m k → Bool
  | .K, .C _ => true
  | .C _, .U => true
  | .K, .U => true
  | .F, _ => false
  | _, .F => true
  | _, _ => false

/-- The order of the constructed plan, as a `PPlan` (its steps are unused). -/
def rorder : PPlan (RA m) (RS m k) where
  init := []
  step := fun _ => ⟨[], []⟩
  before := rbefore
  irrefl := by intro a; cases a <;> rfl
  trans := by intro a b c; cases a <;> cases b <;> cases c <;> simp [rbefore]

/-- A literal of the formula: an atom and its required sign. -/
abbrev lv (q : Fin m × Bool) : Lit (RA m) := ⟨.v q.1, q.2⟩

/-- **The steps' effects** (p. 45–46): `Sᵢ` makes `pᵢ` true, and `satisfied` too if `checking`
holds; `K` and `U` set and clear `checking`; `Cⱼ` asserts `satisfied` if its clause holds. -/
def reff (cl : Fin k → List (Fin m × Bool)) : RS m k → List (Lit (RA m)) → List (Lit (RA m))
  | .S i, st => if (⟨.chk, true⟩ : Lit (RA m)) ∈ st then [⟨.v i, true⟩, ⟨.sat, true⟩]
      else [⟨.v i, true⟩]
  | .K, _ => [⟨.chk, true⟩]
  | .U, _ => [⟨.chk, false⟩]
  | .C j, st => if ∀ q ∈ cl j, lv q ∈ st then [⟨.sat, true⟩] else []
  | .F, _ => []

/-- The initial situation: every atom, `satisfied` and `checking` false. -/
def rinit (m : Nat) : List (Lit (RA m)) :=
  ⟨.sat, false⟩ :: ⟨.chk, false⟩ :: (List.finRange m).map (fun i => ⟨.v i, false⟩)

/-- **Validity** of a DNF formula: every truth assignment satisfies some clause. -/
def Valid (cl : Fin k → List (Fin m × Bool)) : Prop :=
  ∀ T : Fin m → Bool, ∃ j, ∀ q ∈ cl j, T q.1 = q.2

/-- `satisfied` is necessarily true in the final situation. -/
def SatNec (cl : Fin k → List (Fin m × Bool)) : Prop :=
  ∀ L, Completion (rorder (m := m) (k := k)) L → ∀ l₁ l₂, L = l₁ ++ RS.F :: l₂ →
    (⟨.sat, true⟩ : Lit (RA m)) ∈ xrun (reff cl) (rinit m) l₁

variable (cl : Fin k → List (Fin m × Bool))

theorem sat_never_denied : ∀ (j : RS m k) st,
    (⟨.sat, true⟩ : Lit (RA m)).neg ∉ reff cl j st := by
  intro j st; cases j <;> simp [reff, Lit.neg] <;> split <;> simp

theorem vtrue_never_denied (i : Fin m) : ∀ (j : RS m k) st,
    (⟨.v i, true⟩ : Lit (RA m)).neg ∉ reff cl j st := by
  intro j st; cases j <;> simp [reff, Lit.neg] <;> split <;> simp

theorem chk_denied_only_by_U : ∀ (j : RS m k) st, j ≠ .U →
    (⟨.chk, true⟩ : Lit (RA m)).neg ∉ reff cl j st := by
  intro j st hj; cases j <;> simp [reff, Lit.neg] at hj ⊢ <;> split <;> simp

theorem vfalse_denied_only_by_S (i : Fin m) : ∀ (j : RS m k) st, j ≠ .S i →
    (⟨.v i, false⟩ : Lit (RA m)).neg ∉ reff cl j st := by
  intro j st hj
  cases j with
  | S i' => simp [reff, Lit.neg] at hj ⊢ <;> split <;> simp [Ne.symm hj]
  | C j => simp [reff, Lit.neg] <;> split <;> simp
  | _ => simp [reff, Lit.neg]

/-- In a completion, a step necessarily before another has a smaller position. -/
theorem pos_lt_of_before {L : List (RS m k)} (hL : Completion (rorder (m := m) (k := k)) L)
    {x y : RS m k} (h : rbefore x y = true) : pos L x < pos L y := by
  obtain ⟨a, b, hab⟩ := hL.split y
  exact (mem_prefix_iff_pos hab (hL.not_mem_prefix hab) x (hL.complete x)).1
    (hL.mem_prefix_of_lt hab h)

/-- **Validity implies necessary truth** (p. 46): in any completion, either some `Sᵢ` falls
between `K` and `U` and asserts `satisfied`, or the clauses are all checked against the one
assignment made before `K`, and validity gives a clause that holds. -/
theorem satNec_of_valid (hv : Valid cl) : SatNec cl := by
  intro L hL l₁ l₂ hL12
  have hFl : RS.F ∉ l₁ := hL.not_mem_prefix hL12
  -- every step but `F` is before it
  have hin : ∀ x, x ≠ RS.F → x ∈ l₁ := fun x hx =>
    hL.mem_prefix_of_lt hL12 (by cases x <;> simp_all [PPlan.Lt, rorder, rbefore])
  -- positions relative to a split of the prefix
  have hsplit : ∀ x, x ≠ RS.F → ∃ a b, l₁ = a ++ x :: b ∧
      ∀ y, (y ∈ a ↔ pos L y < pos L x) := by
    intro x hx
    obtain ⟨a, b, hab⟩ := List.append_of_mem (hin x hx)
    have hL' : L = a ++ x :: (b ++ RS.F :: l₂) := by simp [hL12, hab]
    have hxa : x ∉ a := hL.not_mem_prefix hL'
    exact ⟨a, b, hab, fun y => mem_prefix_iff_pos hL' hxa y (hL.complete y)⟩
  have hKU : pos L .K < pos L .U := pos_lt_of_before hL rfl
  by_cases hmid : ∃ i, pos L .K < pos L (RS.S i) ∧ pos L (RS.S i) < pos L .U
  · -- some `Sᵢ` sees `checking` and asserts `satisfied`
    obtain ⟨i, hKi, hiU⟩ := hmid
    obtain ⟨a, b, hab, hpos⟩ := hsplit (.S i) (by simp)
    have hKa : RS.K ∈ a := (hpos _).2 hKi
    have hUa : RS.U ∉ a := fun h => by have := (hpos _).1 h; omega
    obtain ⟨a1, a2, ha⟩ := List.append_of_mem hKa
    have hchk : (⟨.chk, true⟩ : Lit (RA m)) ∈ xrun (reff cl) (rinit m) a := by
      rw [ha]
      exact xrun_after _ _ (by simp [reff])
        (fun j hj st => chk_denied_only_by_U cl j st (fun e => hUa (by simp [ha, ← e, hj])))
    rw [hab]
    exact xrun_after _ _ (by simp [reff, hchk]) (fun j _ st => sat_never_denied cl j st)
  · -- every `Sᵢ` is before `K` or after `U`: the assignment is fixed before `K`
    have hside : ∀ i, pos L (RS.S i) < pos L .K ∨ pos L .U < pos L (RS.S i) := by
      intro i
      have hne1 : pos L (RS.S i) ≠ pos L .K := by
        obtain ⟨a, b, hab⟩ := hL.split RS.K
        intro e
        have h1 := mem_prefix_iff_pos hab (hL.not_mem_prefix hab) (.S i) (hL.complete _)
        have h2 : RS.S i ∉ a := fun h => by have := h1.1 h; omega
        have : RS.S i ∈ RS.K :: b := by
          have := hL.complete (.S i); rw [hab] at this
          rcases List.mem_append.1 this with h | h
          · exact absurd h h2
          · exact h
        rcases List.mem_cons.1 this with h | h
        · cases h
        · rw [hab, pos_of_not_mem _ (fun h' => h2 h'), pos_of_not_mem _ (hL.not_mem_prefix hab)]
            at e
          simp [pos] at e
      have hne2 : pos L (RS.S i) ≠ pos L .U := by
        obtain ⟨a, b, hab⟩ := hL.split RS.U
        intro e
        have h1 := mem_prefix_iff_pos hab (hL.not_mem_prefix hab) (.S i) (hL.complete _)
        have h2 : RS.S i ∉ a := fun h => by have := h1.1 h; omega
        have : RS.S i ∈ RS.U :: b := by
          have := hL.complete (.S i); rw [hab] at this
          rcases List.mem_append.1 this with h | h
          · exact absurd h h2
          · exact h
        rcases List.mem_cons.1 this with h | h
        · cases h
        · rw [hab, pos_of_not_mem _ (fun h' => h2 h'), pos_of_not_mem _ (hL.not_mem_prefix hab)]
            at e
          simp [pos] at e
      have := hmid
      by_cases h : pos L (RS.S i) < pos L .K
      · exact Or.inl h
      · right
        refine Classical.byContradiction fun h' => this ⟨i, by omega, by omega⟩
    let T : Fin m → Bool := fun i => decide (pos L (RS.S i) < pos L .K)
    obtain ⟨j, hj⟩ := hv T
    obtain ⟨a, b, hab, hpos⟩ := hsplit (.C j) (by simp)
    have hKC : pos L .K < pos L (RS.C j) := pos_lt_of_before hL rfl
    have hCU : pos L (RS.C j) < pos L .U := pos_lt_of_before hL rfl
    have hcond : ∀ q ∈ cl j, lv q ∈ xrun (reff cl) (rinit m) a := by
      intro q hq
      have hTq := hj q hq
      obtain ⟨i, bq⟩ := q
      cases bq with
      | true =>
        have hi : pos L (RS.S i) < pos L .K := by simpa [T] using hTq
        obtain ⟨a1, a2, ha⟩ := List.append_of_mem ((hpos (.S i)).2 (by omega))
        rw [ha]
        exact xrun_after _ _ (by simp [reff]; split <;> simp)
          (fun j' _ st => vtrue_never_denied cl i j' st)
      | false =>
        have hi : pos L .U < pos L (RS.S i) := by
          rcases hside i with h | h
          · simp [T, h] at hTq
          · exact h
        have hSa : RS.S i ∉ a := fun h => by have := (hpos _).1 h; omega
        exact xrun_keep (eff := reff cl) (by simp [rinit])
          a (fun j' hj' st => vfalse_denied_only_by_S cl i j' st (fun e => hSa (e ▸ hj')))
    have hC : reff cl (.C j) (xrun (reff cl) (rinit m) a) = [⟨.sat, true⟩] := by
      simp only [reff]; split
      · rfl
      · contradiction
    rw [hab]
    exact xrun_after _ _ (by rw [hC]; simp) (fun j' _ st => sat_never_denied cl j' st)

/-- **Necessary truth implies validity** (p. 46: "every truth assignment is generated by some
completion of the plan"): for an assignment `T`, the completion with the true `Sᵢ` before `K`
and the false ones after `U` has `satisfied` at the end only if some clause holds under `T`. -/
theorem valid_of_satNec (h : SatNec cl) : Valid cl := by
  intro T
  let r : RS m k → Nat := fun x => match x with
    | .S i => if T i then 0 else 4 | .K => 1 | .C _ => 2 | .U => 3 | .F => 5
  have hr : ∀ a b, (rorder (m := m) (k := k)).Lt a b → r a ≤ r b := by
    intro a b hab
    cases a <;> cases b <;> simp_all [PPlan.Lt, rorder, rbefore, r] <;> split <;> omega
  obtain ⟨L, hL, hs⟩ := exists_completion_rank rorder r hr
  obtain ⟨l₁, l₂, hL12⟩ := hL.split RS.F
  have hsat := h L hL l₁ l₂ hL12
  -- ranks along a split of the prefix
  have hrank : ∀ a x b, l₁ = a ++ x :: b → (∀ y ∈ a, r y ≤ r x) ∧
      (∀ y, y ∉ a → y ≠ x → r x ≤ r y) := by
    intro a x b hab
    have hL' : L = a ++ x :: (b ++ RS.F :: l₂) := by simp [hL12, hab]
    have hp := List.pairwise_append.1 (hL' ▸ hs)
    refine ⟨fun y hy => hp.2.2 y hy x (by simp), fun y hya hyx => ?_⟩
    have hy := hL.complete y
    rw [hL'] at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact absurd hy hya
    · rcases List.mem_cons.1 hy with hy | hy
      · exact absurd hy hyx
      · exact (List.pairwise_cons.1 hp.2.1).1 y hy
  rcases xrun_source _ _ l₁ hsat with ⟨h0, -⟩ | ⟨a, x, b, hab, hx, hn⟩
  · simp [rinit] at h0
  · obtain ⟨hbefore, hafter⟩ := hrank a x b hab
    cases x with
    | K => simp [reff] at hx
    | U => simp [reff] at hx
    | F => simp [reff] at hx
    | S i =>
      -- `Sᵢ` asserted `satisfied`, so it saw `checking`
      have hchk : (⟨.chk, true⟩ : Lit (RA m)) ∈ xrun (reff cl) (rinit m) a := by
        simp only [reff] at hx; split at hx
        · assumption
        · simp at hx
      exfalso
      rcases xrun_source _ _ a hchk with ⟨h0, -⟩ | ⟨a1, y, a2, ha, hy, hn'⟩
      · simp [rinit] at h0
      · cases y with
        | K =>
          -- `K` is before `Sᵢ`, so `Sᵢ` has rank 4, and so does not precede `U`
          have hK : r RS.K ≤ r (RS.S i) := hbefore RS.K (by simp [ha])
          have hTi : T i = false := by
            cases hT : T i
            · rfl
            · simp [r, hT] at hK
          have hUa : RS.U ∈ a := by
            refine Classical.byContradiction fun hU => ?_
            have := hafter RS.U hU (by simp)
            simp [r, hTi] at this
          rw [ha] at hUa
          rcases List.mem_append.1 hUa with hU1 | hU2
          · -- `U` before `K`: impossible by rank
            have hpa : a = a1 ++ RS.K :: a2 := ha
            have h1 := (hrank a1 RS.K (a2 ++ RS.S i :: b) (by simp [hab, hpa])).1 RS.U hU1
            simp [r] at h1
          · rcases List.mem_cons.1 hU2 with hU | hU
            · cases hU
            · obtain ⟨c, d, hcd⟩ := List.append_of_mem hU
              exact hn' c RS.U d hcd (by simp [reff, Lit.neg])
        | _ => simp [reff] at hy <;> (try split at hy) <;> simp at hy
    | C j =>
      refine ⟨j, fun q hq => ?_⟩
      have hcond : ∀ q ∈ cl j, lv q ∈ xrun (reff cl) (rinit m) a := by
        simp only [reff] at hx; split at hx
        · assumption
        · simp at hx
      have hqa := hcond q hq
      obtain ⟨i, bq⟩ := q
      cases bq with
      | true =>
        -- `pᵢ` true: `Sᵢ` came before `Cⱼ`, so it has rank 0
        rcases xrun_source _ _ a hqa with ⟨h0, -⟩ | ⟨a1, y, a2, ha, hy, -⟩
        · simp [rinit] at h0
        · cases y with
          | S i' =>
            have hi' : i' = i := by
              simp only [reff] at hy; split at hy <;> simp at hy <;> exact hy.symm
            subst hi'
            have := hbefore (.S i') (by simp [ha])
            simp only [r] at this
            cases hT : T i' <;> simp_all
          | C _ => simp [reff] at hy <;> split at hy <;> simp at hy
          | _ => simp [reff] at hy
      | false =>
        -- `pᵢ` false: `Sᵢ` did not come before `Cⱼ`, so it has rank 4
        rcases xrun_source _ _ a hqa with ⟨-, hn0⟩ | ⟨a1, y, a2, ha, hy, -⟩
        · have hSa : RS.S i ∉ a := by
            intro hSa
            obtain ⟨c, d, hcd⟩ := List.append_of_mem hSa
            exact hn0 c (.S i) d hcd (by simp [reff, Lit.neg]; split <;> simp)
          have := hafter (.S i) hSa (by simp)
          simp only [r] at this
          cases hT : T i <;> simp_all
        · cases y with
          | S _ => simp [reff] at hy; split at hy <;> simp at hy
          | C _ => simp [reff] at hy <;> split at hy <;> simp at hy
          | _ => simp [reff] at hy

/-- **The intractability reduction is correct** (p. 45–46): `satisfied` is necessarily true
in the final situation of the constructed plan iff the DNF formula is valid. With the
construction's polynomial size, this makes necessary truth with conditional actions coNP-hard
(see the module docstring for "NP-hard"). -/
theorem reduction_correct : SatNec cl ↔ Valid cl :=
  ⟨valid_of_satNec cl, satNec_of_valid cl⟩

end Tweak.Extended
