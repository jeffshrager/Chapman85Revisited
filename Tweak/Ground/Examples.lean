import Tweak.Ground.MTC

/-!
# Ground examples: white knights, the switched criterion, breakfast, the Sussman anomaly

Every necessary-truth fact below is computed by the modal truth criterion (`decide` on
`MTC`) and transferred by `mtc_iff`; nothing enumerates completions. The witnesses were found
and cross-checked by brute force over all completions in `tools/mtc_check.py`.

* `mtc_of_simple`, `wk_needed`: the "simple" criterion of p. 8 is sufficient but not
  necessary, and the white-knight clause is needed even without variables. Chapman motivates
  that clause only by codesignation (the "odd plan", p. 8); here two establishers each rescue
  the other's clobberer.
* `switched_not_sufficient`: the possible-truth criterion obtained by "switching all the
  modalities" (p. 9) is not sufficient: it holds, yet `p` is true in no completion.
* `breakfast_solves`: the incomplete plan of p. 7 necessarily achieves its goals.
* `sussman_clobbered`, `sussman_solves`: TWEAK's Sussman-anomaly trace (pp. 14–17).
-/

set_option linter.unusedSectionVars false

namespace Tweak.Ground

variable {α : Type} [DecidableEq α] {σ : Type} [DecidableEq σ] [Enum σ]

/-- **The simple criterion** (p. 8): an establisher, initial or a step necessarily before `s`,
with no step possibly between it and `s` that denies `p`. -/
def Simple (P : PPlan α σ) (s : σ) (p : Lit α) : Prop :=
  (p ∈ P.init ∧ ∀ c, c ≠ s → ¬ P.Lt s c → ¬ (P.step c).Denies p) ∨
  ∃ t, P.Lt t s ∧ (P.step t).Asserts p ∧
    ∀ c, c ≠ s → ¬ P.Lt s c → c ≠ t → ¬ P.Lt c t → ¬ (P.step c).Denies p

instance (P : PPlan α σ) (s : σ) (p : Lit α) : Decidable (Simple P s p) := by
  unfold Simple; infer_instance

/-- **The simple criterion is sufficient** (p. 8: "a proposition p is necessarily true in a
situation if there is some previous situation in which it is necessarily true, and no possibly
intervening step possibly denies it"): it implies the modal truth criterion. -/
theorem mtc_of_simple (P : PPlan α σ) (hwf : ∀ i, (P.step i).WF) (s : σ) (p : Lit α)
    (h : Simple P s p) : MTC P s p := by
  rcases h with ⟨h0, hn⟩ | ⟨t, hts, ht, hn⟩
  · exact ⟨Or.inl h0, fun c ⟨hcs, hsc, hcd, _⟩ => hn c hcs hsc hcd⟩
  · refine ⟨Or.inr ⟨t, hts, ht⟩, fun c ⟨hcs, hsc, hcd, hno⟩ => ?_⟩
    by_cases hct : c = t
    · subst hct; exact hwf c p ht hcd
    · by_cases hlt : P.Lt c t
      · exact hno ⟨t, hlt, hts, ht⟩
      · exact hn c hcs hsc hct hlt hcd

/-- A step table and an order from lists, for the examples. -/
def mkOrder {m : Nat} (l : List (Nat × Nat)) : Fin m → Fin m → Bool :=
  fun a b => decide ((a.val, b.val) ∈ l)

namespace Examples

/-- The proposition `p` of the abstract examples. -/
def p : Lit Unit := ⟨(), true⟩

/-- Steps 0 and 1 assert `p`; 2 and 3 deny it; 4 is the step whose input situation we ask
about. -/
def abstractSteps : Fin 5 → Step Unit := fun i =>
  if i.val < 2 then ⟨[], [p]⟩ else if i.val < 4 then ⟨[], [p.neg]⟩ else ⟨[], []⟩

/-- **Two crossed white knights.** `C₂ < A₀`, `D₃ < B₁`, all before `S₄`. Whichever of the
four steps comes last before `S`, it asserts `p`. -/
def wkPlan : PPlan Unit (Fin 5) where
  init := []
  step := abstractSteps
  before := mkOrder [(2, 0), (3, 1), (0, 4), (1, 4), (2, 4), (3, 4)]
  irrefl := by decide
  trans := by decide

theorem abstract_wf : ∀ i, (abstractSteps i).WF := fun i =>
  Step.wf_of_check _ (by revert i; decide)

/-- **The white-knight clause is needed without variables**: `p` is necessarily true at `S`
(by the criterion, each denier is rescued by the asserter ordered after it), but no establisher
is free of possibly-intervening deniers, so the simple criterion fails. -/
theorem wk_needed : NecTrue wkPlan 4 p ∧ ¬ Simple wkPlan 4 p :=
  ⟨(mtc_iff wkPlan abstract_wf 4 p).2 (by decide), by decide⟩

/-- **The switched criterion's counterexample.** `A₀ < D₃`, `B₁ < C₂`, all before `S₄`:
each denier has an asserter possibly after it, but every completion ends with a denier. -/
def switchPlan : PPlan Unit (Fin 5) where
  init := []
  step := abstractSteps
  before := mkOrder [(0, 3), (1, 2), (0, 4), (1, 4), (2, 4), (3, 4)]
  irrefl := by decide
  trans := by decide

/-- **"Switching the modalities" does not give a criterion for possible truth** (p. 9 claims
it does): the switched criterion holds, yet `p` is true at `S` in no completion. It is a
necessary condition only (`switched_of_possTrue`). -/
theorem switched_not_sufficient : SwitchedMTC switchPlan 4 p ∧ ¬ PossTrue switchPlan 4 p := by
  refine ⟨by decide, ?_⟩
  rintro ⟨L, l₁, l₂, hL, hL12, hp⟩
  -- `¬p` is necessarily true there, and situations stay consistent
  have hneg : NecTrue switchPlan 4 p.neg := (mtc_iff switchPlan abstract_wf 4 p.neg).2 (by decide)
  have hcons := consistent_run switchPlan.step switchPlan.init abstract_wf
    (by intro q hq; simp [switchPlan] at hq) l₁
  exact hcons p hp (hneg L hL l₁ l₂ hL12)

/-! ## Planning problems in a small blocks-and-breakfast vocabulary -/

inductive Obj | milk | cheerios | breakfast | a | b | c | table
  deriving DecidableEq, Repr

inductive Atom | here (o : Obj) | there (o : Obj) | cereal (o : Obj)
  | on (x y : Obj) | clear (x : Obj)
  deriving DecidableEq, Repr

def pos (a : Atom) : Lit Atom := ⟨a, true⟩
def ng (a : Atom) : Lit Atom := ⟨a, false⟩

/-- A plan **necessarily solves** its problem if every precondition of every step (including a
final step whose preconditions are the goals) is necessarily true in its input situation
(p. 10). -/
def NecSolves {β : Type} [DecidableEq β] {τ : Type} [DecidableEq τ] [Enum τ] (P : PPlan β τ) : Prop :=
  ∀ s, ∀ q ∈ (P.step s).pre, NecTrue P s q

theorem necSolves_of_mtc {β : Type} [DecidableEq β] {τ : Type} [DecidableEq τ] [Enum τ] (P : PPlan β τ)
    (hwf : ∀ i, (P.step i).WF) (h : ∀ s, ∀ q ∈ (P.step s).pre, MTC P s q) : NecSolves P :=
  fun s q hq => (mtc_iff P hwf s q).2 (h s q hq)

/-- `get x` (p. 7). -/
def get (x : Obj) : Step Atom := ⟨[pos (.there x)], [pos (.here x), ng (.there x)]⟩

/-- `pour milk x` (p. 7, reconstructed from the figure): needs the milk and the cereal here;
makes breakfast and uses up the milk. -/
def pour (x : Obj) : Step Atom :=
  ⟨[pos (.here .milk), pos (.here x)], [pos (.here .breakfast), ng (.here .milk)]⟩

/-- The final step: its preconditions are the goals. -/
def finish (goals : List (Lit Atom)) : Step Atom := ⟨goals, []⟩

/-- **The incomplete breakfast plan** (p. 7): `get milk` and `get cheerios` unordered, both
before `pour milk cheerios`. -/
def breakfast : PPlan Atom (Fin 4) where
  init := [pos (.there .milk), pos (.there .cheerios), pos (.cereal .cheerios),
    ng (.here .milk), ng (.here .cheerios), ng (.here .breakfast)]
  step := fun i => match i.val with
    | 0 => get .milk | 1 => get .cheerios | 2 => pour .cheerios
    | _ => finish [pos (.here .breakfast)]
  before := mkOrder [(0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]
  irrefl := by decide
  trans := by decide

theorem breakfast_wf : ∀ i, (breakfast.step i).WF := fun i =>
  Step.wf_of_check _ (by revert i; decide)

/-- **The breakfast plan necessarily solves its problem** although it leaves the two `get`
steps unordered. -/
theorem breakfast_solves : NecSolves breakfast :=
  necSolves_of_mtc breakfast breakfast_wf (by decide)

/-- `puton x y` from `z` (p. 14). -/
def puton (x y z : Obj) : Step Atom :=
  ⟨[pos (.on x z), pos (.clear x), pos (.clear y)],
   [pos (.on x y), ng (.on x z), ng (.clear y), pos (.clear z)]⟩

/-- `newtower x` from `z` (p. 14). -/
def newtower (x z : Obj) : Step Atom :=
  ⟨[pos (.on x z), pos (.clear x)], [pos (.on x .table), ng (.on x z), pos (.clear z)]⟩

/-- The Sussman anomaly (p. 2): `c` on `a`; `a`, `b` on the table. -/
def sussmanInit : List (Lit Atom) :=
  [pos (.on .c .a), pos (.on .a .table), pos (.on .b .table), pos (.clear .c), pos (.clear .b)]

def sussmanGoals : List (Lit Atom) := [pos (.on .a .b), pos (.on .b .c)]

/-- **TWEAK's plan after the two step additions** (p. 16): `puton a b` (0) and `puton b c` (1)
unordered, both before the finish (2). -/
def sussman2 : PPlan Atom (Fin 3) where
  init := sussmanInit
  step := fun i => match i.val with
    | 0 => puton .a .b .table | 1 => puton .b .c .table | _ => finish sussmanGoals
  before := mkOrder [(0, 2), (1, 2)]
  irrefl := by decide
  trans := by decide

theorem sussman2_wf : ∀ i, (sussman2.step i).WF := fun i =>
  Step.wf_of_check _ (by revert i; decide)

/-- **"The precondition (clear b) of the second step is unachieved because the first step is
possibly before the second and denies the precondition"** (p. 16): `puton a b` clobbers it. -/
theorem sussman_clobbered :
    Clobberer sussman2 1 (pos (.clear .b)) 0 ∧ ¬ NecTrue sussman2 1 (pos (.clear .b)) :=
  ⟨by decide, fun h => (by decide : ¬ MTC sussman2 1 (pos (.clear .b)))
    ((mtc_iff sussman2 sussman2_wf 1 _).1 h)⟩

/-- **TWEAK's final plan** (p. 17): `newtower c`, then `puton b c`, then `puton a b`. -/
def sussmanFinal : PPlan Atom (Fin 4) where
  init := sussmanInit
  step := fun i => match i.val with
    | 0 => newtower .c .a | 1 => puton .b .c .table | 2 => puton .a .b .table
    | _ => finish sussmanGoals
  before := mkOrder [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  irrefl := by decide
  trans := by decide

theorem sussmanFinal_wf : ∀ i, (sussmanFinal.step i).WF := fun i =>
  Step.wf_of_check _ (by revert i; decide)

/-- **The final Sussman plan necessarily solves the problem.** -/
theorem sussman_solves : NecSolves sussmanFinal :=
  necSolves_of_mtc sussmanFinal sussmanFinal_wf (by decide)

end Examples
end Tweak.Ground
