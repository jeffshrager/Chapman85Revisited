import Tweak.Ground.Examples

/-!
# Problems, solutions, and the looping outcome

Chapman (1985), §2.1 p. 10 (problems and solutions); §2.3 p. 13 and §A.2 pp. 43–44 (the
outcomes lemma).

A *problem* is an initial situation and goals; a complete plan *solves* it if every step's
preconditions are true in its input situation and the goals are true at the end (p. 10).

The outcomes lemma says that each of TWEAK's three outcomes — success, failure, and
nontermination — occurs for some problem. Its nontermination example (p. 44) is the problem
with initial situation `¬g, ¬h`, goals `g, h`, and two operators: one needs `¬h` and asserts
`g`, the other needs `¬g` and asserts `h`. "TWEAK loops on this problem, building plans that
are longer and longer chains of steps that alternately assert g and h." The
correctness/completeness theorem then requires that the problem has no solution, which
`loop_unsolvable` proves.

**But TWEAK does not loop on the problem as printed; it fails.** No operator asserts `¬g` or
`¬h` (`loop_no_reassert`), so the only establisher of either is the initial situation and no
white knight can protect it: each operator's step clobbers the other's precondition, and once
one step of each kind is present no modification helps. Nothing ever makes the final goals
unachieved again, so no further steps are added: the search space is finite, and breadth-first
search exhausts it after 9 plans (`tools/tweak.py`). The chains Chapman describes arise when
the operators have *postconditions* `g, ¬h` and `h, ¬g`: each new step clobbers the other goal
and needs a white knight, which needs another. That problem is also unsolvable
(`loop2_unsolvable`), and its search space grows without bound (`tools/tweak.py`). OPEN: the
search itself is not formalized, so the claims about TWEAK's behavior rest on the program.
-/

set_option linter.unusedSectionVars false

namespace Tweak.Ground

variable {α : Type} [DecidableEq α] {ι : Type}

/-- **A complete plan is executable** (p. 6): each step's preconditions are true in its input
situation. -/
def Executable (st : ι → Step α) (init : List (Lit α)) (l : List ι) : Prop :=
  ∀ a i b, l = a ++ i :: b → ∀ q ∈ (st i).pre, q ∈ run st init a

/-- **A complete plan solves a problem** (p. 10): it is executable from the initial situation
and the goals are true after it. -/
def Solves (st : ι → Step α) (init goals : List (Lit α)) (l : List ι) : Prop :=
  Executable st init l ∧ ∀ g ∈ goals, g ∈ run st init l

theorem Executable.of_snoc {st : ι → Step α} {init : List (Lit α)} {l : List ι} {x : ι}
    (h : Executable st init (l ++ [x])) :
    Executable st init l ∧ ∀ q ∈ (st x).pre, q ∈ run st init l := by
  refine ⟨fun a i b hab q hq => h a i (b ++ [x]) (by simp [hab]) q hq, ?_⟩
  exact h l x [] rfl

namespace Examples

inductive GH | g | h
  deriving DecidableEq, Repr

/-- The two operators of the nontermination example (p. 44). -/
def loopOps : Fin 2 → Step GH := fun i =>
  if i.val = 0 then ⟨[⟨.h, false⟩], [⟨.g, true⟩]⟩ else ⟨[⟨.g, false⟩], [⟨.h, true⟩]⟩

def loopInit : List (Lit GH) := [⟨.g, false⟩, ⟨.h, false⟩]
def loopGoals : List (Lit GH) := [⟨.g, true⟩, ⟨.h, true⟩]

/-- **The looping problem of the outcomes lemma has no solution** (p. 44), as the
correctness/completeness theorem requires of any problem on which TWEAK does not halt: no
executable sequence of the two operators ever makes `g` and `h` true together. -/
theorem loop_unsolvable : ∀ l, ¬ Solves loopOps loopInit loopGoals l := by
  have hwf : ∀ i, (loopOps i).WF := fun i => Step.wf_of_check _ (by revert i; decide)
  have hcons := consistent_run loopOps loopInit hwf
    (fun q hq => by simp [loopInit] at hq; rcases hq with rfl | rfl <;> decide)
  -- invariant: in every state an executable plan reaches, g and h are not both true
  have key : ∀ l, Executable loopOps loopInit l →
      ¬ (⟨.g, true⟩ ∈ run loopOps loopInit l ∧ ⟨.h, true⟩ ∈ run loopOps loopInit l) := by
    intro l
    induction l using snoc_induction with
    | nil => intro _; decide
    | snoc l x ih =>
      intro hex ⟨hg, hh⟩
      obtain ⟨-, hpre⟩ := hex.of_snoc
      rw [run_snoc, mem_apply] at hg hh
      have hc := hcons l
      by_cases hx : x.val = 0
      · have hx' : x = 0 := Fin.ext hx
        subst hx'
        have hnh : (⟨.h, false⟩ : Lit GH) ∈ run loopOps loopInit l := hpre _ (by decide)
        rcases hh with hh | ⟨hh, -⟩
        · exact absurd hh (by decide)
        · exact hc _ hh hnh
      · have hx' : x = 1 := Fin.ext (by omega)
        subst hx'
        have hng : (⟨.g, false⟩ : Lit GH) ∈ run loopOps loopInit l := hpre _ (by decide)
        rcases hg with hg | ⟨hg, -⟩
        · exact absurd hg (by decide)
        · exact hc _ hg hng
  intro l ⟨hex, hgoal⟩
  exact key l hex ⟨hgoal _ (by decide), hgoal _ (by decide)⟩

/-- In the printed looping problem no operator re-asserts `¬g` or `¬h`. -/
theorem loop_no_reassert : ∀ i : Fin 2,
    (⟨.g, false⟩ : Lit GH) ∉ (loopOps i).post ∧ (⟨.h, false⟩ : Lit GH) ∉ (loopOps i).post := by
  decide

/-- The operators of the looping problem as the described behavior requires: each asserts one
goal and denies the other; no preconditions. -/
def loopOps2 : Fin 2 → Step GH := fun i =>
  if i.val = 0 then ⟨[], [⟨.g, true⟩, ⟨.h, false⟩]⟩ else ⟨[], [⟨.h, true⟩, ⟨.g, false⟩]⟩

/-- **The corrected looping problem has no solution either**: the last step always denies one
of the goals. -/
theorem loop2_unsolvable : ∀ l, ¬ Solves loopOps2 loopInit loopGoals l := by
  intro l ⟨_, hgoal⟩
  have hg := hgoal ⟨.g, true⟩ (by decide)
  have hh := hgoal ⟨.h, true⟩ (by decide)
  revert hg hh
  induction l using snoc_induction with
  | nil => decide
  | snoc l x _ =>
    intro hg hh
    rw [run_snoc, mem_apply] at hg hh
    by_cases hx : x.val = 0
    · have hx' : x = 0 := Fin.ext hx
      subst hx'
      rcases hh with hh | ⟨-, hd⟩
      · exact absurd hh (by decide)
      · exact hd (by decide)
    · have hx' : x = 1 := Fin.ext (by omega)
      subst hx'
      rcases hg with hg | ⟨-, hd⟩
      · exact absurd hg (by decide)
      · exact hd (by decide)

end Examples
end Tweak.Ground

namespace Tweak.Ground

variable {α : Type} [DecidableEq α] {σ : Type} [DecidableEq σ] [Enum σ]

/-- **Correctness** (the first half of the correctness/completeness theorem, p. 13): if every
precondition of every step of an incomplete plan is necessarily true — TWEAK's termination
test, with the goals as preconditions of a final step `fin` — then every completion is an
executable complete plan, and the goals are true in the input situation of `fin`. "Any of its
completions can be chosen for execution" (p. 10). -/
theorem correctness (P : PPlan α σ) (fin : σ)
    (h : Examples.NecSolves P) (L : List σ) (hL : Completion P L) (l₁ l₂ : List σ)
    (hL12 : L = l₁ ++ fin :: l₂) :
    Executable P.step P.init L ∧ Solves P.step P.init (P.step fin).pre l₁ := by
  refine ⟨fun a i b hab q hq => h i q hq L hL a b hab,
    fun a i b hab q hq => ?_, fun g hg => h fin g hg L hL l₁ l₂ hL12⟩
  exact h i q hq L hL a (b ++ fin :: l₂) (by simp [hL12, hab])

end Tweak.Ground
