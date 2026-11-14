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
`loop_unsolvable` proves. That TWEAK's search does not terminate on it is not modeled here
(OPEN: the search is not formalized; `tools/tweak.py` runs it).
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

end Examples
end Tweak.Ground
