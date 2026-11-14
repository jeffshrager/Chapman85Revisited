# The postulates of Chapman (1985), as CogLean reads them

Chapman, D. (1985). *Planning for Conjunctive Goals*. MIT AI Laboratory Technical Report 802
(revised from an S.M. thesis, January 1985; published in *Artificial Intelligence* 32, 1987).
Page numbers below are the report's.

Each item is marked by its kind. **Mechanism**: a process the theory posits. **Condition**: a
circumstance a result depends on. **Idealization / simplification**: a choice this
formalization makes that the paper does not.

## The plan representation (§2.1)

| | Postulate | Where | Lean |
|---|---|---|---|
| P1 | **Propositions** (mechanism). A proposition has a content (a tuple of elements) and is negated or not; two propositions are negations of each other if they differ only in sign. | p. 5 | `Tweak.Ground.Lit`, `Lit.neg` |
| P2 | **Variables and codesignation** (mechanism). Elements are variables or constants, infinitely many of each; codesignation constraints force or forbid codesignation; distinct constants never codesignate. | pp. 5–6 | NOT MODELED (ground tier only; S1) |
| P3 | **Execution** (mechanism). A step is executable if its preconditions are true in its input situation; the output situation is the input "minus any propositions denied by the step, plus any propositions asserted by the step". A step may not assert and deny the same proposition. | pp. 6–7 | `Tweak.Ground.apply`, `run`, `Step.WF`, `Executable` |
| P4 | **Incomplete plans and completions** (mechanism). The time order is a partial order on steps; a completion is a total order extending it (and a full binding of variables); "necessarily" is in all completions, "possibly" in some. | p. 5 | `PPlan`, `Completion`, `NecTrue`, `PossTrue` |
| P5 | **Problems and solutions** (mechanism). A problem is an initial situation and goals; a complete plan solves it if executable with the goals true at the end; TWEAK's aim is a plan that necessarily solves the problem. | p. 10 | `Solves`, `Examples.NecSolves` |

## The planner (§2.2–2.3, appendix B)

| | Postulate | Where | Lean |
|---|---|---|---|
| P6 | **The goal-achievement procedure** (mechanism). The necessary truth criterion read as a nondeterministic procedure: establishment (existing situation or new step), then for each clobberer promotion, separation, or a white knight. | pp. 10–12, 49–50 | `tools/tweak.py` only (ground, so no separation). OPEN in Lean. |
| P7 | **Top-level control** (mechanism). Choose an unachieved goal, achieve it; breadth-first (dependency-directed) search over the choices; stop when no goal is unachieved. | pp. 12–13, 49 | `tools/tweak.py` only |

## Extended action representations (§3.2.1, appendices A.5–A.6)

| | Postulate | Where | Lean |
|---|---|---|---|
| E1 | **Conditional steps** (mechanism). Always applicable; if-true postconditions if all preconditions held in the input situation, otherwise if-false postconditions. | p. 45 | `Tweak.Extended.reff` (the reduction's steps) |
| E2 | **Effects depending on the input situation** (mechanism). | pp. 21–22, 47 | `Tweak.Extended.xrun` |
| E3 | **Derived side effects** (deductive closure of situations). | p. 22 | NOT MODELED |

## Choices this formalization makes

| | Choice | Why |
|---|---|---|
| S1 | **Ground** (SIMPLIFIED): no variables; codesignation is equality. | The ground tier already carries the criterion's temporal content; codesignation is the next tier. |
| S2 | The **final situation** is the input situation of a final step whose preconditions are the goals (SIMPLIFIED). | The paper treats initial and final situations separately; this is the standard encoding. |
| S3 | The time order is given **already closed** (a strict partial order). | The paper's constraint maintenance closes posted constraints; it is not modeled. |
| S4 | Situations are lists read as sets. | Decidability; no effect on any theorem. |
