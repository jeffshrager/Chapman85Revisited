# The claims of Chapman (1985) and their status

Statuses: **proved** (a Lean theorem, no `sorry`, standard axioms); **refuted** (a Lean
counterexample or contrary theorem); **reinterpreted** (true in a different form, stated);
**empirical** (checked by the Python prototype only); **OPEN** (not yet formalized).
"Ground" means without variables (postulate P2 not modeled).

## The plan representation and the truth criterion (§2.1, §A.1)

| # | Claim | Status |
|---|---|---|
| T1 | Time's arrow lemma: what holds in a situation depends only on the steps before it (p. 38). | **proved**, definitional in the list model (`Tweak.Ground.run_append`). |
| T2 | Truth criterion for complete plans: `p` is true in `s` iff asserted in some `t` at or before `s` and not denied between (p. 39). | **proved** (`Tweak.Ground.mem_run_iff`; `mem_run_of_covered`; with situation-dependent effects, `Tweak.Extended.xrun_source`). |
| T3 | Completion lemma: every incomplete plan has a completion (p. 40). | **proved**, ground (`exists_completion`). |
| T4 | Temporal consistency lemma (p. 40). | **proved** in the stronger form the proof uses: any ranking monotone in the order has a completion sorted by it (`exists_completion_rank`). |
| T5 | Codesignation and noncodesignation consistency lemmas (pp. 40–41). | OPEN (variables). |
| T6 | "Necessarily before" can be read off the order. | **proved** (`necBefore_iff`). |
| T7 | **The modal truth criterion** for necessary truth (pp. 9, 41–43). | **proved, ground**, both directions (`Tweak.Ground.mtc_iff`; sufficiency needs no hypothesis, `necTrue_of_mtc`; necessity needs well-formed steps). With codesignation: OPEN. |
| T8 | "The criterion for possible truth is exactly analogous, with all the modalities switched" (p. 9). | **refuted, ground.** The switched criterion is necessary for possible truth (`switched_of_possTrue`) but not sufficient: a five-step plan satisfies it while `p` is true in no completion (`Examples.switched_not_sufficient`). |
| T9 | The simple criterion (necessary establisher, no possibly-intervening possible denier) is sufficient but not necessary; the white-knight clause is needed, "as illustrated by the odd plan" (p. 8–9). | **proved, and sharpened**: sufficient (`mtc_of_simple`); the white-knight clause is needed even without variables, where the odd plan cannot arise (`Examples.wk_needed`: two crossed establisher/clobberer pairs). |
| T10 | The criterion runs in polynomial time (p. 9). | **reinterpreted**: necessary truth is decided by the criterion, which quantifies over triples of steps (`decNecTrue`); the time bound itself is not formalized. |
| T11 | The breakfast plan (p. 7) solves its problem though two steps are unordered. | **proved** (`Examples.breakfast_solves`; the step definitions are reconstructed from the figure). |

## TWEAK (§2.2–2.4, §A.2–A.3)

| # | Claim | Status |
|---|---|---|
| W1 | Correctness: if TWEAK terminates with a plan, it solves the problem (p. 13). | **proved**: a plan whose preconditions and goals are all necessarily true is, in every completion, an executable solution (`Tweak.Ground.correctness`). The termination test is the criterion, proved equal to necessary truth (T7). |
| W2 | Completeness: if TWEAK fails or does not halt, no solution exists (p. 13). | **empirical, ground**: on 300 random ground domains, breadth-first TWEAK (plans ≤ 4 steps) finds a plan exactly when linear search finds a solution of ≤ 4 steps (210 solvable) (`tools/tweak.py`). OPEN in Lean: the procedure is not formalized. The paper's proof (p. 44) is a sketch: it argues from breadth-first search and finite branching, but not that some sequence of modifications reaches a solution. |
| W3 | Outcomes lemma: success, failure and nontermination all occur (p. 13, 43–44). | Success and failure: trivial, not formalized. **Nontermination example refuted as printed**: the problem is unsolvable (`Examples.loop_unsolvable`), but no operator re-asserts `¬g` or `¬h` (`loop_no_reassert`), so no white knight exists and TWEAK *fails* after 9 plans whatever the bound (`tools/tweak.py`). With postconditions `g, ¬h` and `h, ¬g` instead of the preconditions, the problem is still unsolvable (`loop2_unsolvable`) and the search grows without bound (5, 17, 93, 813 plans at bounds 2, 4, 6, 8): the behavior the paper describes. |
| W4 | The Sussman anomaly trace (pp. 14–17). | **proved** at the checked stages: after the two additions `(clear b)` is clobbered by `puton a b` (`Examples.sussman_clobbered`); the final plan necessarily solves the problem (`Examples.sussman_solves`). The program finds that plan (`tools/tweak.py`). |
| W5 | "Every step is introduced to assert some goal … it is never the case that the only way to achieve a goal is to remove a step" (p. 12). | untested. |
| W6 | Declobbering by a white knight distinct from the establisher is "pretty useless" (p. 32). | Not a claim about truth. As a truth test the clause is indispensable (T9). |

## Extended representations (§3.2, §A.4–A.6)

| # | Claim | Status |
|---|---|---|
| X1 | With effects that depend on the input situation, steps can clobber synergistically and the criterion fails (pp. 21–22, McAllester). | **proved**: no step denies "there is room" from the establishing situation (`Synergy.no_single_denier`), each denies it after another (`second_denies`), and a completion falsifies it (`synergy`). |
| X2 | Intractability theorem: necessary truth with conditional actions is NP-hard (p. 23, 45–46). | **proved and reinterpreted**: the reduction from DNF validity is correct (`Tweak.Extended.reduction_correct`). Since DNF validity is coNP-complete, the theorem is coNP-hardness under many-one reductions (NP-hardness under Turing reductions). Polynomial size of the construction: evident, not formalized. |
| X3 | First undecidability theorem: Turing machines encode as planning problems with an infinite initial situation (p. 13, 44–45). | OPEN. |
| X4 | Second undecidability theorem: two-counter machines, finite initial situation, situation-dependent effects (p. 24, 47). | OPEN. |
| X5 | Range restrictions on variables break the criterion (the "pathological plan", p. 27). | OPEN (variables). |
