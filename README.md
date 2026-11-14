# Chapman85Revisited

*TWEAK Revisited: Chapman's famous proof rendered in Lean.* A self-contained Lean 4
formalization of David Chapman's *Planning for Conjunctive Goals* (MIT AI-TR-802, 1985;
*Artificial Intelligence* 32, 1987), the report that introduced TWEAK and the **modal truth
criterion**. In the CogLean style: the paper's mechanisms stated as postulates with page
references (`notes/POSTULATES.md`), and its claims proved, refuted or reinterpreted
(`notes/CLAIMS.md`). It depends on nothing but Lean's core library — no Mathlib.

Headline results (ground tier, i.e. without variables):

* The modal truth criterion is necessary and sufficient for necessary truth
  (`Tweak.Ground.mtc_iff`), with Chapman's lemmas along the way.
* The white-knight clause is needed even without variables (`Examples.wk_needed`).
* The paper's possible-truth criterion, "with all the modalities switched", is necessary but
  not sufficient (`switched_of_possTrue`, `Examples.switched_not_sufficient`).
* Correctness of TWEAK's termination test (`Tweak.Ground.correctness`).
* The outcomes lemma's nontermination example has no solution (`loop_unsolvable`), but as
  printed TWEAK fails on it rather than looping; a corrected version loops (`tools/tweak.py`).
* The intractability theorem's reduction is correct (`Tweak.Extended.reduction_correct`):
  necessary truth with conditional actions is coNP-hard.
* McAllester's synergy example (`Tweak.Extended.Synergy`).

## Layout

| Path | Contents |
|---|---|
| `Tweak/Ground/Basic.lean` | Propositions, steps, execution; the truth criterion for complete plans |
| `Tweak/Ground/Plan.lean` | Incomplete plans, completions, ranked completions, necessary/possible truth |
| `Tweak/Ground/MTC.lean` | The modal truth criterion; the switched criterion |
| `Tweak/Ground/Examples.lean` | White knights, the switched counterexample, breakfast, Sussman anomaly |
| `Tweak/Ground/Problem.lean` | Problems, solutions, correctness; the looping problem |
| `Tweak/Extended/Conditional.lean` | Situation-dependent effects; the intractability reduction |
| `Tweak/Extended/Synergy.lean` | McAllester's synergistic clobbering |
| `tools/mtc_check.py` | Brute-force check of the ground criterion on random plans |
| `tools/tweak.py` | Executable ground TWEAK: Sussman, completeness check, looping problems |
| `notes/` | Postulates, claims and their status |
| `paper/` | The paper |

## Build

Lean 4.35.0, core only:

```
lake build
python3 tools/mtc_check.py
python3 tools/tweak.py
cd paper && make
```

Every theorem is fully proved, with no `sorry`, and depends only on Lean's standard axioms.
