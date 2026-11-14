# Working on Chapman85Revisited

A self-contained CogLean-style formalization of Chapman (1985), *Planning for Conjunctive
Goals* (TWEAK, the modal truth criterion), aiming at the paper "TWEAK Revisited: Chapman's
famous proof rendered in Lean". The source PDF is `~/Desktop/CogLean/papers/1985_Chapman_AITR-802.pdf`
(scanned; page numbers are the report's).

## Build

- Lean 4.35.0 via elan (`export PATH=$HOME/.elan/bin:$PATH`); **no Mathlib** (Jeff: not
  needed). `lake build`. One library `Tweak`; `Ground` ← `Extended`.
- Every theorem fully proved: no `sorry`; `#print axioms` shows only `propext`, `Quot.sound`,
  `Classical.choice`.
- `python3 tools/mtc_check.py` and `python3 tools/tweak.py` have the same semantics as the Lean
  definitions; every witness used in Lean is found or cross-checked there.
- The paper: `cd paper && make`; rebuild after every substantial edit;
  `python3 tools/check_paper.py` checks cited Lean names.

## Conventions

- Postulates are in `notes/POSTULATES.md` with page references; every claim and its status is
  in `notes/CLAIMS.md`. Keep both current. Mark `SIMPLIFIED:`, `NOT MODELED:`, `OPEN:` in
  docstrings.
- Headline docstrings begin in bold and quote or cite the page.
- Commit after every successful major step. The GitHub repo is public
  (all CogLean repos are); push when Jeff asks.
