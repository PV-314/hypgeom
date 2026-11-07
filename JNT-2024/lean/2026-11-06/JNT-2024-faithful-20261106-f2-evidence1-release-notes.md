# Bounds on the number of squares in recurrence sequences

Lean formalisation of Paul M Voutier’s manuscript, version **2026-11-06d**. The release package is **JNT-2024-faithful-20261106-f2-evidence1**, containing the audited **f2** proof sources.

The formalisation proves Theorem 1.4 under its stated hypotheses and three explicit external inputs. The theorem bounds the number of distinct squares among the sequence terms by two, with a bound of three in the listed exceptional cases. Its Lean proof follows the revised Section 5, and the Section 6 upper bounds use that same theorem.

The three external inputs are the denominator estimate for Lemma 2.3(a) (`DenominatorEstimate4`), Akhtari’s Theorem 1.1 (`AkhtariTheorem11`), and the Section 4.6 Magma result (`Section46Magma`). For the 63 quartics, Lean certifies the solution lists for $1\le y\le109$. The Magma input asserts that every positive solution lies within that bound. The exact maxima at $r=3$ in Lemma 2.3(a) are recorded separately and are independent of the proof of Theorem 1.4.

## Build and audit

The clean f2 build used Lean 4.35.0 and rebuilt all 218 project modules. The axiom audit covered 3,101 compiled declarations, with explicit axiom reports for all 45 principal declarations. Only `propext`, `Classical.choice` and `Quot.sound` occurred. All 92 checks of specified proof steps passed.

The evidence1 revision packages that build and its audit logs together with verification records from fresh ZIP extractions. Its verification reused the f2 build evidence. After extraction, see `release/EVIDENCE.md` for the evidence index, `release/README.md` for reproduction instructions, and `reports/` for correspondence, corrections, external inputs and omissions.

## Two manuscript corrections identified after packaging

- **Lemma 3.10, proof, case (iv).** For odd $t$ and even $u$, parity gives $t^2-du^2\equiv1\pmod4$. This contradicts the residue $0$ required by the norm equation. The Lean proof uses the correct parity calculation.
- **Lemma 3.13, proof, finite-search paragraph.** The numerator in the second search condition, with right-hand side $300$, should be $21.12\sqrt d\,y_k$. The Lean theorem includes $\sqrt d$ in the bound with right-hand side $190$. Its finite case uses a separate certified proof. The historical search sentence itself remains unformalised.

These two entries supplement the corrections report shipped in the ZIP. Both concern intermediate manuscript steps and preserve the formal conclusion of Theorem 1.4.
