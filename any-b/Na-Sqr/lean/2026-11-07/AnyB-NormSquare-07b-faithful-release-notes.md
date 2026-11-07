# Faithful Lean formalisation of the square-norm paper (07b)

Lean 4.35.0 checked the proofs of all 12 numbered results in the 07b manuscript using the pinned JNT-2024 formalisation. Conjectures 1.1 and 1.2 are recorded as statements only. The release passed a clean rebuild and all 25 dependency tests.

Six premises remain explicit and unproved. Each result uses only the premises it requires.

- **From JNT-2024** — `DenominatorEstimate4`, `AkhtariTheorem11`, and the earlier Magma calculation `Section46Magma`.
- **From Section 5.6** — completeness of the Java tuple enumeration (`JavaEnumeration`), correctness and completeness of the bounded square search (`JavaSquareSearch`), and completeness of the sequence-specific Magma and PARI/GP quartic results (`ExceptionalQuartics`).
