# One-local Pauli word linear-universality no-go

- **ID:** `one-local-pauli-word-linear-universality-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / HOSTILE BOUNDARY
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O4
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/OneLocalPauliWordLinearUniversalityNoGo.lean`
- **Novelty:** `[NOT CLAIMED]`; exact obstruction certificate, not paper headline

## Exact theorem

On an `n`-qubit register, let `E_n` be the endpoints of matrix words of
length at most `n` whose factors are Pauli matrices of physical weight at
most one. Every full Pauli matrix `P_s` belongs to `E_n`; more sharply it is
a product of at most `wt(s)` such factors. Since the full Pauli family is a
basis of the matrix algebra,

\[
 \operatorname{span}_{\mathbb C} E_n=M_{2^n}(\mathbb C).
\]

Thus a word family with uniformly linear circuit length already has maximal
linear span in the exponentially large operator algebra.

## No-go closure

- **Exact killing mechanism:** full linear span, Lie closure, replica rank,
  or Hall expansion cannot alone lower-bound circuit word length. Strongest
  possible linear coverage occurs inside length-`n` one-local words.
- **Strongest positive survivor:** correct O4 invariant must remain nonlinear
  after circuit selector is formed: robust word-metric injectivity radius,
  annular shortcut-centre packing, or equivalent circuit-tube energy.
- **New insight:** newly proved linear-depth all-replica Hall law closes a
  representation-theoretic depth question, not Brown--Susskind growth. Any
  claimed Hall-to-complexity transfer must add a quantitative nonlinear
  separation theorem that fails on `E_n`.
- **Status:** paper proof dependency-closed and formalized. Targeted
  elaboration passes; capstone axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Lean declarations

- `QuantumAlg.exists_oneLocalPauliWord`
- `QuantumAlg.pauliMat_mem_oneLocalPauliWordEndpoints`
- `QuantumAlg.span_oneLocalPauliWordEndpoints_eq_top`

## Gates

- [x] Exact bounded-length local-word factorization
- [x] Full operator-span capstone
- [x] Targeted Lean verification
- [x] Standard-axiom audit
- [x] Umbrella import
- [ ] Nonlinear selector-aware O4 theorem

## Log

- 2026-08-05 — Formalized after hostile review of the linear-depth
  all-replica Hall theorem exposed the missing nonlinear implication.
