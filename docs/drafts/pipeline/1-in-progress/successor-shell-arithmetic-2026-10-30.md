# Successor-Shell Arithmetic (SSh)

- **ID:** successor-shell-arithmetic-2026-10-30
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — research programme
- **Source:** `docs/reports/review-3010/opus.md` §7 (the proposed field), §2 M1/M1b/M2, §6 Q1
- **Statement:** Develop the signed additive–multiplicative arithmetic of the successor-shell block
  `n = km + h` of the complete atomic Weil form at growing overlap, beyond conductor modes.

## Goal
Lean programme `formal/GaloisForLFunctions/SuccessorShellArithmetic/`, umbrella
`SuccessorShellArithmetic.lean`, foundational README, unconditional theorems answering the questions
Q1–Q8 of the README and building its tools.

## Plan (topics → modules)
- **A. Shell decomposition (Q2).** `nonRatioForm = Σ_{h≠0} shellForm h`; support `|h| ≤ N(e^w−1)`;
  top band `km ≥ |h|/(e^w−1)`; finite shell count `≤ 2c e^{c/N}`.
- **B. Discreteness (Q3, Q7).** Continuum shell completion: `(2/M)∫_0^c F_c = cq`, so the continuum
  conductor-one energy is `log(1/(2πc)) + β/M → −∞`; lattice gain `≥ log(2πc) − β/M`. Conductor `m ≥ 2`.
- **C. Ramanujan averaging.** Period average of `c_m(ℓ)c_l(ℓ+h)` is `[m=l] c_m(h)`.
- **D. Packets (Q5).** Fixed packets positive for `α < 1/19` with the horizon-decay residual.
- **E. Mean-square conductor cost (Q6).**
- **F. Absolute payment floor (Q4).**
- **G. Signed payment on the conductor span (Q1 first step).**

## Gates
- [x] 0 → 1  in-progress: well-posed, attack ideas
- [x] 2 → 3  formalized: A, B, D, F (with survivor), twin defect; modules checked with
  `lake --old env lean`, standard axioms only, wired into `SuccessorShellArithmetic.lean`

## Status
- Formalized (cards in `3-formalized/`): `the-non-ratio-form-is-a-finite-sum-of-shells`,
  `the-integrality-of-the-shift-repays-the-logarithm`,
  `conductor-packets-positive-below-the-nineteenth-root`,
  `the-shells-alone-cost-the-square-of-the-overlap`,
  `the-shells-and-the-pole-cancel-on-the-top-band`,
  `the-twin-defect-is-a-successor-disagreement-shell`.
- Not built: C (Ramanujan averaging; already in the corpus), E (mean-square conductor cost, Q6),
  G (signed payment beyond the witness, Q1). Open topics are listed in the README §9.
