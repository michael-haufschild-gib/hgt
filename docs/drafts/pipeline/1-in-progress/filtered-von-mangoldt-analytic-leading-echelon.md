# Filtered von Mangoldt analytic leading-echelon transfer

- **ID:** filtered-von-mangoldt-analytic-echelon
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Lean-corpus synthesis: `PrimeValuationLeadingEchelon`,
  `PrimeClockAnalyticEulerCompletion`, and `XiShiftPrimeExposure`
- **Statement:** The actual upper-end Dirichlet germ with coefficients
  `Lambda(n) (1 - n^(-2))` is hypertranscendental over the rational coordinate field; more
  generally, prime-dependent nonzero private valuation coefficients force leading-echelon
  differential independence and any formally differentially independent finite-abscissa family
  transfers analytically.

## Goal

Close the unrecorded interface gap between the formal arithmetic-function differential matroid and
the actual finite-abscissa meromorphic field, then apply it to the exact positive prime source
exposed by the `+2` shift defect of `xi'/xi`.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact leaf checks green, ordinary-axioms audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Replace the constant private coefficient in the prime-valuation leading-echelon law by a
   prime-dependent coefficient with no zero prime values.  For each source, the unit coefficient
   pattern still has infinite tail support, so the separated prime packet and Jacobian proof are
   unchanged.
2. Extract the analytic transfer proof so its exact input is formal differential independence over
   `C`; retain the stronger clock-independent theorem as a corollary.
3. Regard `Lambda(n) (1 - n^(-2))` as a finite-abscissa arithmetic source.  Its support is contained
   in positive prime powers, and at every prime `p` its coefficient is
   `log(p) (1 - p^(-2))`, which is nonzero.
4. Apply the one-source prime-dependent leading-echelon law, then the formal-to-analytic transfer.
   The resulting carrier is the exact L-series in `xi_logDeriv_shift_two_exposes_prime_source`.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Not falsified.
- **Strongest positive survivor:** Pending exact Lean verification.
- **New insight:** The filtered completed-prime source does not require a new general analytic
  Ostrowski theorem: the corpus's arithmetic Jacobian and rational-coordinate uniqueness bridge
  already suffice once their interfaces are aligned.
- **Status:** Internal corpus audit complete; novelty audit remains provisional until the exact
  theorem and axiom surface pass.

## Log

- 2026-07-18 — created in 1-in-progress after corpus-first audit; paper mechanism identified.
