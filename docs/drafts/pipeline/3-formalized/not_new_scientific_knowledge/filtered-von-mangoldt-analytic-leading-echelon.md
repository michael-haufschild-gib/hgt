# Filtered von Mangoldt analytic leading-echelon transfer

- **ID:** filtered-von-mangoldt-analytic-echelon
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
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
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, exact leaf checks green, ordinary-axioms audit PASS
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

## Paper proof [PROVED HERE]

For a finite source family with pairwise distinct private valuation layers, suppose the private
coefficient of source `r` at prime `p` is `c_r(p) ≠ 0`.  In every finite jet rectangle, the
private-layer row is `c_r(p)` times the usual rotated-log monomial row.  Multiplication of all
columns at coordinate `p` by the common nonzero scalar `c_r(p)` preserves tail coefficient
independence.  The existing separated-prime packet therefore supplies an invertible Jacobian minor,
so the family is differentially independent.  Constant private coefficients are a specialization.

If a finite-abscissa arithmetic family is formally differentially independent over `C`, its full
rotated-log jet family is algebraically independent in the arithmetic-function ring.  Injectivity
of the finite-abscissa subtype and uniqueness of polynomial-weighted L-series transfer this to the
upper-end meromorphic field over the genuine coordinate field `C(z)`.  Thus no prime-clock quotient
hypothesis is needed at the analytic interface.

For `a(n) = Lambda(n) (1 - n^(-2))`, nonzero coefficients occur only at positive prime powers.  At
every prime `p`, `a(p) = log(p) (1 - p^(-2)) ≠ 0`, since `p > 1`.  The one-source prime-dependent
echelon law and the formal-to-analytic transfer make its upper-end carrier hypertranscendental over
`C(z)`.  Finally `xi_logDeriv_shift_two_exposes_prime_source`, evaluated at `s = -I z`, identifies
the underlying germ with the rationally corrected `+2` shift defect of `xi'/xi`.

## Novelty audit

- **Verdict:** Not new mathematical knowledge; new formal synthesis and interface closure.
- **Reason:** Ostrowski's 1920 theorem already gives difference-differential independence for an
  ordinary Dirichlet series whose nonzero indices involve infinitely many primes.  The filtered
  von Mangoldt support satisfies that hypothesis.  Modern expositions also record the
  polynomial-in-`s` strengthening, which yields the `C(s)` formulation after clearing
  denominators.
- **Primary sources:** A. Ostrowski, *Über Dirichletsche Reihen und algebraische
  Differentialgleichungen*, Math. Z. 8 (1920), 241–298; English translation
  [arXiv:2211.02088](https://arxiv.org/abs/2211.02088).  The shift-strengthened context is also
  recorded in Chiang–Feng, [Difference independence of the Riemann zeta function](https://arxiv.org/abs/math/0610479).
- **Formal contribution:** The corpus no longer needs a missing general analytic Ostrowski
  interface for this source: the arithmetic Jacobian, finite-abscissa uniqueness theorem, and the
  actual xi shift identity are now connected unconditionally.

## Lean certificate

- General law:
  `primeValuationLeadingEchelon_differentialIndependent_of_primeDependent`.
- Discharged analytic interface:
  `differentialIndependent_finiteAbscissaPrimeProfiles_of_formal`.
- Actual source theorem:
  `RHTower.filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver`.
- Value relation:
  `RHTower.filteredVonMangoldtUpperEndGerm_eq_xiLogDerivShiftTwoPrimeDefect`.
- Validation: exact source and object checks pass; all four theorem layers use only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-18 — created in 1-in-progress after corpus-first audit; paper mechanism identified.
- 2026-07-18 — exact Lean source/object checks and ordinary-axioms audit passed; moved to
  3-formalized/not-new-scientific-knowledge after external Ostrowski audit.
