# Critical-feature lattice-summed prime–Gamma budget

- **ID:** `critical-feature-lattice-prime-gamma-budget`
- **Label:** W-H205
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / QUANTITATIVE SOURCE BUDGET
- **RH status:** open
- **Computation used:** mpmath constant audit plus exact rational Lean audit
- **Source:** `HedenmalmCriticalFeatureHolomorphicSectorCoercivity.lean` and
  `HedenmalmWardDefectTransverseGreenSource.lean`
- **Statement:** Sum the explicit real-centered critical-feature prime–Gamma diagonal over the
  nearest-integer height lattice, with a sharp enough window budget to feed an exact 75% receiver.

## Goal

For a height cutoff `T`, construct a finite source-only quantity from the explicit pole, Gamma,
and absolutely convergent von Mangoldt terms in
`criticalFeaturePrimeGammaSourceDiagonal k`, `k : ℤ`, and prove a quantitative upper bound whose
leading constant is below the `1/8` off-line census threshold after the existing
`64/2025` nearest-integer Ward–Green quantum is applied.

The result must be proved from the pre-divisor prime–Gamma formula.  An inequality stated directly
for a sum over Xi zeros is a receiver restatement and does not discharge this card.

## Exact dependency-closed receiver

Already Lean-proved:

1. every strict-right Xi multiplicity copy is detected by its nearest integer feature with charge
   at least `64/2025`;
2. every fixed-feature Ward–Green trace is bounded by an explicit prime–Gamma source diagonal;
3. total zero multiplicity splits as on-line multiplicity plus twice strict-right multiplicity.

Needed source estimate: a lattice-window bound strong enough to imply that strict-right
multiplicity is at most one eighth of total multiplicity.

The formalized sharp receiver now uses the diagonal-subtracted budget directly: if the corrected
lattice budget is at most `(4/25) N`, then strict-right multiplicity is at most `N/8`, hence at
least `3N/4` copies lie on the critical line.

## Approach

1. Expand the four source cups defining `criticalFeaturePrimeGammaSourceDiagonal` into pole,
   Gamma, and von Mangoldt terms.
2. Sum each rational Cauchy translate over a finite integer lattice before any divisor expansion.
3. Use exact rational-lattice identities or monotone integral comparison for tails; preserve
   cancellation between reflected source cups whenever absolute values lose the required constant.
4. Compare the resulting leading term with the Riemann–von Mangoldt census and numerically
   pre-certify the constant before formalization.
5. Formalize the strongest dependency-closed source theorem.  If the `1/8` margin fails, record the
   exact sharp obstruction and derive the best proportion coefficient instead.

## Hostile falsifiers

- Summing `xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal` after rewriting it
  as a zero sum is circular for this producer.
- The existing uniform constant `fiveShiftWardGreenUpperConstant` is intentionally coarse and may
  destroy every useful density constant.
- Replacing the lattice window by the whole real line may reconstruct nonholomorphic divisor mass
  rather than yield an independently bounded source.
- Absolute-value bounds on all four prime–Gamma cups may lose the reflection cancellation needed
  for 75%.
- A theorem whose premise is already the desired lattice budget is only an interface, not progress.

## Gates

- [x] 0 → 1: well-posed source-pure target and exact receiver identified
- [x] explicit finite lattice source formula
- [x] numerical `1/8` margin pre-certified
- [x] hostile circularity audit passed for raw and corrected algebraic budgets
- [x] complete paper proof of raw no-go, exact diagonal subtraction, and 75% receiver
- [x] Lean theorem and targeted build
- [x] axiom and module lint audit (standard `propext`/choice/quotient axioms only; global lint's
      remaining failure is unrelated `HTGeometry.SteinbergIndexAvoidance` umbrella reachability)
- [ ] pre-divisor pole--Gamma--von-Mangoldt upper bound `correctedBudget ≤ (4/25) N`

## No-go closure

- **Exact killing theorem/mechanism:**
  `card_mul_thirtyTwo_twentyFive_le_rawLatticeBudget` proves every multiplicity copy deposits at
  least `32/25` in the raw nearest-integer prime--Gamma diagonal.  The nominal 75% source scale is
  `8/2025`; `(32/25)/(8/2025)=324`.  Therefore
  `rawLatticeBudget_threeQuartersScale_forces_empty` proves that raw target can hold only for an
  empty packet.  Summing uncorrected diagonals is dead.
- **Strongest positive survivor:** subtract the exact critical-line feature energy before lattice
  summation.  `criticalFeatureHermitian_add_line_le_two_sourceDiagonal` sharpens the sector bound
  on the line, and
  `finite_strictRight_card_mul_thirtyTwo_twentyFive_le_offLineLatticeBudget` gives the corrected
  count without the coarse Ward constant.  The exact receiver is
  `three_quarters_line_of_sharp_primeGammaOffLineLatticeBudget`.
- **New insight:** diagonal subtraction changes the useful source threshold from the impossible
  raw `8/2025` scale to the sharp corrected `4/25` scale.  Abel traces converge to the correction,
  but are still divisor-indexed; the remaining producer must evaluate or dominate the corrected
  Abel lattice budget using only pole, Gamma, and von Mangoldt data.
- **Status:** active.

## Log

- 2026-08-16 — card created after improved declaration search found an unconditional nearest-integer
  Ward–Green quantum and fixed-feature prime–Gamma Hermitian majorant, but no lattice-summed source
  budget.
- 2026-08-16 — Formalized raw lattice no-go, exact line/off-line source separation, corrected
  lattice budget, Abel convergence, multiplicity-exact count, and sharp 75% receiver in
  `HedenmalmCriticalFeatureLatticePrimeGammaBudget.lean`.  Targeted Lean build passed.  mpmath
  confirmed the raw factor-324 obstruction and exposed the old Ward constant `C ≈ 4645.542`; the
  sharp corrected receiver eliminates `C` entirely.
