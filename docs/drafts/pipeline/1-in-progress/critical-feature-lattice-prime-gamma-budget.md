# Critical-feature lattice-summed prime–Gamma budget

- **ID:** `critical-feature-lattice-prime-gamma-budget`
- **Label:** W-H205
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / QUANTITATIVE SOURCE BUDGET
- **RH status:** open
- **Computation used:** pending numerical pre-certification
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
- [ ] explicit finite lattice source formula
- [ ] numerical `1/8` margin pre-certified
- [ ] hostile circularity audit passed
- [ ] complete paper proof
- [ ] Lean theorem and targeted build
- [ ] axiom and formal lint audit

## No-go closure

- **Exact killing theorem/mechanism:** pending.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** active.

## Log

- 2026-08-16 — card created after improved declaration search found an unconditional nearest-integer
  Ward–Green quantum and fixed-feature prime–Gamma Hermitian majorant, but no lattice-summed source
  budget.
