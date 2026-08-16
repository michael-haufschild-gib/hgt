# Suzuki Weil position-torque recurrence, formalized

- **ID:** `suzuki-weil-position-torque-recurrence`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-weil-position-torque-recurrence.md`
- **Lean (built for this card):**
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueTentSeries.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueTentLaplace.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorquePrimeSeries.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorquePrimeLaplace.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueArchLaplace.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorquePrimeOrder.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueArchOrder.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueTotalTransform.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueEulerTransform.lean`
  - `formal/GaloisForLFunctions/RHTower/LaplaceAbscissaExists.lean`
  - `formal/GaloisForLFunctions/RHTower/ComplexLaplaceHolomorphy.lean`
  - `formal/GaloisForLFunctions/RHTower/RealJetsOfHolomorphic.lean`
  - `formal/GaloisForLFunctions/RHTower/LandauSingularAtAbscissa.lean`
  - `formal/GaloisForLFunctions/RHTower/RiemannXiRealAxisNonvanishing.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueContinuationAnalytic.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueContinuationPole.lean`
  - `formal/GaloisForLFunctions/RHTower/HeadLaplaceEntire.lean`
  - `formal/GaloisForLFunctions/RHTower/TailMeasureLaplace.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueTailCarrier.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTailTransform.lean`
  - `formal/GaloisForLFunctions/RHTower/OneSignTailImpossible.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiTorqueCofinalSign.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ConvexDiffCountableConnected.lean`
- **Lean (inherited, already in the corpus):**
  - `formal/GaloisForLFunctions/RHTower/SuzukiWeilPositionTorqueCurvature.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiWeilPrimeCommutatorTorque.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiResolventPositionTorquePromotion.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiSecondDefectParityCommutator.lean`,
    `SuzukiSecondDefectCompactParitySource.lean`
  - `formal/GaloisForLFunctions/RHTower/LandauAbscissaRigidity.lean`,
    `LandauAbscissaWitnesses.lean`, `LaplaceTransformMomentDerivative.lean`
  - `formal/GaloisForLFunctions/RHTower/XiLogDerivNonholonomic.lean`,
    `XiRealAxisNonvanishing.lean`, `RiemannXiZerosInfinite.lean`,
    `XiWeilDivisorHilbert.lean`, `FarFieldAnchor.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)`, `(2)` the restricted-Weil distribution kernel and its smooth remainder | `suzukiWeilRemainderSecondDerivative`, `suzukiWeil_positionArchKernel_eq` |
| `(3)`, `(4)` the position torque as a lag correlation | `suzukiLagCrossCorrelation`, `suzukiPrimeCommutatorAtom_eq_lagCrossCorrelation`, `suzukiLagCrossCorrelation_cosh_sinh` |
| `(5)` the visible prime layer is the Mangoldt tent sum | `suzukiFiniteWeilPrimeTorque_cosh_sinh`, `suzukiFreePrimePositionTorque_eq` |
| `(6)` exact principal-value/Gamma cancellation | `suzukiFreeUnreducedArchPositionTorque_eq` |
| `(7)`, `(8)`, `(9)`, `(10)` the exact source decomposition | `suzukiFreePositionTorque`, `suzukiFreePositionTorque_eq`, `suzukiFreeArchPositionTorque`, `suzukiTentCoeff`, `suzukiFreePrimePositionTorque_eq_tsum` |
| `(11)`, `(12)` the archimedean closed form | `suzukiFreeArchPositionTorque_closedForm`, `integral_tent_mul_exp_interval` |
| `(13)` the universal tent transform | `integral_suzukiPositionTent_mul_exp`, `integral_suzukiTentTerm_mul_exp` |
| `(14)` the complete torque transform | `integral_suzukiFreePositionTorque_mul_exp`, `integral_suzukiFreeArchPositionTorque_mul_exp`, `integral_suzukiFreePrimePositionTorque_mul_exp` |
| `(15)`, `(16)` the completed Xi curvature continuation | `suzukiPositionTorqueLaplaceContinuation`, `suzukiPositionTorqueLaplaceContinuation_eq_eulerSource`, `integral_suzukiFreePositionTorque_mul_exp_eq_continuation` |
| `(17)` the prime layer's exponential order | `suzukiFreePrimePositionTorque_le`, `continuous_suzukiFreePrimePositionTorque` |
| `(18)` the archimedean layer's exponential order | `abs_suzukiFreeArchPositionTorque_le`, `continuous_suzukiFreeArchPositionTorque` |
| absolute convergence of the prime tent series | `summable_suzukiTentCoeff_mul_exp`, `tsum_suzukiTentCoeff_mul_exp`, `integrableOn_suzukiFreePositionTorque_mul_exp` |
| the Landau lemma (Taylor–Tonelli form) | `laplaceMass_ne_top_of_moments`, `hasDerivAt_laplaceMomentReal`, `iteratedDeriv_ofReal_comp`, `false_of_analyticAt_abscissa` |
| the convergence abscissa exists | `exists_isAbscissa`, `exists_isAbscissa_tail` |
| the transform of the one-sign tail | `tailCarrier`, `tailMeasure`, `laplaceReal_tailMeasure_eq`, `tailTransform`, `tailTransform_ofReal` |
| the head is entire | `headLaplace`, `differentiable_headLaplace`, `analyticAt_headLaplace` |
| `ξ` has no real zero, so the continuation is analytic at every nonzero real point | `xi_ne_zero_of_real`, `xi_ne_zero_of_ofReal`, `analyticAt_suzukiPositionTorqueLaplaceContinuation_ofReal` |
| `ξ` does not vanish right of `Re s = 1`, so the far curvature is regular at `ρ+2` | `xi_ne_zero_of_one_lt_re` |
| the double pole at `p = ρ + 1/2` | `meromorphicOrderAt_deriv_logDeriv_xi_eq_neg_two`, `meromorphicOrderAt_continuation_eq_neg_two`, `exists_xi_zero_openStrip`, `exists_continuation_pole` |
| a convex domain minus a countable set stays connected (identity theorem on the divisor complement) | `isPathConnected_diff_of_countable_of_convex`, `isPreconnected_diff_of_countable_of_convex_complex`, `xi_zeroSet_countable`, `countable_shifted_xi_zeroSet` |
| no profile with a completed double pole can keep one sign | `no_oneSign_tail` |
| `(19)` the cofinal two-sided recurrence theorem | `not_eventually_nonneg_suzukiFreePositionTorque`, `not_eventually_nonpos_suzukiFreePositionTorque`, `exists_suzukiFreePositionTorque_sign_change` |
| `(20)` the prime torque crosses its archimedean baseline cofinally | `exists_suzukiFreePrimePositionTorque_cross_baseline` |
| `(P1)`–`(P4)` the source-domain resolvent promotion | `suzukiShiftedResolventScale`, `suzukiShiftedResolventScale_firstOrder_on_range`, `suzukiShiftedResolventScale_positionTorque_limit` |

## Notes

**How `(19)` is actually proved in Lean.**  The paper argument cuts the torque past its last sign
change and applies Landau to the resulting nonnegative tail.  Two things have to be added to make
that unconditional in Lean.

1. *The abscissa has to exist.*  A nonnegative tail may converge on the whole line, in which case
   there is no abscissa and Landau says nothing.  The formalization therefore thickens the tail by
   the reference density `e^{u/4}` (`tailCarrier`): the sum still converges right of `3/2` by
   `(17)`–`(18)`, and it certainly diverges left of `1/4`, so `exists_isAbscissa_tail` pins an
   abscissa `c ∈ [1/4, 3/2]`.  The reference contributes the single extra pole `1/(s−1/4)` to the
   transform, which is why `1/4` is the one real point the argument cannot exclude.

2. *Landau needs the identity down to the abscissa, not just right of `3/2`.*  `(16)` is proved for
   `σ > 3/2` only.  Both sides are real-analytic on the connected interval `(c, ∞)` — the transform
   because `complexLaplace` is holomorphic right of the abscissa (`hasDerivAt_complexLaplace`), the
   continuation because `ξ` has no real zero — so the real identity theorem on an interval extends
   the agreement from `(3/2, ∞)` to all of `(c, ∞)`.  Landau then forces `c = 1/4`.

   With `c = 1/4` the tail transform is holomorphic on the whole half-plane `Re s > 1/4`, and the
   complex identity theorem on `{Re s > 1/4} ∖ {ξ(s−1/2) = 0}` — preconnected by
   `isPreconnected_diff_of_countable_of_convex_complex`, which is the domain-relative form of
   mathlib's "the complement of a countable set is path connected" — carries that holomorphy onto
   the continuation at `p = ρ + 1/2`.  That contradicts
   `meromorphicOrderAt_continuation_eq_neg_two`.

**The constants of `(17)`–`(18)`.**  The card states `|A(L)| ≤ L³e^{3L/2}`; the Lean statement is
`|A(L)| ≤ 22 L³ e^{3L/2}`, and `(17)` is proved with the card's own `1/2`.  The card says the
constants are inessential — they are used only to place the convergence abscissa at most `3/2`,
which the constant `22` does equally well.

**What the card leaves outside stage 3.**  The card's own `2 → 3` gate names exactly one open item,
the cofinal sign theorem, which is now closed.  Construction of Suzuki's concrete restricted-Weil
operator, and the Fourier-multiplier proof that `cosh`/`sinh` lie in its domain, are listed by the
card under the `3 → 4` gate ("standalone operator theorem"); the Lean promotion theorems are stated
in the bounded-resolvent coordinate `B`, exactly as the card describes, so no unbounded operator is
postulated.  The joint transition-scale classification is explicitly the card's live open problem
and is not a claim of this card.

All listed declarations audit to `[propext, Classical.choice, Quot.sound]`.
