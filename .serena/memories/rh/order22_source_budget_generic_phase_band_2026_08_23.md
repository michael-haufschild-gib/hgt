# Order-22 source closure and generic opposite-phase propagation (2026-08-23)

Status: dependency-closed paper/Lean result; novelty remains [NOVELTY UNVERIFIED].

## Exact first-atom fourth-moment floor
Module: `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomFourthMomentSixtyFourthFloor.lean`
- `twoThousandNineHundredFiftyOne_div_oneMillion_lt_sum_firstAtomFourthLowerMass64`
- `sum_firstAtomFourthLowerMass64_le_thetaCuspAtomRawEvenMoment_two_one`
- `twoThousandNineHundredFiftyOne_div_oneMillion_lt_thetaCuspAtomRawEvenMoment_two_one`
Exact 56-cell rational kernel certificate through 7/8 proves raw fourth moment > 2951/10^6.

## Order-22 source budget
Module: `formal/GaloisForLFunctions/RHTower/XiCenteredOrderTwentyTwoSourceBudgetClosure.lean`
- theta normalized μ₂ > 2951/500000
- normalized prime-arch M₁ < 9/100000
- order-22 sector positivity with N=205, t=7/100
- residual annulus u ∈ (2365/13152, 1/4), v ∈ [2365/16, 411/2)
- fourth trace atom > 9/400000, hence source > 9/100000
- residual annulus empty
- all centered reciprocal-square 22nd powers have positive real part
- normalized prime-arch moment M₂₁ > 0

## Generic higher principle
Module: `formal/GaloisForLFunctions/RHTower/PrimeArchOppositePhasePurePowerPropagation.lean`
`re_pow_mul_pow_nonneg_of_opposite_phase_of_pow_pos_bounded`:
right half-plane + opposite imaginary signs + sector bounds
(121/10)|Im z|≤Re z and (363/10)|Im w|≤Re w,
0<Re(z^p), p≤38, r≤57 imply 0≤Re(z^p w^r).
This converts a pure-power sign into a full bounded Hausdorff row.

## Order-22 Hausdorff band
Module: `formal/GaloisForLFunctions/RHTower/PrimeArchOrderTwentyTwoHausdorffSourceBand.lean`
- row k=21 is nonnegative for every r≤57
- closed rectangle has cardinality 22*58=1276
- remaining tail `21 < k ∨ 57 < r` is equivalent to RH
- umbrella `formal/GaloisForLFunctions/RHTower.lean` imports all new modules

## Verification
Each module compiled with `lake env lean`; oleans built. `#print axioms` in /tmp reports only `propext`, `Classical.choice`, `Quot.sound`. Forbidden-declaration scan and targeted diff check passed. Global lint reaches new modules; failure is only unrelated dirty-tree unreachable modules.

## Next quantitative wall
Order 23 candidate sector N=217, t=17/250 leaves high endpoint 435/2. Current M₁ < 9/100000 is slightly too weak for fourth-trace exclusion. Candidate target M₁ < 1/12000. Investigate sharper exact endpoint curvature `2 + γ - log(4π)`, a stronger exact first-atom fourth-moment floor, or a different trace invariant. Do not assume this route is best; keep alternate invariants/cofinal mechanisms live.