# Integral Fitting charge of the symmetric Euler-Maclaurin hole

- **ID:** sem-integral-fitting-charge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `formal/GaloisForLFunctions/RHTower/SEMFittingCharge.lean`

## Statement

Every actual `SEMSplitData ρ r₀ R N zs u` canonically determines an attached algebraic
non-split unipotent defect model `semHoleDefectZ`.  This is not yet an identification with a defect
produced by the analytic gluing construction.  For every jet depth `m ≥ 1` and modulus `n`,

`integralJetCharge m n (Fitting(semHoleDefectZ)) = zs.length mod n`.

Since `semSplitData_count_eq` identifies `zs.length` with
`(analyticOrderAt xi ρ).toNat`, this is also the ξ-order modulo `n`.

Consequences:

1. `RHLadder k` is equivalent to vanishing of this concrete integral Fitting charge modulo
   `2^k` for every symmetric-EM split at every hypothetical right-half zero.
2. RH is equivalent to simultaneous vanishing of all these charges.
3. Failure of a rung, and failure of RH, are equivalent to the existence of an unconditional
   finite symmetric-EM split carrying a nonzero integral Fitting charge.
4. If the integral charge is nonzero, it cannot factor through any additive charge on the
   rational jet algebra after base change.  Every rational additive finite charge kills the
   base-changed constant jet.
5. The attached defect is rigid across every annulus, truncation, and split representative at a
   fixed centre, and is exactly the model labelled by the finite analytic order of the ξ-germ.
6. Adding it to the standard presentation changes the determinant to
   `X^m + C(zs.length)`; for `m ≥ 1`, preservation of divisibility by `X^m` is equivalent to
   `zs.length = 0`.

The capstones are `integralJetCharge_semHoleDefectZ_eq_xiOrder`,
`rhLadder_iff_semHoleFittingCharge_zero`,
`riemannHypothesis_iff_all_semHoleFittingCharges_zero`, and
`not_riemannHypothesis_iff_exists_semHoleFittingCharge_ne_zero`.

## Proof

The integral presentation is the sheared matrix

`standardPresZ m = [[X^m, 1], [0, 1]]`.

For the defect parameter `t = -zs.length`, its adjugate/Fitting trace is `-C t`, hence
the Fitting class is the constant jet `C(zs.length)`.  Constant-coefficient reduction
`ℤ[X]/(X^m) → ZMod n` therefore returns exactly `zs.length mod n`.  The existing
unconditional annulus theorem supplies a split at every strip point, and its count theorem
identifies that length with the central ξ-order.  The ladder and RH equivalences then follow
from the existing dyadic divisibility characterizations.

For the base-change barrier, the integral class becomes the rational constant jet.  Composing
any additive rational-jet charge with the rational constant-jet line gives an additive map
`ℚ → ZMod n`, which is zero because the source is divisible and the target has bounded
exponent.  Thus a nonzero integral charge cannot be recovered after additive scalar extension.

## Dual gate

- **NOVEL:** the integral Fitting/deck channel and the symmetric Euler-Maclaurin annulus supply
  were previously separate theorem islands.  The new result attaches an integral algebraic seam
  model to the actual finite member and proves that the model reads the exact ξ multiplicity at
  every modulus.
- **SIGNIFICANT:** the all-rung obstruction is now a concrete finite-member boundary charge,
  not an abstract hole-count premise.  It also eliminates analytic additive base change as a
  possible annihilation mechanism.  Any successful unconditional proof must use a non-additive
  determinant/valuation/monodromy boundary, or retain integral arithmetic before scalar extension.

## Remaining open core

`[OPEN CORE]` First construct an actual arithmetic/analytic defect and prove that its
presentation-invariant integral boundary is the attached `semHoleDefectZ` model.  Then prove that
this actual boundary is annihilated at every dyadic level by a mechanism not already equivalent to
divisor multiplicity.  The theorem cannot be an additive functional after extension to `ℚ` or
`ℂ`; that channel is now formally ruled out.  A non-additive localization boundary or an integral
pre-extension conservation law is required.

## Verification

- Focused compilation passes.
- Capstone axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
