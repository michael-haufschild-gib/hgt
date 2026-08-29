# Theta C5 Riccati-charge monotonicity no-go

- **ID:** `C5-RB1-CHARGE-MONO-NOGO`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/drafts/pipeline/5-failed/theta-cusp-c5-riccati-charge-monotonicity.md`
- **Statement:** Strict increase from zero of the integrating-factor Riccati charge, together with
  global Riccati margin and local seam C5, does not force global C5; the same countermodel also
  satisfies the already formalized six-jet atom/likelihood architecture.

## Lean artifact

- Module:
  `GaloisForLFunctions.HilbertMetric.RiccatiChargeFifthRootNoGo`
- Main theorem:
  `HilbertMetric.sexticGaussianRiccatiChargeMonotonicity_does_not_force_globalC5`
- Supporting theorems:
  `HilbertMetric.hasDerivAt_sexticGaussianRiccatiCharge`,
  `HilbertMetric.deriv_sexticGaussianRiccatiCharge_pos`, and
  `HilbertMetric.strictMonoOn_sexticGaussianRiccatiCharge`
- Positive survivor:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_chargeEnvelope`

## RH-chain consequence

Retires every `C5-RB1` proof using only lower Riccati drift, charge positivity, or charge
monotonicity. Surviving significant premise is a theta-specific nonlocal upper envelope at negative
intrinsic minima. If proved, it closes modular-center C5 before still-open off-center rank-four,
higher-packet/no-escape, and CLG/TTF-or-Weil joins to RH.

## Verification

- `lake env lean GaloisForLFunctions/HilbertMetric/RiccatiChargeFifthRootNoGo.lean`
- targeted `lake build GaloisForLFunctions.HilbertMetric.RiccatiChargeFifthRootNoGo`
- `#print axioms` on main and supporting public theorems
- formal lint gate

No hypotheses, premises, added axioms, `sorry`, `admit`, `opaque`, `unsafe`, or computation.
