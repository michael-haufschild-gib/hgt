# Route C2 zero-safe current multiplicity tomography

- **ID:** `route-c2-zero-safe-current-multiplicity-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / ROUTE-CLOSURE SURVIVOR
- **Scientific status:** `[BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:**
  `other/route-c2-zero-safe-current-multiplicity-tomography.md`
- **Statement:** Completed theta-cusp current has an exact zero-safe odd divisor factorization at
  every Xi zero, recovers multiplicity from transverse order, and has an exact planar leading cone
  with a higher coefficient vanishing at the divisor.

## Lean theorem surface

Module: `RHTower/ThetaCusp/ThetaCuspCenterMixedDivisorTomography.lean`.

- `hasDerivAt_normSq_XiC_transverse`: zero-safe squared-energy derivative.
- `thetaCuspCenterMixedFourierCurrent_eq_xiTransverseEnergyCurrent`: literal source-current
  identification throughout `|a|<1`.
- `xiTransverseEnergyCurrent_support_factorization`: exact odd transverse factorization.
- `xiSupportTransverseResidual_center_pos`: strictly positive terminal cofactor coefficient.
- `tendsto_xiTransverseEnergyCurrent_normalized_at_support`: exact `2m-1` multiplicity limit.
- `exists_xiTransverseEnergyCurrent_local_sign`: forced negative/positive sides.
- `xiTransverseEnergyCurrent_support_planar_factorization`: exact radial planar factorization.
- `xiTransverseEnergyCurrent_eq_planarLeadingCone_add_higher` and
  `xiSupportPlanarHigherResidual_center`: exact leading cone and vanishing higher coefficient.
- `exists_physical_thetaCuspCenterMixedFourierCurrent_sign_chamber`: physical C2 negative chamber
  forced by every hypothetical right-of-line zero.

All theorems are unconditional. No logarithmic derivative or nonvanishing premise is used at the
divisor.

## No-go closure

- **Exact killing theorem/mechanism:** C2 positivity phase threshold already equals actual Xi zero
  width; at zero width it is RH. Divisor tomography proves an off-line zero cannot be erased by
  completed shell cancellation.
- **Strongest positive survivor:** zero-safe current is an exact divisor transducer recovering
  side, location, and multiplicity.
- **New insight:** tangential motion cannot compensate the leading transverse sign: the planar
  leading cone is `2m|Q(alpha)|² x(x²+y²)^(m-1)`.
- **Status:** paper proof dependency-closed; direct `lake env lean` check and axiom audit pass;
  umbrella wired. Repository lint reaches this module but is currently blocked only by unrelated
  untracked `BVCoPoissonCompactSeedRigidity` and `DeningerEnergyIdentity` modules missing umbrella
  imports. Full build intentionally not run.

## Gates

- [x] 0 -> 1: source-fixed, hostile falsification and novelty audits complete
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean theorem, umbrella wiring, direct audit
- [ ] 3 -> 4: independent priority and expert review

## Log

- 2026-08-01 — exact theorem surface formalized; planar leading-cone claim promoted from prose to
  an equality with continuous higher coefficient vanishing at divisor.
