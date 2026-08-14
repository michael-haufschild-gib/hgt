# Route U prime–Gamma source disintegration formalized (2026-08-14)

Formal module:
- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaSourceDisintegration.lean`
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`
- Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-u-cofinal-filtered-prime-gamma-source-disintegration.md`

New closed Lean surface:
- literal completed Gamma–polar–von-Mangoldt balance = `π * xiPolynomialGaussianHeatTraceReal`;
- positive-time filtered source kernel = filtered Xi Gamma kernel;
- filtered source capital = `π * (2d)! * xiShiftedReciprocalHankelQuadratic`;
- negative capital forces an actual positive-time completed-source inversion;
- for positive shift the inversion lies beyond completed aperture;
- hard-edge reciprocal reversal exactly cancels all degree powers, leaving the degree-free Cauchy density;
- explicit finite packet specialization;
- `¬ RiemannHypothesis ↔ XiShiftedHardEdgeCofinalPrimeGammaInversionPhase`;
- premise-free dichotomy `RiemannHypothesis ∨ XiShiftedHardEdgeCofinalPrimeGammaInversionPhase`.

Verification:
- Checked-in source compiled with `lake env lean` in isolated scratch Lake/olean overlay.
- Separate scratch audit typechecked public theorem surfaces and `#print axioms`.
- Axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `#eval`, or `#reduce`.
- No project/module/full `lake build` run. User explicitly requires scratch Lean only, then umbrella wiring.

Scientific result:
Divisor Hankel negativity, heat polynomial growth, and Cauchy hard-edge compactness are one positive source disintegration. Reciprocal reversal is exact gauge cancelling admission-degree powers. False RH is now equivalent to cofinal super-aperture literal prime–Gamma source inversions from one fixed carrier.

True open core:
Prove unconditionally that one fixed polynomial–Gaussian carrier cannot sustain those cofinal super-aperture source inversions, using the degree-free Cauchy density and literal Gamma–polar–von-Mangoldt incidence. Generic scalar tail estimates/fixedness alone are insufficient or RH-equivalent.

Related prior memories:
- `mem:route_u/cofinal_linear_finite_hankel_dimension_formalized_2026_08_13`
- `mem:route_u/parabolic_degree_horizon_formalized_2026_08_13`
- `mem:route_u/reciprocal_clearing_scratch_audited_2026_08_14`