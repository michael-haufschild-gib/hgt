# Hawking generic coupling, local winding, and selection no-go (2026-08-23)

Mission: source-faithful actual Davies–Fulling moving-mirror scattering/KMS; canonical Cayley completion kept distinct from actual full mirror.

## New formal endpoints

1. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorGenericCouplingMixingEndpoint.lean`
   - Builds entire complex-coupling extension `thetaCuspHawkingEikonalCouplingEntire` from bounded positive theta source using four Jordan components of the complex density.
   - `thetaCuspHawkingEikonalCouplingEntire_ofReal`: restriction is exact real Davies–Fulling eikonal response.
   - `thetaCuspHawkingFullMirrorDarkCouplings_countable`: fixed positive-frequency sector's real dark couplings are countable.
   - `exists_arbitrarily_weak_common_thetaCuspHawkingFullMirror_mix`: for any countable nonempty family, one arbitrarily weak nonzero physical coupling activates every sector simultaneously.
   - Status: unconditional source-faithful survivor, not RH producer.

2. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorCouplingWindingEndpoint.lean`
   - `analyticOrderAt_thetaCuspHawkingEikonalCouplingEntire_zero`: complex-coupling zero order equals `thetaCuspHawkingFullMirrorSectorCouplingOrder`.
   - `exists_thetaCuspHawkingEikonalCouplingWinding_eq_order`: sufficiently local complex-coupling phase winding of exact eikonal response equals least nonzero coupling order.
   - `riemannHypothesis_iff_thetaCuspHawkingFullMirrorUnitCouplingWinding`: RH iff every noncentral tilted sector has unit local coupling-plane scattering index.
   - Status: [BRIDGE] [NOVELTY UNVERIFIED], source-faithful Birman–Krein-type coupling index; still equivalence/observer, not producer.

3. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingUnitWindingSelectionNoGo.lean`
   - Delayed Cayley family with numerator λ^m and load λ^(2m)/4.
   - Exact two-port Hermitian conservation, exact Hawking KMS detailed balance, strict mixing for every λ≠0, local winding m.
   - `lossless_KMS_every_nonzero_mix_not_force_unitCouplingWinding`: explicit m=2 countermodel.
   - Status: [FALSIFIED] losslessness + KMS + full nonzero-coupling mixing cannot select RH-bearing unit winding.

Support edit: public theorem `thetaCuspHawkingFullMirrorCouplingJetIntegral_eq_integral` and public `hasDerivAt_thetaCuspHawkingEikonalFourier_all` in `ThetaCuspHawkingFullMirrorValueMixingEndpoint.lean`.

All modules imported by `formal/GaloisForLFunctions/RHTower.lean`; endpoints report updated. Each module compiles. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Formal lint is blocked by unrelated pre-existing umbrella error: `GaloisForLFunctions.HTGeometry.AntiInvariantEvaluationMinor` unreachable from `GaloisForLFunctions.HTGeometry`.

## Literature/corpus verdict

- Obadia–Parentani and Ritus support source-faithful moving-mirror Bogoliubov/Fourier-current interpretation.
- Azamov resonance-index work supports argument principle in complex coupling and tangency order as scattering invariant.
- Higher-order FGR literature confirms delayed onset is a normal selection-rule phenomenon.
- KMS/Davies detailed balance supplies positivity and thermal ratios, not primitivity or first-order brightness.

## Remaining open core

Need theta-source-specific mechanism forbidding tangential coupling contact/order >1. Generic KMS, unitarity, canonical Cayley completion, and even mixing at every nonzero coupling are now formally insufficient. Candidate additional laws must use source coefficients/locality/minimality; avoid repackaging no-order-jump itself. Full actual mirror ≠ scalar canonical Cayley (prior parity no-go).