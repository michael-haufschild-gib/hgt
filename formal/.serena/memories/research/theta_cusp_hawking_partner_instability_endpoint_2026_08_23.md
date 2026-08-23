# Theta-cusp Hawking reflected partner-instability endpoint (2026-08-23)

## Result
Added `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPartnerInstabilityEndpoint.lean`, imported by `formal/GaloisForLFunctions/RHTower.lean`.

For every nonkinematic dark Born frequency `d`:
- exact compact theta Green eigenfrequency `mu_d = -d⁻¹`;
- exact eigenline orbit `exp(-i t mu_d) • thetaCuspHawkingKreinMode d`;
- norm law `norm = exp(t * Im(mu_d)) * initial norm`;
- growth rate `Im(mu_d) = Im(d)/normSq(d)`;
- flux weld `KreinFlux = 2 * mass * normSq(d) * energy * growthRate`;
- reflected dark frequency `-d` has opposite growth rate;
- every off-line `d` gives a strictly growing member of the reflected pair;
- `RiemannHypothesis ↔ ThetaCuspHawkingSourcePartnerNoAmplification`.

Key declarations:
- `thetaCuspHawkingPartnerGreenFrequency`
- `thetaCuspHawkingPartnerGrowthRate_eq`
- `thetaCuspHawkingReflectedDarkFrequency`
- `thetaKernelOperator_thetaCuspHawkingPartnerGreenOrbit`
- `norm_thetaCuspHawkingPartnerGreenOrbit`
- `thetaCuspHawkingKreinFlux_eq_growthRate`
- `thetaCuspHawking_offLine_has_growing_reflected_partner`
- `riemannHypothesis_iff_thetaCuspHawkingSourcePartnerNoAmplification`

## Verification
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingPartnerInstabilityEndpoint` passed.
- `#print axioms` on five key theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- New Hawking files contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Full formal lint remains red only on six unrelated pre-existing umbrella reachability failures (`PairQubit...` and `GaussianAffinePauli...` families).

## Hostile audit / killed routes
- Energy conservation / Krein two-port balance permits reciprocal squeezing and does not force neutrality.
- First-order Bogoliubov anomalous identity is automatic: Born kernel is symmetric in partner frequencies.
- FDT/KMS constrains noise/dissipation spectra but does not prove radiation-reaction balance; dynamical mirror literature has runaway branches.
- Self-adjoint Hawking/SUSY doubling is compatible with every complex shift through conjugate sewing.
- Scalar Polya-frequency/total positivity is already equivalent to RH.
- Independent Born/Witten channel particle numbers are positive/incoherent; Xi darkness is coherent Fourier cancellation.

## Physical interpretation boundary
The new orbit is an exact source Green eigenline, not yet physical moving-mirror time evolution. Do not call it a Hawking QFT mode without proving generator matching.

## Open core
Construct from the Kumar–Reyes–Wintergerst anomalous dynamical-mirror/backreaction equation (or another source-derived dynamical law) a fixed physical generator/intertwiner whose restriction to a dark channel equals the theta compact Green eigenline. Then physical forward stability would close RH through the theorem above. Ordinary prescribed-trajectory Born coefficients do not establish this identification.

Related memories: `mem:research/theta_cusp_hawking_bogoliubov_born_endpoint_2026_08_23`, `mem:research/theta_cusp_hawking_born_partner_port_endpoint_2026_08_23`, `mem:research/theta_cusp_hawking_krein_flux_endpoint_2026_08_23`.