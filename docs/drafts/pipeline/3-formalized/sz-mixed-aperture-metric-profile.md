# SZ: actual mixed-aperture metric source profile

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); all four public declarations audited
- **Route:** SZ
- **Target:** retained metric response in the exact cross-aperture Riesz law.

## Source mechanism

Write c_a for the prescribed shift, P_a(s) for the literal whole-line
exponential source, F_a(s) for its actual completed covariance response,
and K_ab(s) for the existing metric-shift correction, a <= b.
Covariance self-adjointness and exact zero extension give

    <P_b(t), K_ab(s)> = (c_a-c_b)<F_b(t),F_a(s)>.

The left pairing is taken in the larger interval, with the literal
exponential interval source. This moves covariance off the unknown
extended response without assuming any regularity or source budget for it.
For s,t in {1,-1}, existing source-uniform profiles imply uniformly

    ||F_a(s)-P_a(s)/c_a|| -> 0,  ||P_a(s)/c_a|| <= 2.

Thus the full complex mixed Gram error tends to zero jointly as both
apertures grow. Since c_a,c_b <= C exp(b) when a<=b, multiplication by
exp(-b)*(c_a-c_b) preserves this limit, even for unbounded aperture gaps.
The proposed capstone is the actual complex metric source profile

    exp(-b) * |<P_b(t),K_ab(s)>
       -(c_a-c_b)/(c_a*c_b)<P_b(t),P_a(s)>| -> 0

uniformly for b>=a and both literal V2 signs. No parity, pole, prime,
Gamma or cross term is discarded. This resolves a mixed-response datum,
not the full shell Wronskian or shift removal. Prescribed-shift Xi
identification is already disproved in the corpus and is not revived.

## Novelty and failed attempts

Direct signed recovery from the prime-moment negative valleys remains
unproved: the chronological identity bounds work from below, whereas
barrier recovery needs an upper bound. Factorial/Selberg formulas retain
signed terminal errors. Source-only Schur estimates retain exponential
scale. The proposed common source profile was found already proved in
SuzukiFiniteSourceProfile; no duplicate theorem is being added.

Current searches are partial and mostly source-only/pending compiler
metadata. Exact corpus sources and targeted Lean checks determine
applicability; no absence claim is inferred from search ranking.

## Remaining hard problems

Signed full shell/metric cancellation near the admissible spectral floor,
canonical-head joint Gamma--prime--polar sign, and the eventual actual
prime-moment primitive barrier. No RH proof or falsification follows from
this prescribed-shift metric profile alone.

## Scale audit

The arbitrary-gap result uses exp(-b). It does not supply the same error
at exp(-a) for arbitrary gaps. For each fixed finite L and 0<=b-a<=L,
exp(-a)=exp(b-a)*exp(-b) transfers the error uniformly to the original
smaller-aperture scale. Both statements are to be exported, preserving
the precise domain of uniformity. A full near-floor source profile is
not supplied by this argument.

## Proof audit checkpoint

Scratch95206 passed all three initial public theorems without diagnostics.
Earlier32088/11789 failures were coercion-sensitive rewrites, repaired
by an explicit covariance symmetry equality and exact zero-extension
inner-product transport. The mathematical statement was unchanged.
Bounded-gap smaller-scale corollary is under sequential audit76241.

Search1223282 retrieves the actual metricShiftCorrection definition,
its Riesz identity, physical covariance representation and full shell
law. Candidate/source-argument sections inspected; no proof ideas or
ingredient sets. Coverage is pending/partial, so applicability rests on
current source reads and Lean. Earlier searches1223262 and1223273 were
partial with complete inventory snapshots but mostly pending/stale
compiler metadata; their suggested Neumann-boundary and Weil-polarization
ingredients did not prove the required sign or mixed estimate.

Scratch76241 passed the bounded-gap theorem without diagnostics. The
production version reduces that corollary to one exponential comparison
and drops the unneeded MetricCurvature import in favor of the exact
RieszTransport dependency. Final leaf audit12976 is running.

This closes a source-paired mixed covariance obligation at the actual V2
parameter1. It does not prove the full vector approximation of covariance
on an extended unknown response, nor the matched parameter1/2 signed
energy determinant, nor a near-floor or unshifted assertion. Further
prescribed-shift profile variants are not the next RH-bearing target.

Final production audit12976 passed without diagnostics:

    lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiMixedApertureMetricProfile.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Suzuki/SuzukiMixedApertureMetricProfile.olean

New leaf is wired once after SuzukiTaV2PrescribedEnergySource. All four
public declaration axiom queries55330 and global structural lint23382
are running. No umbrella or full build was used. Target whitespace check
passed.

Global lint23382 exited1 with 13 unrelated unreachable-module errors;
no prohibited proof declaration or new-leaf error was reported.

```text
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMApertureChainProfile
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMApertureTranslationChains
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMExponentialRampPrimeMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMExponentialRampSourceDissipation
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMExponentialRampTerminalEntropy
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMRetainedChainKernelLower
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MertensProductDiamondPintz
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.RoutePNativeMixedLaplaceAdmission
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
```

## Final closure

All four public axiom queries55330 passed: only propext, Classical.choice,
Quot.sound. Exact reciprocity and bounded-gap root types were printed
from the production olean. Final leaf12976 passed without diagnostics;
unique umbrella import verified. Lint23382 has the13 unrelated errors
listed above. No full/umbrella build, computation experiment, heartbeat
increase, added axiom, subagent or commit.

Exported roots in SuzukiMixedApertureMetricProfile:

- suzukiTaRiesz_metricShiftCorrection_source_pairing
- suzukiTaV2_mixed_response_profile
- suzukiTaV2_mixed_metric_source_profile
- suzukiTaV2_mixed_metric_source_profile_bounded_gap

This is a completed actual mixed metric profile theorem, not an RH proof
or falsification. Goal remains active. The next proof attempt must address
signed shell/metric cancellation at the spectral floor or the canonical
head/prime-primitive sign, not another prescribed-shift profile variant.

All9 exact owned scratch/search/lint files removed after every owned
process terminated. Audited production olean retained. Cross-session
memory: `rhtower/sz-mixed-aperture-metric-profile-2026-10-04`.
