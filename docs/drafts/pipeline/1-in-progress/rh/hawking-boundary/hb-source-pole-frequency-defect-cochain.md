# HB source-pole frequency-defect cochain

- **ID:** hb-source-pole-frequency-defect-cochain
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md · HB literal cyclic Peierls realization
- **Statement:** The literal off-frequency Einstein defect factors exactly by `w - 2*physicalRate`; its quotient has a literal frozen-metric difference realization. The remaining task is to transport that metric/source cochain, together with the explicit wave cochain, through the causal noncompact boundary comparison to `mixedField`.

## Goal

Close or kill the sole remaining HB/FZZ-P/PW-B/RBH producer edge:

`source pole residue + retarded/advanced continuation -> defect cochain + explicit wave cochain -> mixedField action boundary -> cyclic Peierls current extinction -> RH`.

The candidate is significant only if it proves that literal residue transport reaches the full `mixedField` boundary current, or proves a nonzero mismatch and kills this final distributional/action survivor.

## Gates

- [x] 0 → 1 in-progress: source-pure exact factorization identified from `frequencyDefectTensor`.
- [x] Exact cochain factorization formalized: `ThetaCuspHawkingBMStreamFrequencyDefectCochain.frequencyDefectTensor_factor`; source check passed and the RHTower umbrella is wired. The proof uses two generic scalar factor identities and a generic four-slot matrix lemma, so forced profiles and current remain literal opaque inputs.
- [x] Local metric realization formalized: `frozenMixedDifferenceJet_cosmological` constructs a complete frozen metric-two-jet difference whose cosmological Einstein residual is exactly `(w-2*s) * frequencyDefectCochain`. This removes any local residual-to-metric inverse premise.
- [ ] 1 → 2 fully-proven: prove or refute the cochain's action pairing with the explicit wave cochain and `mixedField`.
- [ ] 2 → 3 formalized: add the resulting boundary theorem to Lean and audit its axioms.
- [ ] 3 → 4 publication-ready: isolate pole-residue transport and its four-route consequence.

## Approach

Put `v = 2*physicalRate q branch`, `f = r^2-1`, and `D = w^2-v^2`.
Every component in `frequencyDefectTensor` contains either `D` or `w-v`; since
`D=(w-v)(w+v)`, define the literal quotient tensor by replacing

`D` with `w+v` in the temporal block and by factoring the displayed `w-v` out of both radial terms.

Then prove exactly

`frequencyDefectTensor q branch w r B z = (w-v) • frequencyDefectCochain q branch w r B z`.

Writing `P,P1,C` for the displayed forced-stream value, first derivative, and literal current,
the quotient's two nonzero blocks are

`T = f/(2r²)*(w+v)*(r²/f*P1 - 2r/f²*P)`,

`R = -C/(r²*f) + w/(2r²*f)*(w+v)*r²/f*P`.

The factorization is an exact ring identity. At the physical exterior, where the existing source
proof supplies `r≠0` and `f=r²-1≠0`, its on-shell value is exactly

`T(v) = v*P1 - 2v/(r*f)*P`,

`R(v) = -C/(r²*f) + v²/f²*P`.

These identities were Lean-scratch checked with only standard axioms. The denominator facts are
essential; no cancellation is valid before the literal exterior geometry is introduced.

At `w=v`, its radial quotient contains

`- current s r B (fullSquareCovector ...) (fullGradientCovector ...) / (r^2*(r^2-1))`,

the same literal current retained by `mixedField`'s radial action boundary. The unit source-pole residue of F350 therefore selects this quotient rather than a pole-free field. `frozenMixedDifferenceJet_cosmological` now realizes the *scaled* cochain as an actual complete metric two-jet, by subtracting the frozen pencils at `w` and `v`; no local inverse is left to assume. The decisive next theorem is a noncompact causal transgression: after adding the explicit lift/principal wave cochain, identify its two-leg boundary with the retained `actionSymplectic` boundary of `mixedField`.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending. A nonzero action-boundary mismatch at this cochain kills the only remaining pole-cleared distributional HB realization.
- **Strongest positive survivor:** the exact quotient tensor, if the mismatch is nonzero; otherwise the `mixedField` boundary law.
- **New insight:** F350's unit residue is not an obstacle to remove: it canonically exposes the defect cochain whose radial component already carries the physical source current.
- **Status:** exact quotient/factorization and its complete local frozen-metric difference realization are formalized in `ThetaCuspHawkingBMStreamFrequencyDefectCochain`; direct source checks passed on 2026-09-16. `frozen_stream_cosmological_source_factor` and `frozenMixedDifferenceJet_cosmological` compose it with the full Einstein-source identity. Corpus search confirms that the existing lift weak-wave theorem is compact-test only; no causal/noncompact quotient-to-`mixedField` action-boundary theorem exists.

## Frozen bridge B1 — retarded compact weak equation

**Proof chain it closes:**

`source pole → explicit lift + reduced source → retarded/future causal difference → [B1] compact-test homogeneous difference → cutoff boundary transgression → mixedField two-leg action → Peierls extinction → RH`.

**Statement.** On every compact smooth test supported in the open physical wedge `0 < p < r` (equivalently `x=(p-r)/2<0`), `originalPotential` obeys the same full weak-wave identity as `correctedFutureField`. Their literal difference is then weakly homogeneous on that test class.

**Corpus evidence.** `originalPotential_wave` gives the complete pointwise forced wave equation, including fixed onset and gradient source; `originalPotential_smooth` gives interior C-infinity. `complete_original_weak_wave` gives the full compact-test weak equation for `correctedFutureField`; `original_cap_weak_wave` is homogeneous; `original_future_weak_wave` gives the reduced response. `SmoothCylinderIntegral` supplies radial/angular compact integration-by-parts primitives.

**Falsifier / route consequence.** A nonzero compact physical interior defect refutes B1 and kills this literal realization before any horizon limit. If B1 holds, the only remaining calculation is the noncompact cutoff-face limit; a surviving nonzero face kills the route, while zero identifies the required two-leg boundary.

**Current obstruction.** No corpus theorem converts `originalPotential_wave` into this four-variable weak identity. The needed source-only imports lack object files; no broad Lake build will be run. This is a build-environment constraint, not a relaxation of B1.

**Paper status.** B1 is dependency-closed on paper in
`../2-fully-proven/hb-retarded-compact-weak-realization.md`: the literal
pointwise equation is transposed on a compact box strictly inside `0<p<r`,
with the exact `exp(-k)` hyperbolic angular adjoint.  The new Lean leaf
`HTGeometry.ComplexWaveGreenIdentity` source-checks the complex one- and
two-coordinate compact Green primitives.  The remaining Lean work is the
explicit target-coordinate/angular assembly, not a new mathematical premise.

## Frozen bridge B2a — finite two-leg contact transgression

**Proof chain it closes:**

`source pole → explicit wave cochain → B1 homogeneous causal difference →
[B2a] finite current/source two-leg identity → noncompact causal limit →
mixedField boundary → Peierls extinction → RH`.

`physicalProjectedModeAction_transport` has the exact form
`J_o(t)-J_o(s)=(-c I_o-(K_o(t)-K_o(s)))N`, where `K_o` is the literal source
contact.  Therefore `J_o+K_oN` transports by `-cI_oN`, and subtracting the two
outer legs gives an exactly skew finite two-leg functional.  This dependency-
closed algebra is recorded in
`../2-fully-proven/hb-literal-finite-cutoff-two-leg-current.md`.

**Remaining content.** B2a does not label the two outer modes retarded and
advanced, take a noncompact causal limit, or compare the result to the
source-pole cochain and `mixedField`.  A nonzero residual in that comparison
kills the literal distributional/action realization.

## Cutoff-face reduction

The literal physical lift current has horizon spectral factor
`(2s+3)((s+1)(s+2)-2)((s+1)(s+2)-6)`.  It is now Lean-proved nonzero at every
`s=physicalRate q branch` in
`ThetaCuspHawkingBMPhysicalRateNonreal`.  Hence the cutoff-face test has no
spectral-root escape: after unit source amplitude, only the actual angular
pairing/contact or a cross-channel term can cancel it.  The next conjecture
must prove that exact cancellation in the `mixedField` action, or show its
residual is nonzero and retire this realization.

## Log

- 2026-09-16 — candidate created after on-shell Hilbert no-go left only an action/distributional survivor.
- 2026-09-16 — formalized literal factorization and the composed full frozen-Einstein source factorization; remaining action comparison is now a sharply stated sole edge.
- 2026-09-16 — formalized the complete local metric realization by frozen-frequency difference. The remaining obstruction is no longer a local Einstein inverse: it is the noncompact causal action transgression of the explicit lift plus residual cochain.
- 2026-09-16 — froze B1 after corpus audit: the retarded/future difference becomes a literal homogeneous causal field only after a compact physical strong-to-weak transgression. Its interior defect or eventual cutoff face is a decisive falsifier.
