# HB: full canonical action cannot match the unit-source receiver

- **ID:** HB-DN-full-canonical-unit-source-matching
- **Stage:** 5-failed
- **Type:** FALSIFIED matching option; THEOREM (Lean)
- **Source:** [complete source reduction](../1-in-progress/hb-dn-source-moment-reduction.md)
- **Statement:** No copy-dependent returned vector makes the literal complementary unit-source probe match the original complete canonical QNM action, even only in its extinction locus.

## Exact scope

Let `A(q)=canonicalQNMValue q true true 1` and
`P_r(q)=hbXiPeierlsSourceProbeProfile r q`. Lean proves

```
not exists r : XiZeroCopy -> HBXiPeierlsCarrier, forall q, P_r(q)=A(q)
not exists r : XiZeroCopy -> HBXiPeierlsCarrier, forall q, (A(q)=0 iff P_r(q)=0).
```

The returned vector is unrestricted and may depend on the copy. Arbitrary
nonlinear carrier responses are consequently included. This excludes the
literal unit-source matching option. It does not exclude a changed
source-retaining receiver and does not prove or falsify RH.

## Proof

The source-derived identity for the complete original action is
`E(w)^2*(5*w+8)^2*A(q)=-mu*C(q)*G(w)` at `w=-1-rho/2`.
The temporal derivative holds the source rate fixed. The original metric,
logarithmic and twice-subtracted forcing terms and constants are retained.
`G` is entire of finite exponential type with
`G(-1)=27*pi^2*T(-2,-1)/4>0`, hence has only linearly many zeros.

On the critical line, `C(q)=0` requires a Xi zero at one of
`2-5*rho/2`, `1-rho/2`, `3*rho/2`. These injective affine maps have real
part `3/4`. The corpus density bound controls each image in its actual
multiplicity-weighted zero census. Their counts and the radial count
cannot cover the corpus's superlinear simple-critical census.
Thus an actual critical copy has `A(q)!=0`. Every `P_r` vanishes at that
copy because its literal complementary testing source is zero.

## No-go closure

- **Killing theorem:** `not_exists_hbXiPeierls_fullCanonicalExtinction_matching`.
- **Strongest positive survivor:** among simple critical Xi zeros up to height `N/3`, only `O(N)` can have zero complete canonical action. For every `eps>0`, their count is eventually at most `eps` times the actual simple-critical count. Nonvanishing therefore has relative density one in this census.
- **New insight:** a receiver matching the full physical action must retain critical-copy information erased by the literal unit source. The obstruction persists after every temporal, metric and forcing contribution has been combined.
- **Paper status:** complete derivation in the linked source reduction; the unused alternative expansion at `w=0` is not a dependency.
- **Lean status:** scratch check and isolated exact module audit passed; module wired. The final audit built two jobs in 98 seconds. Repository lint reports the unrelated unwired module `RHTower.DivisorCoreMellinResidueUniformMargin`; no error concerns these new modules.

## Lean certificate

[FullCanonicalMatchingNoGo](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFullCanonicalMatchingNoGo.lean):
`fundamentalCanonicalCriticalZeroFinset_card_linear`,
`fundamentalCanonicalCriticalZeroFinset_relative_density_zero`,
`exists_critical_canonicalQNMValue_ne_zero`,
`not_exists_hbXiPeierls_fullCanonicalQNM_matching`,
`not_exists_hbXiPeierls_fullCanonicalExtinction_matching`.

[CanonicalContourAttachment](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMCanonicalContourAttachment.lean)
proves the exact attachment to the complete original action.
