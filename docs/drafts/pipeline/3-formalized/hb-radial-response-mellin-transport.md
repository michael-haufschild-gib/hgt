# HB: physical response periods from source moments and endpoint fluxes

- **ID:** HB-RRMT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessor:** [full scalar-tested cusp decomposition](hb-radial-response-cusp-pair.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source
→ physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Complete source and response

Let q be an actual Xi occurrence, rho its spectral point, Q the full theta
half-square, and A either constructed full angular response. Write alpha for
that branch's original parameter, and M(y) and S(y) for the width-one horizontal
means of A and Q. The source equation gives the closed mean identity

```
y² M''(y)-alpha M(y)=alpha S(y),       y>0.
```

The proof uses the actual smooth modular field. Its horizontal second derivative
integrates to zero by the original modular translation. Both the particular
cusp response and the native residual remain in M; S includes the complete
signed Fourier source. No equation, regularity or integrability premise is
supplied by the caller.

Above height three, M equals the predecessor's exact cusp formula. Its decaying
native coefficient and both infinite forcing moments remain part of the actual
endpoint data below.

## Original physical weights and nonresonance

The physical scalar test psi has principal part
`P(y)=Lambda(rho-1)y^(1-rho/2)`. The complete source principal half-square is
`Q0(y)=sum_i A_i y^e_i`, where `e=[2rho,1,2-2rho]`. Their product is exactly

```
P(y)Q0(y)=Lambda(rho-1) sum_i A_i y^v_i,
v=[1+3rho/2, 2-rho/2, 3-5rho/2].
```

These are angular height weights, not changed physical time frequencies. The
common Hawking clock is unchanged.

For each weight define `gap_i=alpha-v_i(v_i-1)`. The first branch's two roots
are `2rho-2` and `3-2rho`; the second branch's roots are `-2rho` and `1+2rho`.
Thus each gap is minus the product of the weight's differences from those roots.
Every such difference has nonzero rational coefficient of Im(rho). The literal
Xi occurrence's independently proved nonzero imaginary part therefore excludes
all twelve root collisions and proves all six gaps nonzero. No critical-line
condition is used.

## Exact finite-height transport

Use the actual full-response endpoint flux

```
J_i(y)=y^v_i M'(y)-v_i y^(v_i-1)M(y).
```

Differentiating by the genuine product rule and substituting the full mean
equation gives

```
J_i'(y)=y^(v_i-2)[alpha S(y)+gap_i M(y)].
```

All functions are continuous on every positive compact height interval. The
fundamental theorem of calculus gives, for any positive endpoints a,b,

```
integral_a^b y^(v_i-2)M(y)dy
 = [J_i(b)-J_i(a)-alpha integral_a^b y^(v_i-2)S(y)dy]/gap_i.
```

Both endpoint jets are retained. This evaluates the response moment through
the original complete source, rather than assigning a homogeneous solution or
setting a cusp coefficient to zero.

Let `T=(psi Q-chi P Q0)A` be the predecessor's complete admitted source/test
remainder, with the original cutoff chi. For a,b>3 the actual finite pairing is

```
integral_a^b [mean(psi Q A)-mean(T)]dy/y²
 = Lambda(rho-1) sum_i A_i
     [J_i(b)-J_i(a)-alpha integral_a^b y^(v_i-2)S(y)dy]/gap_i.
```

This follows from the proved full-test cusp decomposition, the three-term
physical product expansion, and the source-driven transport law. T remains
explicit and is independently L1 in the native quotient measure. The theorem
does not declare its period zero.

## What remains for extinction

The original radial source work combines two such response pairings with its
local Q² term and two angular-current divergences. Infinite-height finite parts
and those currents' boundary contributions must still be evaluated together.
The full independent SS/SV/VV assembly, solved ++/+- corrections, metric weights,
and horizon, characteristic and source-contact faces must then enter the same
physical left-QNM action identity. This leaf proves none of those remaining
cancellations and does not prove extinction or RH.

The tested variational shortcut does not remove this burden. The existing
`ThetaCuspHawkingCubicPeierlsPolarization` proves that cyclicity and Peierls
skewness kill the mixed self-pairing but retain the polarized ++/-- pairing.
Its common propagator, augmented pairing and boundary cyclicity are hypotheses
to identify physically, not consequences of source reconstruction alone.

## Search and Lean validation

Deep source/action and variational-method searches returned the physical mode
action, true Einstein variation symmetries and existing Peierls reductions.
They reported partial retrieval and did not supply the missing action sign.
Broad Mellin/tail retrieval found a weighted Hardy tail identity and source
primitive bounds; those generic results were not used to assume an infinite
limit. The finite transport instead follows directly from the actual source
equation and its verified averaging calculus.

Module:
[ThetaCuspHawkingBMQuarticResponseMellinTransport.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQuarticResponseMellinTransport.lean),
namespace `RHTower.D4BMQuarticResponseMellinTransport`.
Nine public theorems and five definitions are wired into the RHTower umbrella
once. `lake env lean /tmp/hb-response-mellin-transport.lean` passed without
diagnostics. Proofs use explicit scalar types, component integrability and
algebraic factorization; no heartbeat, recursion-depth or transparency override
was introduced. Final
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticResponseMellinTransport`
passed without warnings in 45 seconds against cached imports. The audited source
hash is `e25a2775f9bc18a97835d036108f3419c05678c821a5baade8f49ef31cd9861c`.
No dependency or umbrella build ran.

Index regeneration registered all fourteen public declarations. The final
`scripts/formal_tools.py lint --check-generated` reports eight other unreachable
worktree modules: `ThetaCuspHawkingBMHorizonModeOuterUniformBound`,
`ThetaCuspHawkingBMTemporalCurrentClearedDensity`,
`ThetaCuspHawkingBMTemporalCurrentClearedDensityBound`,
`ThetaCuspHawkingBMTemporalCurrentRadialCutoff`,
`ThetaCuspHawkingBMTemporalCurrentRadialLaurent`,
`ThetaCuspHawkingBMTemporalCurrentRadialPackage`, `JetCoefficientUniqueness`, and
`SecondEndpointMellinLaurentInterchange`. No error names this leaf; no generated
file was reported stale in this run. The exact source hash, single umbrella
import and public API rows were verified. All processes started for this leaf
have finished. Whole-tree lint is not green.
