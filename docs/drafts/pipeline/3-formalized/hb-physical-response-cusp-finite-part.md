# HB: original-source restoration of physical response cusp periods

- **ID:** HB-QRCFP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessor:** [complete cusp-flux decay](hb-physical-cusp-flux-decay.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical
causal radial/left-QNM action → fixed common Hawking-clock extinction → RH.

## Exact source and its counterterms

Let M be either actual full angular response mean, alpha its original parameter,
and v one of the three physical test/source height weights from the preceding
Mellin transport. Let e_j,A_j be the original half-square principal exponents
and amplitudes, j=0,1,2. Put

```
d_j=v+e_j-1,
k_j=alpha A_j/[e_j(e_j-1)-alpha],
gap=alpha-v(v-1).
```

The actual particular cusp response is K(y)=sum_j k_j y^e_j. No response
coefficient is assigned by the new construction. The old particular-response
formula is exactly this three-power sum, with its original denominators.
Every d_j is nonzero: after the nine finite substitutions, each has a nonzero
rational coefficient of Im(rho). The occurrence's independently proved nonzero
imaginary part excludes zero. The original resolvent and physical gap theorems
supply all the other nonzero denominators used below.

Write S for the full theta half-square mean. Its literal decomposition is

```
S(y)=Q0(y)+(1/2)mean(squareRemainder(theta,y)).
```

This identity retains the complete complex signed source. Horizontal slice
continuity justifies the integral splitting. For r_-=root false and its original
flux source F_-, it follows that

```
alpha y^(v-2) S(y)
 = alpha y^(v-2) Q0(y)+y^(v-r_-) F_-(y).
```

The last density is absolutely integrable on every ray (a,infinity), a>3,
by the previously proved arbitrary-weight inverse-square source bound. Define
its integral as the complete source-tail moment, not a zero remainder.

The forced source antiderivative is

```
B_source(Y)=sum_j alpha A_j Y^d_j/d_j.
```

The genuine derivative rule and finite-height integration prove that its
increment is exactly the complete principal-source moment. Hence

```
alpha integral_a^Y y^(v-2)S(y)dy
 = B_source(Y)-B_source(a)+integral_a^Y y^(v-r_-)F_-(y)dy.
```

## Full-response restoration

Retain C_-=limitingCoefficient false and both actual roots r_-,r_+, with
r_-+r_+=1. The source-prescribed response subtraction is

```
B_response(Y)=sum_j k_j Y^d_j/d_j
              +C_- Y^(v-r_+)/(v-r_+).
```

The native exponent v-r_+ is nonzero because the original physical gap factors
as (r_--v)(v-r_+), and that gap is nonzero. In particular the native coefficient
has not been removed by claiming that its power decays in the whole strip.

Writing J_v(f)=y^v f'-v y^(v-1)f, the exact coefficient relation
`[e_j(e_j-1)-alpha] k_j=alpha A_j` proves

```
gap B_response+B_source=J_v(K)+J_v(native).
```

The Lean definition through the fluxes is verified to equal the explicit
power antiderivative above. This matters: no additional constant, fitted
normalization or changed frequency is used to force a desired period.

Insert the full-source moment identity into the previously proved finite
physical response law. At every finite Y>3,

```
integral_a^Y y^(v-2)M(y)dy-B_response(Y)
 = [J_v(M)(Y)-J_v(K)(Y)-J_v(native)(Y)
    -J_v(M)(a)+B_source(a)-integral_a^Y y^(v-r_-)F_-(y)dy]/gap.
```

The first three upper-endpoint terms tend to zero by the predecessor's actual
physical flux remainder theorem. Absolute source integrability gives convergence
of the source moment. Therefore

```
lim_Y [integral_a^Y y^(v-2)M(y)dy-B_response(Y)]
 = [-J_v(M)(a)+B_source(a)-integral_a^infinity y^(v-r_-)F_-(y)dy]/gap.
```

This proves existence and the exact value of the restored cusp period for
both original response branches and all three physical weights. Its value
contains the actual lower-boundary jet and complete source moment. It is not
proved zero.

## Remaining action problem

The two angular-current integrations must still be combined with these restored
response periods and the full scalar-test remainder. The local Q² period,
retained spin-two terms, independent SS/SV/VV channels, solved ++/+- responses,
metric weights and horizon/characteristic/source-contact faces remain part of
the complete physical left-QNM problem. This theorem supplies no universal sign,
clock covariance or extinction assumption. Hawking time and all physical
frequencies remain unchanged; only original angular-height divergences are
restored.

## Method audit

Three deep corpus searches inspected period, Green-current and self-dual
candidate lemmas, proof methods and ingredient sets; each reported partial
retrieval. The local self-dual Jacobi route was already excluded by
`ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo`, whose surviving cyclic
vertex is a graph-Laplacian energy. Its positive survivor requires nonlocal
causal propagation. A generated description of
`d4BMPlusPlusContinuousGreenResponse_adsBranch` incorrectly suggested a zero
response. The actual theorem retains the normalizable solution times a source
moment; that inference was rejected.

Broad recent-paper searches led to Noah Miller's
[26 August 2026 self-dual gravity notes](https://arxiv.org/html/2608.26242v1).
The flat-space amplitude cancellation requires absence of a multiparticle
pole in the summed off-shell current, with collinear qualifications. It is
not a proof of such regularity for the present causal AdS action. The
[27 August 2026 AdS self-dual Yang–Mills paper](https://arxiv.org/html/2608.27731v1)
retains boundary conditions, contact terms and nonzero boundary correlators;
exchange and contact contributions must be combined consistently. The original
source's independent scalar/vector modes have no established identification
with the needed self-dual sector. These papers motivate the complete-action
comparison but do not supply its missing source-level vanishing theorem.


## Lean validation

Module:
[ThetaCuspHawkingBMQuarticResponseCuspFinitePart.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResponseCuspFinitePart.lean),
namespace `RHTower.D4BMQuarticResponseCuspFinitePart`.
Seven public theorems and six definitions are wired once into the RHTower
umbrella. `lake env lean /tmp/hb-response-cusp-finite-part.lean` passed without
diagnostics. Final exact-leaf
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseCuspFinitePart`
passed against cached imports in 18 seconds without warnings. No dependency,
full or umbrella build ran. The audited source SHA256 is
`70c14b84874bac701d5aba6495139a57ffeffa4c6a31154385e104db0905dce4`.

The proof uses explicit finite-power coefficients, local integral admission,
nonzero-gap factorization and the verified source-tail limit. No heartbeat,
recursion-depth or transparency override was added. No numerical experiment or
axiom-printing check was used.

The final corpus search located `integral_cusp_field_from` in
`ThetaCuspHawkingBMCuspFieldIntegral`. It already proves exact native modular
integration of a full cusp-supported field from its horizontal mean under
integrability. Its original chart proof also exposes the product-space admission
needed to transfer the independently proved full scalar-test remainder to the
height-period limit. This is the next attachment, not a reason to erase that
remainder's integral.


Index regeneration registered all thirteen public declarations. Final
`scripts/formal_tools.py lint --check-generated` returned exit 1 for two other
unreachable worktree modules: `ThetaCuspHawkingBMTemporalCurrentFundamentalFactor`
and `ThetaCuspHawkingBMTemporalOppositeOuterCurrent`. No error targets this
leaf, and no stale generated-document error was reported. Those unrelated
modules were not modified. All owned searches, Lean, Lake, index and lint
processes completed; the isolated audit directory was removed.
