# HB: full physical scalar-tested response cusp period

- **ID:** HB-QFTCP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessor:** [source-derived response finite part](hb-physical-response-cusp-finite-part.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical
causal radial/left-QNM action → fixed common Hawking-clock extinction → RH.

## Complete pairing and native admission

Fix an actual Xi occurrence, either original quadratic response branch b, and
a height a>3. Let psi be the original physical scalar test, Q the complete
theta half-square, A_b the constructed full angular response, P the principal
part of psi, and Q0 the original three-power principal half-square. Write

```
T_b=(psi Q-cutoff P Q0) A_b,
R_b(y)=mean_x(T_b(x,y))/y^2,
D_b(y)=mean_x(psi(x,y) Q(x,y) A_b(x,y))/y^2.
```

The original `testedResponseTail_integrable` admits T_b in the native modular
quotient measure. Restrict its exact density chart to the rectangle
[-1/2,1/2] times (3,infinity). This rectangle lies in the original fundamental
cell. The chart density becomes y^-2; the real-product measure equivalence
and Fubini then prove absolute integrability of R_b on (3,infinity).
No pointwise decay bound on the full response is needed for this transfer.

Applying the original cusp integral theorem to the actual height indicator
gives the signed identity

```
integral_(a,infinity) R_b(y)dy
 = integral_{z in native quotient, Im(z)>a} T_b(z)dmu(z).
```

The right-hand side is the original source/test remainder, including both
tails and the original cutoff. It is not assigned a zero value.

## Exact restoration and finite part

Let L=Lambda(rho-1), let A_i be the three original principal source amplitudes,
v_i the unchanged physical test/source weights, and M_b the full response
mean. The already established horizontal source identity yields, for y>3,

```
D_b(y)=R_b(y)+L sum_i A_i y^(v_i-2) M_b(y).
```

All finite-interval integrations are admitted: R_b by the native L1 transfer,
and the weighted full means by their proved differentiability. Let B_bi be
the source-prescribed response counterterms from the predecessor and put

```
B_b(Y)=L sum_i A_i B_bi(Y).
```

For a,c>3 the exact identity is

```
integral_a^c D_b(y)dy-B_b(c)
 = integral_a^c R_b(y)dy
   +L sum_i A_i [J_i(c)-J_i(K)(c)-J_i(native)(c)
                 -J_i(a)+B_source,i(a)-integral_a^c F_i(y)dy]/gap_i.
```

Every quantity on the right is the original one: the full response Wronskian,
particular cusp response, native homogeneous coefficient, lower boundary jet,
source antiderivative, complete signed source-tail density, and physical gap.
The predecessor proves decay of the first three terms as one complete flux
remainder and absolute admission of F_i. Native admission supplies the limit
of the R_b integral. Finite-sum limit rules therefore give

```
lim_(Y→infinity) [integral_a^Y D_b(y)dy-B_b(Y)]
 = integral_{native cusp above a} T_b dmu
   +L sum_i A_i sourceDeterminedPeriod_bi(a).
```

This is the finite part of the full physical pairing, including the scalar
test remainder. Both branches and all three source powers remain independent.
All public theorems specialize original constructed data and add no extinction,
covariance, orientation, integrability or action-identification premises.

## What this leaves for extinction

The remaining angular current must be tested with psi itself. In planar cusp
coordinates, the relevant product rule is

```
psi div J = div(psi J)-grad psi dot J.
```

Thus even after horizontal side cancellation, integrating an actual divergence
retains its upper and lower tested vertical currents and the scalar-test
derivative work. Declaring those terms zero would lose part of the physical
projection. The new theorem supplies the response-source periods for that
balance; it does not yet supply the complete tested-current balance, the local
Q^2 finite part, or cancellation across all independent scalar/vector channels
and horizon, characteristic, cusp and source-contact boundaries.

No fixed-clock invariance or radiative extinction follows merely from the
existence of this finite part. HB remains open and is not retired.

## Lean verification

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticFullTestedCuspPeriod`.
Five public theorems and five public definitions. Scratch verification passed
with `lake env lean /tmp/hb-full-tested-cusp-period.lean` at default limits.
The isolated final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticFullTestedCuspPeriod` passed in 66 seconds using cached imports. Source SHA256: `e4e2f2efc0c15ec211def51df61969ee227614025ce295ceda872a541d147bde`. The umbrella imports the leaf once.
No heartbeat, recursion-depth or transparency override was added.

The generated index was refreshed once (4 changed files); all ten public API
entries and the single umbrella import were checked. Repository
`scripts/formal_tools.py lint --check-generated` passed with exit code 0.
The audit source hash was rechecked unchanged. All owned Lean, audit, search,
index and lint processes completed; the temporary audit directory was removed.
