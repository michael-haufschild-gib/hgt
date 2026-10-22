# Fixed-source horizon matching

Target remains full temporal/metric/QNM matching of the original corrected
future field. DN37 identifies the canonical action with a source-derived
profile, but does not identify that profile with the corrected future field
or a physical Peierls observable. DN82 closes original future-pulse smoothness.

[BRIDGE] The remaining horizon contribution should admit joint target
derivatives through a fixed-source kernel, without differentiating the
original angular field at circles of unbounded radius.

For a target `(tau,x)`, put

```
D_x(t)=cosh(x)*exp(t)+sinh(x),
V_x(t)=tau+log(D_x(t)),
J_x(t)=cosh(x)*exp(t)/D_x(t),  t>0.
```

Then `D_x(t)>0`, `V_x` maps `(0,infinity)` bijectively to
`(tau+x,infinity)`, its derivative is `J_x`, and the original horizon
argument at source time `V_x(t)` is exactly `exp(t)`. Thus the same fixed
angular mean `M(arcosh(exp(t)),X,k)` serves both original characteristic
arms. Their scalar weights differ only by replacing x with -x. The original
onset derivative vanishes before zero, so its original positive source-time
domain is retained by this change of variables.

For either original angular field F, the corresponding polar kernel on the
hyperbolic plane is

```
cosh(x)*timeOnsetFirst(2*s,tau+log(cosh(x)*cosh(d)+sinh(x)))
  /(cosh(x)*cosh(d)+sinh(x)).
```

The angular average contributes `1/(2*pi)`; hyperbolic area contributes
`sinh(d) dd dtheta`. The denominator is positive even at d=0. In fixed
source coordinates target derivatives act on this smooth scalar kernel.
This is an analytical candidate, not an established plane-integral identity.

The actual combined angular input is `B-s*(s-1)*Q/4`, multiplied by
`power(2*s,2)*amp^2`. This follows from the independently specified seed
and lift trace coefficients; neither horizon arm may be dropped.

## Temporal/radial regularity: analytical proof

Write a=2s and z=exp(-h). For source time beyond one the exact weight is

```
J_x(h)*timeOnsetFirst(a,V_x(h)) = exp(a*h)*W_a(tau,x,z),
W_a(tau,x,z) = a*exp(a*(tau+log(cosh(x)+z*sinh(x))))
                *cosh(x)/(cosh(x)+z*sinh(x)).
```

For `0<=z<=1`, its denominator is the positive convex combination
`(1-z)*cosh(x)+z*exp(x)`. W therefore extends smoothly through z=0 and z=1.
On each compact target neighborhood, every tau/x derivative of W is bounded
uniformly on this closed z interval. Also
`cosh(x)+z*sinh(x)>=exp(-abs(x))`, so one finite H makes V_x(h)>1 for
every target in that neighborhood and every h>H.

The integral over `0<=h<=H` is smooth by finite parameter integration: its
angular mean is continuous and independent of tau/x. On h>H, the actual
B mean and Q mean have bounds `C*exp(gamma*h)` for some gamma<2, using
`arcosh(exp(h))<=h+log(2)` and their established growth bounds. Since
`Re(a)<-2`, the product with every differentiated weight is bounded by
`C_n*exp((Re(a)+gamma)*h)`, an integrable function. Repeated dominated
differentiation proves joint C-infinity regularity in tau/x for each fixed
angular base point, for both complete caps. It requires no growth estimates
on angular derivatives. The source-variable equality and compact smooth
weight are Lean verified; the full dominated-differentiation theorem
for the cap remains to be formalised.

The direct fixed-plane proof still needs absolute source-plane admission.
The bound on the norm of the spherical mean of B does not bound its spherical
mean of norms. A proof must use the actual modular decomposition
`fullAngular=globalCuspCutoff+globalResponse`, whose remainder is the native
Hilbert-space correction, or prove the required stronger bound. It cannot
silently replace this obligation by the already proved radial mean estimate.

Whole-route consequence: fixing the source geometry exposes where the actual
angular differentiability problem sits. Temporal/radial cap derivatives are
already partly controlled by CapNormalTrace's delay substitution; a new proof
must include angular derivatives and the noncompact left-QNM admission.
No matching impossibility or RH conclusion follows yet.

## Lean status

`ThetaCuspHawkingBMFixedSourceHorizon` (260 lines) proves
`sourceArm_eq_fixedArm`, `liftCap_eq_fixed`, `seedCap_eq_fixed`, and
`combinedCap_eq_fixed` for the original admitted fields, with no matching
or convergence premise. `tailWeight_smooth` and `late_weight_factorization`
prove the compact smooth tail formula above. Scratch passed in 12.41 seconds;
the exact leaf audit with a reduced direct import passed in 16.05 seconds,
two jobs, no warnings. Source bytes and installed olean verified; umbrella
wired without building it. Default heartbeats, one foreground Lean process.

The only change to `FutureSeedHorizonCap` makes its existing
`seedCapField_arms` theorem public; its proof is unchanged. The exact
dependency leaf audit passed in 58.73 seconds, two jobs, no warnings.
No pointwise angular-derivative admission or full matching claim is added.
Repository lint reports only the pre-existing unreachable
`ThetaCuspHawkingBMOnsetTransgressionHorizon` error and existing size warnings.
No error concerns the new leaf or modified dependency.

Search evidence: broad cap/transgression/polar and derivative-growth searches;
deep matching and kernel-derivative mechanism searches inspected candidate
statements, source proof methods and ingredient groups. Matching search was
partial; other completed searches reported complete inventory but predominantly
source-only compiler coverage. NativeSourceJetGrowth permits an unrestricted
radius exponent, which does not supply the fixed-clock integrable jet bound.
The August 2026 paper [AKSZ Descent on Manifolds with Ordinary Corners](https://arxiv.org/abs/2608.02928)
retains oriented face defects under an explicit
formal mapping-space hypothesis; it supplies no applicable noncompact source
admission theorem here. No result from it is used in Lean.
