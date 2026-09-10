# HB: exact source equation for the native causal response

Status: three public theorems formalized and audited. Equality with the existing massive L² evolution, complete physical current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and all physical boundary currents. This result supplies the exact source equation for the native principal response, needed to identify the causal inverse entering that pairing.

## Actual object and normalization

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSourceEquation`. Namespace: `RHTower.D4BMNativeResponse`.

Let `U(tau,x)=radialResponse nu s amplitude tau x`, the previously constructed integral of the original Riemann kernel against `F=oddSource s amplitude`. All three complex parameters are arbitrary. Set

```
p=tau+x, q=tau-x, a=sigma+y, b=sigma-y,
Uhat(p,q)=U((p+q)/2,(p-q)/2),
Fhat(a,b)=F((a+b)/2,(a-b)/2),
Vhat(c,d)=nu(nu+1)/cosh((c-d)/2)^2.
```

The actual forcing vanishes outside `|y|<=sigma` for nonnegative source time. Its support intersected with the retarded cone is exactly `0<=a<=p`, `0<=b<=q`. The linear map from `(a,b)` to `(sigma,y)` has determinant `-1/2`. Change of variables therefore gives

```
Uhat(p,q)=1/4 integral_0^p integral_0^q R(p,q;a,b) Fhat(a,b) db da,
R(p,q;a,b)=R_nu((p+q-a-b)/2,(p-q)/2,(a-b)/2),
p,q>=0.
```

This equality is proved for the existing `radialResponse`. A private clamped extension of the kernel supplies global continuity for the integration lemmas and is removed on every causal rectangle. It does not replace the integrated kernel or introduce an assumed source equation.

## Forced Goursat equation

The previously audited Riemann-kernel identity gives

```
R(p,q;a,b)=1+1/4 integral_a^p integral_b^q Vhat(c,d) R(c,d;a,b) dd dc.
```

Multiplying by the original forcing and reversing the two triangular integration orders yields

```
Uhat(p,q)=1/4 integral_0^p integral_0^q Fhat(a,b) db da
          +1/4 integral_0^p integral_0^q Vhat(c,d) Uhat(c,d) dd dc.
```

`radialResponse_goursat` proves this at every `p,q>=0`, including the characteristic edges. The private Fubini proof handles a jointly continuous complex integrand depending on all four variables. It does not assume a product of separate source and observation profiles. Compact rectangle integrability, triangular indicators, both order reversals and both Jacobian factors are discharged in Lean.

## Differential and retarded forms

The combined integrand `(Fhat+Vhat Uhat)/4` is jointly continuous. Applying the fundamental theorem of calculus twice to its double primitive, and using local equality with the actual response at interior points, gives

```
partial_q partial_p Uhat=(Fhat+Vhat Uhat)/4, p,q>0.
```

`radialResponse_null_wave` states this with Lean's actual iterated `deriv`, the original source and original potential. This theorem asserts the mixed null derivative. It does not separately assert pure second static derivatives or H² membership.

Define the effective static source `G=F+V U`, where `V(y)=nu(nu+1)/cosh(y)^2`. This source is jointly continuous and has the same finite propagation support as `F` and `U`. Applying the proved coordinate change to `G` gives

```
U(tau,x)=1/2 integral_0^tau integral_(x-(tau-sigma))^(x+(tau-sigma))
  [F(sigma,y)+V(y) U(sigma,y)] dy dsigma,
tau>=0, x arbitrary.
```

`radialResponse_freeDuhamel` proves this on the whole spatial line. Outside `|x|<=tau`, every possible source point in the retarded interval lies outside the effective source's support, so both sides vanish. Characteristic points are included. The complete current calculation remains separate from this scalar source identity.

## Remaining comparison

Writing the last identity as `U=D0(F+V U)`, the exact conversion required by `principalTimeResponse_unique` is

```
D0 G=D_m G+m^2 D_m(D0 G), m=2*pi,
U=D_m F+D_m((m^2+V)U).
```

The free operator identity, its spatial-integral representation in the actual L² quotient, and the necessary Bochner integral interchange remain to be formalized. The new scalar integral identity supplies a route to that comparison without requiring a separate H² argument first. It is not itself an equality with `principalTimeResponse`.

For the complete angular response, the original modular domain, cusp subtraction and boundary admission must also be proved. The complete physical current pairing must still be evaluated.

## Corpus search and validation

Broad Fubini/retarded searches and deep triangle/change-of-variable searches exposed compact-integrability and triangle-interchange arguments. The separated-profile triangle lemmas were insufficient for the coupled kernel, so the exact four-variable integral argument was built. The proof uses the actual mathlib interval-integral swap and Jacobian theorem. Broad OR and deep free/massive-Duhamel searches recovered scalar oscillators and the existing massive Duhamel formulas. Their generated ingredient group did not establish the required free-operator identity. Candidate and source-argument views were inspected. Search reported complete file inventory but incomplete semantic coverage, 48 compiled snapshots, 43 stale snapshots and predominantly source-only metadata. Applicability of every ingredient used here was verified by Lean.

Foreground scratch `lake env lean` passed without warnings. The final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSourceEquation`, with 4029 frozen own-module caches and 11 package caches. The new leaf built in 102 seconds; Lake reported three jobs. No old dependency, full or umbrella build ran.

Only the three new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. All six installed source/artifact files match the audited files byte for byte. The unique import is in the `GaloisForLFunctions.RHTower` area umbrella; no umbrella build ran.

Global formal lint passed, with the corpus's existing file-size warnings. The module-filtered lexical corpus search returned all three public theorems. The frontier map and route-independent STATUS ledger were unchanged. No mathematical computations ran.

All owned Lean/Lake, search and lint processes completed. Scratch files and the frozen audit tree were removed.
