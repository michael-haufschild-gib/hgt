# HB: the actual causal kernel's characteristic integral equation

Status: two public theorems formalized and audited. Equality of the complete native and physical causal responses, full-current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0` with independent tensor amplitudes and all physical boundary currents. The new result supplies an exact integral equation for the already constructed physical kernel, needed to identify the response used in that pairing.

## Exact result

The module is `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalGoursat`, namespace `RHTower.D4BMCausalKernel`. Write

```
R_nu(h,x,y)=legendreKernel(nu,Z(h,x,y)),
Z=(cosh h+sinh x sinh y)/(cosh x cosh y),
u=h+x-y, v=h-x+y,
Rhat_nu(a,b;y)=R_nu((a+b)/2,y+(a-b)/2,y).
```

For every complex degree and every original `CausalPoint`, `riemannKernel_goursat` proves

```
R_nu(h,x,y)=1+integral_0^u integral_0^v
  nu(nu+1) Rhat_nu(a,b;y)/(4 cosh(y+(a-b)/2)^2) db da.
```

The theorem includes both characteristic edges and their vertex. It assumes no kernel differential equation or integral representation: it derives the mixed derivative from the actual hyperbolic invariant and the previously constructed Gauss series. The two original characteristic values equal one, their tangential derivative vanishes, and two finite-interval FTC applications give the formula. Continuity and integrability of the actual derivatives on the relevant intervals are proved.

Let `C_nu(h,x,y)` be the displayed rectangle integral inside the forward cone and zero outside. With the original degree `nu=-1/2+i chi`, `dirichletCausalKernel_volterra` proves

```
dirichletCausalKernel(chi,h,x,y)
 = (1_{|x-y|<=h}-1_{|x+y|<=h})/2
   +(C_nu(h,x,y)-C_nu(h,x,-y))/2.
```

Both support conditions, the reflected source point, and the original factor one half remain explicit. For a principal exponent `alpha`, degree `nu=-alpha` gives precisely the potential coefficient `alpha(alpha-1)`; the previously audited circle-to-Gauss theorem supplies that principal kernel.

## Remaining comparison

The [current comparison card](../1-in-progress/hb-native-cusp-inverse-identification.md) gives the analytical source-impulse and Volterra interpretation. In null coordinates the rectangle Jacobian is one half, so the displayed formula is the scalar kernel identity behind `G=G0+G0*(V G)`. The constant term has exactly the unit physical source normalization.

The Lean results do not yet construct the forced L² integral or prove the distribution identity. To identify the native response with `principalTimeResponse`, integrate against the original forcing, justify the actual integral interchanges, and convert the free wave integral equation to the existing free massive Duhamel equation with mass `2*pi`. The full angular residual still requires its original domain and boundary admission, and the complete physical current remains unevaluated.

## Validation

Foreground scratch `lake env lean` passed without warnings. Final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalGoursat`, using 2623 frozen own-module caches and 11 package caches. The new leaf built in 66 seconds; Lake reported three jobs. No old dependency, full or umbrella build ran.

Only the two new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. All six installed source/artifact files match the audited files byte for byte. The unique import is in the `GaloisForLFunctions.RHTower` area umbrella; no umbrella build ran.

Global formal lint passed. The module-filtered lexical corpus search returned both public theorems. The frontier map and route-independent STATUS ledger were unchanged. No mathematical computations ran.

All owned Lean/Lake, search and lint processes completed. Scratch files and the frozen audit tree were removed.
