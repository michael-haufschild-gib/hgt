# HB: differential rigidity of the literal source contact

Status: formalized. Complete physical extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal/left-QNM action → original common Hawking-clock extinction → RH.

Owner: [ThetaCuspHawkingBMSourceContactRigidity.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceContactRigidity.lean), namespace `RHTower.D4BMSourceContactRigidity`.

## Exact source law

For every actual Xi occurrence, let f be the full literal theta scalar, lambda=q(q-1), Q=f²/2 and E=grad f dot grad f. Both Weyl terms and every Fourier mode remain in f. The original common source producer supplies

```
J=KQ=((7lambda-2)Q-2Delta Q)/8,
J=[(3lambda-2)f²/4-E]/4.
```

The new theorem, evaluated at every point of the original upper half-plane, is

```
(lambda-2)(lambda-6)(3lambda-2) f^4
 =16(lambda-2)(lambda-6) f² J
  +64(lambda-2)[2f grad f dot grad J+J E]
  -128 E Delta J-512 grad J dot grad J.
```

The coefficient multiplying f^4 is proved nonzero for every actual Xi occurrence. The open critical strip gives Re(lambda)<0, excluding 2, 6 and 2/3. No RH assumption is used.

All products and gradient pairings are complex bilinear. This is an exact differential identity, not a Hermitian positivity estimate. It requires no division by the scalar, its gradient energy, the contact, or the fixed onset.

## Proof

Differentiate the original scalar eigen-equation in both real angular coordinates. Establish the first and second contact jets by the actual product rules and equality of source germs. The full third scalar jets, including their ordered derivative exchanges, yield the hyperbolic Bochner formula with curvature -1.

In an orthonormal hyperbolic frame write g=grad f, H=Hess f and k=(3lambda-2)/4. The proved contact derivatives satisfy

```
grad J=(k f g-Hg)/2,
2Delta J=k lambda f²+(k-lambda+1)E-tr(H²),
tr H=lambda f.
```

Contract the two-dimensional Cayley-Hamilton identity against g and substitute these derivatives. Eliminate E from the leading term using 4J=k f²-E. This gives the displayed fourth-power identity. Every scalar equation and differentiability input is discharged from the original theta source; callers supply only an actual Xi occurrence and an upper-half-plane point.

The [active research card](../1-in-progress/hb-source-contact-rigidity.md) records the broader first-order source-symmetry test and its paper endpoint remainder -3K. That operator commutator and its physical boundary transport are not part of this Lean leaf.

## Public API and validation

Three public definitions retain the original contact, its scalar/contact gradient pairing and its own bilinear gradient energy. Three public theorems prove its exact gradient-energy expression, the differential rigidity identity and the nonzero spectral coefficient.

The foreground scratch check passed. Two proof-style warnings were removed before the final exact leaf audit. `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceContactRigidity` passed without warnings in 172 seconds, using twelve existing cache roots; only the new leaf compiled. It is wired once into `RHTower.lean`; no full or umbrella build ran. Source SHA-256: `67ffcc6f7291dc582d8ea482e230cf1af125ff569131ee2d4dec3a673b35ce9e`.

Index refresh, all six public API rows, the unique umbrella import, source/audit hash equality and new-card links were verified. Global formal lint passed with existing large-file warnings. Scoped whitespace checks passed. The 308-line leaf's canonical olean and ilean remain installed; all owned Lean/Lake processes exited and all owned scratch, search-output and audit files were removed. No commit or push was made.

## Effect on the extinction problem

The contact cannot be set identically to zero on an open region while retaining a nonzero scalar there. The full physical action could still cancel this contribution against other terms. The theorem does not establish a global nonzero scalar witness, physical left-QNM identification of this local current, compensation by the ++/+- corrections, cancellation of the nine independent SS/SV/VV pairings, or a signed estimate after every temporal, horizon, exterior, cusp, characteristic and source-contact face is included.

The remaining extinction interface is unchanged: derive the sign of the complete physical action from the source, then combine its physical identification with C=-Sigma|D|² and Sigma>0. This new law supplies a source constraint that such a derivation must respect; it does not itself produce C=0.
