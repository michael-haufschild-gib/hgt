# HB: exact spin-two primitive of the original Riemann kernel

Status: kernel identities formalized. Complete physical extinction and RH remain unproved.

The original positive-chart Legendre kernel has an explicit double primitive for its complete spin-two weight. For every complex degree `nu`, write `ell=nu(nu+1)`, `p=Z^2-1`, and use the actual kernel `P_nu` from `ThetaCuspHawkingBMCausalRiemannKernel`:

```
F_nu(Z)=p[ell P_nu(Z)-2Z P_nu'(Z)]
       =p^2 P_nu''(Z),
F_nu'(Z)=p(ell-2)P_nu'(Z),
F_nu''(Z)=ell(ell-2)P_nu(Z),
F_nu(1)=F_nu'(1)=0.
```

No spectral factor is divided out; the formulas include `ell=0` and `ell=2`. Actual derivatives are proved on the positive real chart. On `Z>=1`, two finite-interval identities also hold:

```
F_nu'(Z)=ell(ell-2) integral_1^Z P_nu(r) dr,
F_nu(Z)=ell(ell-2) integral_1^Z (Z-r)P_nu(r) dr.
```

The proof uses the existing kernel's actual first and second derivatives and its proved differential equation. The Volterra formula follows by differentiating `F_nu(r)+(Z-r)F_nu'(r)` and evaluating both original boundary jets. No fourth-derivative assumption or computation certificate enters the proof.

## Lean statements

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSpinTwoKernelPrimitive`.
Namespace: `RHTower.D4BMSpinTwoKernel`.

- `primitive_derivatives`: the two actual derivative identities.
- `primitive_eq_weighted_second`: the explicit double-zero factor multiplying the original second derivative.
- `primitive_characteristic`: both characteristic jets are zero.
- `primitiveFirst_integral`: the first-primitive integral formula.
- `primitive_volterra`: the full double-primitive integral formula.

## Physical use and limits

The [full-source spin-two transfer](../1-in-progress/hb-spin-two-kernel-transfer.md) derives the corresponding native-circle identity analytically with `Delta` retained as an operator on the complete theta half-square. It transfers the full fixed-onset density on finite ingoing-time domains, controls the coincident-radius characteristic limit on compact radial squares, and displays the retained terminal source Wronskian inside the surviving bulk coefficient.

Those native-circle, time-transfer and integrated-limit statements are not proved by substituting an angular eigenvalue into this leaf. Their formalization, the horizon and cusp limits, matching to the physical response/source-contact currents, and the independent SS/VV coefficients remain open. No vanishing of the resulting bulk or complete action is asserted.

## Validation

The new leaf passed foreground `lake env lean` in scratch. Its final audit used only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSpinTwoKernelPrimitive`, with 2623 existing own-module caches and 11 package caches frozen. It built the new leaf in 80 seconds and reported three jobs. No old dependency, full or umbrella build ran.

Only the five new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Installed source, olean and ilean are byte-identical to the audited files. One umbrella import is wired without building the umbrella. `scripts/formal_tools.py lint` passed with existing large-file warnings. A module-filtered lexical search returned all eight declarations, including all five public theorems.
