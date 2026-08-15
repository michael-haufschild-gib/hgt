# Route P primitive Burnol aperture defect colligation

- **ID:** `route-p-primitive-burnol-aperture-defect-colligation`
- **Stage:** 3-formalized
- **Label:** `P-G188`
- **Source:** P-G185--P-G187, positive-aperture Burnol conormal geometry
- **Statement:** Every nonnegative weighted-aperture translation has two explicit positive defect
  channels--the deleted boundary interval and the lost tail cocycle--which complete transported
  energy to an exact three-channel conservation law. On every primitive Euler feature their joint
  mass is exactly the complement of P-G185 damping, and globally defect plus transported mass is
  the fixed P-G181 source budget.

## Conjecture and proof

P-G187 proved that

```text
(T_c f)(L) = L/(L+c) f(L+c),     c>=0,
```

is contractive and that no negative time acts on the full positive-aperture `L2` domain. The live
conjecture was that this unilateral loss has a concrete positive completion, rather than only an
abstract contraction defect.

After translating `u=L+c`, transported energy has the exact tail form

```text
E(T_c f) = integral_(u>c) ((u-c)/u)^2 |f(u)|^2 du.                  (1)
```

Define the two defect features

```text
B_c f(u) = 1_(0,c](u) f(u),
D_c f(u) = 1_(c,infinity)(u)
           sqrt(1-((u-c)/u)^2) f(u).                               (2)
```

For every continuous finite-energy datum, Lean proves

```text
E(T_c f) + E(B_c f) + E(D_c f) = E(f).                             (3)
```

The square-root tail weight is pointwise in `[0,1]`; equation `(3)` follows from an exact partition
of the aperture ray and the identity

```text
((u-c)/u)^2 + [1-((u-c)/u)^2] = 1.                                (4)
```

For a primitive Burnol feature with `lambda_(p,e)=log(p^(e+1))` and P-G186 base mass `w_(p,e)`,

```text
E(B_c F_(p,e,kappa)) + E(D_c F_(p,e,kappa))
  = (1-exp(-2c lambda_(p,e))) w_(p,e).                              (5)
```

Hence every defect mass is nonnegative and summable for `c>=0`, and

```text
sum_(p,e) defectMass_c(p,e) + sum_(p,e) transportedMass_c(p,e)
  = routePPrimitiveBaseCauchyCubicTraceBudget < 2.                  (6)
```

## New route knowledge

P-G187's boundary wall is not a single hard-edge scalar. Its exact positive completion has two
geometrically distinct pieces: mass deleted on `(0,c]` and cocycle loss distributed over the
entire surviving tail. Completion therefore has a finite-budget, source-defined target to match.
A polar--Gamma producer must identify or extend these channels before Xi-divisor Gram comparison;
postulating an abstract contraction after zero expansion remains target-fed.

This also sharpens the next conjecturing loop. For primitive Burnol features, the hard-edge term is
higher order at small aperture because the feature vanishes linearly at `L=0`, while the total
defect `(5)` has a nonzero first-order flux. Thus the leading completion current should come from
the distributed tail cocycle, not from boundary-interval mass alone. That infinitesimal claim is
not part of P-G188 and remains to be proved exactly.

The internal `SoninApertureRestrictionDefect.lean` theorem exhibits a related but distinct
universal pattern: nested aperture restriction defects factor through an explicit lost positive
layer. P-G188 supplies the scalar positive-half-line Burnol semigroup analogue and, uniquely here,
identifies its entire primitive mass with the P-G185/P-G186 arithmetic budget.

## Novelty and theatre audit

Internal search found the Sonin lost-layer Gram-square defect and P-G187's aperture semigroup, but
no explicit `(T_c,B_c,D_c)` Burnol colligation, primitive defect-mass formula, or global conserved
Euler budget.

Primary-source audit found general weighted translation and operator-defect/dilation theory,
Burnol's co-Poisson/Sonine Hilbert geometry, and Connes--Consani's scaling positivity framework.
None of the audited sources states `(1)`--`(6)` for Burnol conormal features with primitive Euler
weights: [Phatak--Sholapurkar](https://arxiv.org/abs/1804.08981),
[operator-valued weighted shifts](https://arxiv.org/abs/1902.01708),
[Burnol co-Poisson](https://arxiv.org/abs/math/0407443), and
[Connes--Consani](https://arxiv.org/abs/1910.14368). No external priority claim is made beyond the
exact Route P synthesis formalized here.

The theorem applies to arbitrary continuous finite-energy data and proves the integral identity
directly. It does not define a defect by subtraction, assume a dilation theorem, use Xi zeros, or
claim RH. Equation `(6)` conserves the already-proved source budget; it does not yet identify the
completed polar--Gamma coefficients.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolApertureDefectColligation.lean
```

Capstones:

- `routePBurnolApertureEnergy_forwardDampingShift_eq_tail`;
- `routePBurnolApertureDamping_energy_colligation`;
- `routePPrimitiveBurnolApertureDefect_energy_eq_mass`;
- `routePPrimitiveBurnolApertureDefectMass_nonneg`;
- `summable_routePPrimitiveBurnolApertureDefectMass`;
- `tsum_routePPrimitiveBurnolApertureDefectMass_add_baseMass_eq_budget`.

Verification:

- `/tmp/pg188.lean`: `lake env lean /tmp/pg188.lean` passed cleanly;
- exact leaf build passed;
- `/tmp/pg188_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] paper proof dependency-closed
- [x] exact unconditional Lean formalization
- [x] explicit positive boundary and tail channels
- [x] primitive and global mass conservation
- [x] scratch verification
- [x] exact leaf build
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] identify first-order defect flux with a completed Gamma--polar source current
- [ ] construct matrix-complete boundary transport to Xi divisor nodes
- [ ] unconditional RH
