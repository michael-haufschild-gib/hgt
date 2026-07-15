# Before There Was Time: holographic horizon curvature and integrability rigidity

- **ID:** `pretemporal-horizon-curvature-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM / FILTERED LIE CONSTRAINTS / HYPERTRANSCENDENCE GEOMETRY
- **Scientific status:** `[LEAN-FORMALIZED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED]`
- **Statement:** The apparent countable characteristic arrangement of a rank-one filtered
  hypertranscendental observable collapses under commutator closure. Its obstruction is an
  intrinsic alternating consecutive-symbol curvature.

## 1. Setup

Let `k subset K subset L` be fields, let `g` be a `k`-linear law space, and let

```text
rho : g -> Der_k(L)
```

preserve `K`. Let `(u_n)` be algebraically independent over `K`, and suppose

```text
rho(A)u_n = sigma_n(A) u_(n+1) mod F_n,
F_n = span_K{u_0,...,u_n},
```

for linear layer symbols `sigma_n:g -> K`.

Define the consecutive-symbol curvature

```text
Omega_n(A,B)
  = sigma_n(B) sigma_(n+1)(A)
      - sigma_n(A) sigma_(n+1)(B).
```

It is the coefficient of `u_(n+2)` in the commutator
`rho(A)rho(B)-rho(B)rho(A)`.

## 2. Curvature and closure theorem `[PROVED HERE]`

If the laws close under commutator at filtered order one, meaning that for every
`A,B` there is a law `[A,B]` with

```text
rho(A)rho(B)-rho(B)rho(A)=rho([A,B]),
```

then

```text
Omega_n(A,B)=0
```

for every `n,A,B`.

The reason is order: the right side raises the source filtration by at most one layer, while
`Omega_n(A,B)` is the only possible two-layer principal coefficient on the left. Algebraic
independence prevents that coefficient from being absorbed by the lower filtration.

## 3. Horizon rigidity theorem `[PROVED HERE]`

Under the same closure hypothesis:

1. if some linear map `sigma_m` is identically zero, every law direction is
   differential-algebraic on `u_0`;
2. if every `sigma_m` is nonzero, all kernels `ker sigma_m` coincide and

```text
{A | u_0 is differential-algebraic for rho(A)} = ker sigma_0.
```

Thus a closed rank-one constraint algebra admits only one projective characteristic horizon, not
an arbitrary countable arrangement.

### Proof

Write

```text
rho(B)u_n = sigma_n(B)u_(n+1) + r_B,   r_B in F_n.
```

Applying `rho(A)`, compatibility with the coefficient-field derivation puts
`rho(A)r_B` and `rho(A)(sigma_n(B))u_(n+1)` below `u_(n+2)`. Hence

```text
rho(A)rho(B)u_n
  = sigma_n(B)sigma_(n+1)(A)u_(n+2) mod F_(n+1).
```

Antisymmetrization gives `Omega_n(A,B)` as the exact `u_(n+2)` coefficient of the commutator.
Commutator closure identifies the commutator with `rho([A,B])`, which raises the filtration by at
most one layer and therefore belongs to `F_(n+1)`. Algebraic independence of `(u_n)` forces
`Omega_n(A,B)=0`.

Suppose `sigma_n` and `sigma_(n+1)` are both nonzero. Choose `B` with `sigma_n(B) != 0`. If
`sigma_n(A)=0`, the identity `Omega_n(A,B)=0` gives

```text
sigma_n(B)sigma_(n+1)(A)=0,
```

so `sigma_(n+1)(A)=0`. Reversing the two layers gives the opposite kernel inclusion. Thus adjacent
nonzero kernels agree, and induction identifies every layer kernel with `ker sigma_0`.

The graded principal-symbol theorem identifies the differential-algebraic spectrum with the union
of all layer kernels. If one layer map is zero, that union is the whole law space. Otherwise all
kernels coincide and the union is `ker sigma_0`. `QED`

## 4. Physical meaning `[CONJECTURE]`

Before a time ray is selected, commutator closure is the consistency law for candidate observable
directions. The curvature `Omega` measures whether two candidate laws generate a forbidden
two-layer displacement. Vanishing curvature is integrability; a nonzero value is an anomaly.

The theorem would imply that a genuinely stratified horizon requires at least one of:

- an anomalous/open constraint algebra;
- higher-rank graded observable sectors, producing matrix-valued symbols;
- failure of the rank-one algebraically free source model.

This is a falsifiable structural statement, not a claim that a known QFT or cosmology realizes the
model.

## 5. Lean formalization

`formal/GaloisForLFunctions/HTGeometry/PrincipalSymbolCurvatureRigidity.lean` proves:

- `principalSymbolCurvatureForm`, the genuine bilinear curvature form;
- `law_comp_sub_consecutiveSymbol_smul_mem`, the two-step symbol product;
- `law_commutator_sub_principalSymbolCurvature_smul_mem`, the exact commutator coefficient;
- `principalSymbolCurvature_eq_zero_of_commutatorClosure`, integrability implies flatness;
- `no_commutatorClosure_of_principalSymbolCurvature_ne_zero`, the exact anomaly obstruction;
- `consecutiveSymbol_ker_eq_of_curvature_zero` and
  `all_layerSymbol_kernels_eq_first_of_curvature_zero`, kernel rigidity;
- `principalSymbolCurvature_unique`, intrinsicness of the curvature;
- `characteristicSet_eq_univ_of_layerSymbol_eq_zero` and
  `characteristicSet_eq_first_ker_of_commutatorClosure`, the two exact branches;
- `characteristicSet_integrable_rankOne_dichotomy`, the complete theorem.

The complete module passes direct Lean source checking, targeted integration build, formal lint,
and terminal axiom audit. The audited theorem surface depends only on `propext`,
`Classical.choice`, and `Quot.sound`; it contains no project axiom, `sorry`, `admit`, opaque
declaration, or unsafe declaration.

## 6. Anti-theatre and significance gate

The free realization of arbitrary symbol sequences is elementary and does not survive the
significance gate. The curvature theorem instead removes those arbitrary arrangements from the
integrable constraint class and identifies the exact obstruction left behind.

The parent audit confirms that symbol-level commutator obstructions are standard. Spencer
cohomology packages obstructions to formal integrability; Kruglikov--Lychagin identify bracket
vanishing with formal integrability for generalized complete-intersection PDE systems; rank-one
flatness calculations also make wedge-zero identities unsurprising. Hypertranscendence literature
proves algebraic independence of successive derivatives for fixed difference equations, but does
not parameterize the ordinary derivation itself by a closed law algebra.

Exact and equivalent searches found no source deriving the **ordinary differential-algebraic law
spectrum dichotomy** above from filtered commutator closure. This remains an absence-of-hit report,
not a priority claim. The curvature identity alone is `[BRIDGE]`; candidate scientific content is
the fact that its vanishing collapses the complete hypertranscendence horizon to one kernel or the
whole law space.

## 7. RH impact

No direct RH implication is present. The theorem does kill a class of possible RH strategies: a
rank-one algebraically free completed-`L`-function filtration with a closed first-order law algebra
cannot produce several independent characteristic walls. Any such route must use a higher-rank
observable sector, a nonclosed/anomalous law system, or additional non-symbolic input.

## 8. Lean obligations

- [x] two-step principal commutator formula
- [x] curvature vanishing under first-order commutator closure
- [x] equality of consecutive nonzero symbol kernels
- [x] all-layer kernel collapse
- [x] exact characteristic-spectrum dichotomy
- [x] symbol-curvature intrinsicness from symbol uniqueness
- [x] targeted build, formal lint, and terminal axiom audit
