# Lagrange-multiplier Landau--Ginzburg vacua are locally blind to RH

- **ID:** `landau-ginzburg-local-vacuum-blindness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** independent foreign-field reframe; disjoint from the live RHTower routes in
  `docs/reports/rhtower_status_1107.md`
- **Statement:** For a holomorphic function `F` with simple zeros, the two-field potential
  `W_F(s,u)=uF(s)` realizes every zero as a nondegenerate critical point of common critical value
  zero, but every local Landau--Ginzburg germ is the same node `xy`. Moreover, the family over every
  nonzero potential value is explicitly isotrivial. Consequently, local vacuum invariants and
  ordinary nonzero-fiber monodromy cannot distinguish a divisor on the critical line from an
  FE--Schwarz-symmetric divisor off it.

## Goal

Turn the slogan "the zeros are supersymmetric vacua" into an exact constraint construction and
decide whether its local B-model data or ordinary fibration monodromy contains horizontal
zero-location information. The answer is negative. This eliminates uncompactified
Landau--Ginzburg vacua and nonzero-fiber monodromy as RH mechanisms and localizes any possible
supersymmetric content in extra growth or compactification data at infinity.

## Gates

- [x] 0 → 1 in-progress: precise potential, critical equations, attack by on-line/off-line models.
- [x] 1 → 2 fully-proven: complete proof below; no open dependency in the stated local theorem.
- [ ] 2 → 3 formalized: the algebraic critical-locus, critical-value, Hessian, and node-factorization
  core is proved in `formal/GaloisForLFunctions/RHTower/LandauGinzburgConstraint.lean`; a formal
  category of matrix factorizations and its invariance under analytic coordinate change are not in
  the current Lean development.
- [ ] 3 → 4 publication-ready: not eligible as new scientific knowledge; the parent-theory gate
  fails.

## Construction

Let `U ⊆ C` be open and let `F : U → C` be holomorphic. On `U × C` define

```text
W_F(s,u) = u F(s).
```

This is a static constraint potential. The new coordinate `u` is a Lagrange multiplier, not a time
or flow parameter. Its critical equations are

```text
∂_u W_F = F(s) = 0,
∂_s W_F = u F'(s) = 0.
```

Thus the construction obtains the zero scheme from the source function `F` without first choosing a
list of zeros.

## Theorem `[PROVED HERE]`

Let `rho` be a simple zero of `F`.

1. The unique critical point of `W_F` over `rho` is `(rho,0)`.
2. Every critical point of `W_F` has critical value zero.
3. The Hessian at `(rho,0)` is

   ```text
   [ 0        F'(rho) ]
   [ F'(rho)  0       ],
   ```

   so its determinant is `-F'(rho)^2 ≠ 0`.
4. The germ of `W_F` at `(rho,0)` is analytically equivalent to the node `xy`.
5. Hence the local Jacobian algebra is one-dimensional and the local matrix-factorization category
   is the standard category of the node, independently of `rho`.
6. For every `t≠0`, the fiber `W_F^{-1}(t)` is canonically biholomorphic to `U` with the zeros of
   `F` removed; the whole family over `C*` is a product.

### Proof

The first three assertions follow directly from the displayed critical equations. At a simple zero,
`F'(rho) ≠ 0`, so `uF'(rho)=0` forces `u=0`. At any critical point, `F(s)=0`, hence `W_F(s,u)=0`.
Differentiating a second time gives the displayed Hessian.

For the local form, factor

```text
F(s) = (s-rho) G(s)
```

with `G` holomorphic and `G(rho)=F'(rho)≠0`. The coordinate change

```text
x = s-rho,
y = u G(s)
```

is locally biholomorphic at `(rho,0)`, and in these coordinates

```text
W_F = xy.
```

The Jacobian algebra is therefore `C{x,y}/(x,y) ≅ C`. Invariance of the local singularity and
matrix-factorization categories under analytic coordinate change identifies every simple vacuum
with the same node model. This is the local Landau--Ginzburg/matrix-factorization framework of
[Orlov](https://arxiv.org/abs/math/0302304) and
[Dyckerhoff](https://arxiv.org/abs/0904.4713).

For `t≠0`, the equation `uF(s)=t` forces `F(s)≠0` and then uniquely gives `u=t/F(s)`. Thus

```text
U minus Z(F)  ->  W_F^{-1}(t),
s             |-> (s,t/F(s))
```

is a biholomorphism, with inverse projection to `s`. Simultaneously in `t`, this identifies
`W_F^{-1}(C*)` with `(U minus Z(F)) × C*` over `C*`. Hence the ordinary fibration has no nontrivial
variation or monodromy from which to recover horizontal zero location. ∎

## Exact RH-blind pair `[PROVED HERE]`

Write `z=s-1/2`. Choose `a,b,b_1,b_2>0` with `b_1≠b_2`, and define

```text
F_off(s) = ((z-a)^2+b^2) ((z+a)^2+b^2),
F_on(s)  = (z^2+b_1^2) (z^2+b_2^2).
```

Both are real and even in `z`; therefore both obey functional-equation reflection and Schwarz
reality. Both have four simple zeros. Every zero of `F_on` lies on `Re(s)=1/2`, whereas every zero
of `F_off` lies off that line. Nevertheless the four local germs of `W_{F_on}` and the four local
germs of `W_{F_off}` are each four copies of `xy`.

Therefore any invariant determined only by the multiset of local Landau--Ginzburg vacuum germs,
local Jacobian algebras, Milnor numbers, or local matrix-factorization Morita classes has the same
value on these two models. Such an invariant cannot detect RH-type line confinement.

## Attack and verdict

- `[SEARCH]` Supersymmetric quantum-mechanical models whose energies contain zeta values already
  exist. In one direct construction, the critical-line zero is selected as a parameter of the
  ground state rather than forced by the model; see
  [Kalauni--Milton](https://arxiv.org/abs/2211.04382).
- `[PROVED HERE]` The multiplier model avoids that specific zero-selection step: `F=0` is a critical
  equation.
- `[PROVED HERE]` Local supersymmetric data then erases the horizontal position of every simple
  zero. FE--Schwarz symmetry does not repair the loss.
- `[PROVED HERE]` Passing from local germs to the ordinary family over nonzero critical values does
  not repair the loss: that family is explicitly a product.
- `[BRIDGE]` The proof uses the standard Lagrange-multiplier construction, elementary local
  factorization, and standard locality of matrix factorizations. Erasing the zeta vocabulary leaves
  a routine parent-theory theorem. It therefore fails the parent-theory and significance gates for
  new scientific knowledge.
- `[OPEN CORE]` A supersymmetric route could retain RH information only after adding structure not
  present in the uncompactified Landau--Ginzburg fibration: a source-canonical compactification,
  growth condition, or irregular boundary category at infinity for `W_Xi(s,u)=uXi(s)`. It must not
  reduce to the product trivialization above or to reconstruction of the zero divisor. No such
  source-built boundary theorem is proved here.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/LandauGinzburgConstraint.lean` proves:

- `lagrangeGradient_eq_zero_iff`;
- `lagrangeGradient_eq_zero_iff_of_derivative_ne`;
- `lagrangeGradient_at_simpleRoot_eq_zero_iff`;
- `lagrangePotential_eq_zero_of_gradient_eq_zero`;
- `lagrangePotential_eq_of_gradient_eq_zero`;
- `lagrangeHessianDet_eq`;
- `lagrangeHessianDet_ne_zero_at_simpleRoot`;
- `lagrangePotential_linearFactor_eq_node`;
- `lagrangeFiberEquivZeroComplement`.

The module compiles independently and the theorem declarations have only the standard project
axioms `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-07-11 — paper theorem and algebraic Lean core completed; classified BRIDGE after the
  parent-theory attack. The nonzero-fiber family was then proved isotrivial, leaving only additional
  compactification/growth data at infinity as a possible supersymmetric residue.

## Lean formalization — 2026-07-31 (2 → 3 gate work)

The 2 → 3 gate named one missing item: *"a formal category of matrix factorizations and its
invariance under analytic coordinate change"*.  That is now built, together with the holomorphic
upgrade of the algebraic core (the previous `LandauGinzburgConstraint.lean` was polynomial-only and
its Hessian was a hard-coded expression rather than an actual second-derivative matrix).

All modules build green and every declaration below is `#print axioms`-clean
(`propext`, `Classical.choice`, `Quot.sound` only).  No hypothesis interfaces.

### `formal/GaloisForLFunctions/HTGeometry/MatrixFactorizationCategory.lean`

| Declaration | Statement |
|---|---|
| `MatrixFactorization R w` | two square matrices over `R` of a common size with both products equal to `w • 1` |
| `MFHom`, `Category` instance | morphisms are pairs of matrices intertwining the differentials |
| `MatrixFactorization.map` | the functor induced by a ring homomorphism carrying `w` to `w'` |
| `mapFaithful`, `mapFull`, `mapEssSurj` | a ring isomorphism induces a fully faithful, essentially surjective functor |
| `MatrixFactorization.mapEquivalence` | **`MF(R,w) ≌ MF(S,w')` for any ring isomorphism carrying `w` to `w'`** |

### `formal/GaloisForLFunctions/HTGeometry/AnalyticGermRing.lean`

| Declaration | Statement |
|---|---|
| `analyticGermSubring p`, `AnalyticGerm p` | the germs at `p` with an analytic representative form a subring |
| `germPullbackHom`, `analyticGermPullback` | pullback of germs along a map analytic at the point, as a ring homomorphism |
| `analyticGermEquiv` | **an analytic change of coordinates induces a ring isomorphism of the two local rings** |

### `formal/GaloisForLFunctions/RHTower/LandauGinzburgNodeGerm.lean`

| Declaration | Statement |
|---|---|
| `lgPotential`, `nodePotential` | `W_F(s,u) = u F(s)` and `x y`, as holomorphic functions on `ℂ²` |
| `exists_analyticAt_factor_of_simple_zero` | `F = (z − ρ) G` near a simple zero, `G` analytic and `G(ρ) ≠ 0`; proved from `analyticOrderAt F ρ = 1` |
| `lgCoordChange`, `lgCoordChangeInv` | `(s,u) ↦ (s − ρ, u G(s))` and its inverse, both analytic, mutually inverse near the base points |
| `lgPotential_eventuallyEq_node_comp` | **`W_F = node ∘ Φ` near `(ρ,0)`** |
| `lgNodeGermEquiv` | the induced isomorphism of local rings of analytic germs |
| `lgNodeGermEquiv_node` | it carries the germ of the node to the germ of `W_F` |
| `lgNodeMatrixFactorizationEquiv`, `exists_lgNodeMatrixFactorizationEquiv` | **the matrix-factorization category of `W_F` at `(ρ,0)` is equivalent to that of the node at the origin, for every `F` and every simple zero `ρ`** |

This is theorem items 4 and 5 of the card, unconditionally, in the local analytic category.

### `formal/GaloisForLFunctions/RHTower/LandauGinzburgHolomorphicCore.lean`

Items 1–3 and 6 in the holomorphic setting, with genuine derivatives.

| Declaration | Statement |
|---|---|
| `lgGradient`, `lgGradient_eq` | the gradient is `(u F'(s), F(s))`, computed from `deriv`, not postulated |
| `lgGradient_eq_zero_iff_of_deriv_ne` | at a point of nonvanishing derivative the critical locus is `F(s) = 0, u = 0` |
| `lgPotential_eq_zero_of_lgGradient_eq_zero`, `lgPotential_eq_of_lgGradient_eq_zero` | every critical point has critical value zero |
| `lgHessian`, `lgHessian_eq` | the Hessian assembled from actual iterated partial derivatives equals `!![u F''(s), F'(s); F'(s), 0]` |
| `det_lgHessian`, `det_lgHessian_ne_zero_of_simple` | **the determinant is `−(F'(s))²`, nonzero at a simple zero** |
| `lgNonzeroLocusEquiv` | **the part of the total space over the nonzero values is `(U ∖ Z(F)) × ℂ*`** — the isotriviality of item 6, simultaneously in the value, not one fibre at a time |

### Remaining before the gate can be checked

- The Jacobian algebra of the node and its one-dimensionality (Milnor number 1) in the local ring.
- The exact RH-blind pair `F_on` / `F_off`: both real and even in `z = s − ½`, four simple zeros
  each, all zeros of `F_on` on `Re s = ½` and all zeros of `F_off` off it, and the resulting equal
  multisets of local germs.
