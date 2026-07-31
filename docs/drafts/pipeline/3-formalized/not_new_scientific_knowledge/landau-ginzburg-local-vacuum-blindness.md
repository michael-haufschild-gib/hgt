# Lagrange-multiplier Landau--Ginzburg vacua are locally blind to RH

- **ID:** `landau-ginzburg-local-vacuum-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
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
- [x] 2 → 3 formalized: every item of the theorem, the RH-blind pair, and the Jacobian-algebra
  statement are proved unconditionally in Lean; the matrix-factorization category, its invariance
  under analytic coordinate change, the local ring of analytic germs, and Hadamard division in two
  complex variables were all built for this card.  `lake build` green,
  `#print axioms` clean on every declaration.
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

### `formal/GaloisForLFunctions/RHTower/LandauGinzburgRHBlindPair.lean` — the exact RH-blind pair

The card's "Exact RH-blind pair" section, formalized in full and unconditionally.

| Declaration | Statement |
|---|---|
| `linearQuartic r₀ r₁ r₂ r₃` | the quartic with four prescribed roots |
| `deriv_linearQuartic_root₀`, `linearQuartic_swap₁/₂/₃` | the derivative at each root is the product of the three differences |
| `deriv_linearQuartic_ne_zero` | four distinct prescribed roots are all simple |
| `onQuartic b₁ b₂`, `offQuartic a b` | `(z²+b₁²)(z²+b₂²)` and `((z−a)²+b²)((z+a)²+b²)` with `z = s − 1/2` |
| `onQuartic_eq_linearQuartic`, `offQuartic_eq_linearQuartic` | the explicit linear factorizations, via `z² + c² = (z − i c)(z + i c)` |
| `onQuartic_reflection`, `offQuartic_reflection` | `F(1 − s) = F(s)`: both obey the functional-equation reflection |
| `onQuartic_conj`, `offQuartic_conj` | `F(conj s) = conj F(s)`: both are Schwarz real |
| `onQuartic_deriv_ne_zero`, `offQuartic_deriv_ne_zero` | all four zeros of each model are simple |
| `onQuartic_re_eq` | **every zero of the on-line model has real part `1/2`** |
| `offQuartic_re_ne` | **no zero of the off-line model has real part `1/2`** |
| `rhBlind_zero_separation` | the two models are separated by the location of their zeros |
| `rhBlind_localMatrixFactorization_equiv` | **at any zero of either model the local matrix-factorization categories of the two multiplier potentials are equivalent** |

The last two together are the card's conclusion: the zero locations differ, and the local vacuum
data does not.

### The Jacobian algebra — built, including the missing analysis

`formal/GaloisForLFunctions/HTGeometry/AnalyticHadamardDivision.lean` proves **Hadamard division in
two complex variables**, which Mathlib does not have:

| Declaration | Statement |
|---|---|
| `curryShiftSeries p e` | the series whose `n`-th term is the `(n+1)`-st term of `p` with `e` fixed in its first slot |
| `norm_curryShiftSeries_le`, `radius_le_curryShiftSeries` | the shift does not decrease the radius of convergence |
| `apply_eq_curryShiftSeries_add` | `p (n+1) (v,…,v) = v.1 · qA n (v,…,v) + v.2 · qB n (v,…,v)`, from linearity of `curryLeft` and `v = v.1 • (1,0) + v.2 • (0,1)` |
| `exists_hadamard_decomposition` | **`f v = f 0 + v.1 · A v + v.2 · B v` near the origin, with `A`, `B` analytic** |

`formal/GaloisForLFunctions/HTGeometry/AnalyticGermMaximalIdeal.lean`:

| Declaration | Statement |
|---|---|
| `germValue`, `analyticGermValue` | evaluation at the base point as a surjective ring homomorphism onto `ℂ` |
| `germCoordFst`, `germCoordSnd` | the two coordinate germs at the origin |
| `ker_analyticGermValue_eq_span` | **the kernel of evaluation is the coordinate ideal** (the nontrivial inclusion is Hadamard division) |
| `analyticGermQuotientCoordEquiv` | **the quotient of the local ring by the coordinate ideal is `ℂ`** |

`formal/GaloisForLFunctions/RHTower/LandauGinzburgJacobianAlgebra.lean`:

| Declaration | Statement |
|---|---|
| `nodePartialFst`, `nodePartialSnd`, and their `_eq` lemmas | the partial derivatives of the node, computed from `deriv`, are the two coordinates |
| `nodeJacobianIdeal_eq_coordIdeal` | the Jacobian ideal of the node is the coordinate ideal |
| `nodeJacobianAlgebraEquiv` | **the Jacobian algebra of the node is `ℂ`: the Milnor number of a simple vacuum is one** |
| `lgJacobianAlgebraEquiv` | the same at the simple vacuum of any multiplier potential, by transport along `lgNodeGermEquiv` |

This closes item 5 of the theorem.  For the record, the route that was used (all names checked
against the current Mathlib):

- from `HasFPowerSeriesOnBall f p 0 r`, set `qA n := (p (n+1)).curryLeft (1,0)` and
  `qB n := (p (n+1)).curryLeft (0,1)` (`ContinuousMultilinearMap.curryLeft` exists, with
  `curryLeft_apply : (f.curryLeft x) m = f (Fin.cons x m)`);
- `‖qA n‖ ≤ ‖p (n+1)‖` by `ContinuousMultilinearMap.opNorm_le_bound`, hence
  `p.radius ≤ qA.radius` by `le_radius_of_bound` together with `norm_mul_pow_le_of_lt_radius`;
- `A := qA.sum`, `B := qB.sum` are analytic at the origin by
  `FormalMultilinearSeries.hasFPowerSeriesOnBall`;
- termwise, `(x,y) = x • (1,0) + y • (0,1)` and linearity of `curryLeft` give
  `p (n+1) (fun _ ↦ v) = v.1 * qA n (fun _ ↦ v) + v.2 * qB n (fun _ ↦ v)`;
- summing with `HasFPowerSeriesOnBall.hasSum`, `hasSum_nat_add_iff'` and
  `HasFPowerSeriesOnBall.coeff_zero` gives `f v − f 0 = v.1 * A v + v.2 * B v` near the origin.
