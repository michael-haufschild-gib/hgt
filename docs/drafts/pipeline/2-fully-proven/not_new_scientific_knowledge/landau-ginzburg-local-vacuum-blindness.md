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
