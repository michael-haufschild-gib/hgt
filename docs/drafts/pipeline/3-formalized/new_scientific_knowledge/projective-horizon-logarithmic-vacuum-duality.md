# Projective-horizon logarithmic vacuum duality

- **ID:** `projective-horizon-logarithmic-vacuum-duality`
- **Stage:** 3-formalized
- **Type:** THEOREM / STATIC LANDAU--GINZBURG DUALITY
- **Scientific status:** `[PROVED ON PAPER] [FORMALIZED] [NOVELTY PROVISIONAL] [SIGNIFICANCE OPEN]`
- **Formal status:** fully formalized in Lean 4
- **Parents:** `projective-horizon-finite-jet-page-transition`,
  `projective-horizon-rectangular-schur-caustic`
- **Lane:** source-pure hypertranscendental geometry; no carrier or flow

## Theorem

Let `m,n>=1`, `L=m+n`, and work over a characteristic-zero field `K`.  Fix polynomial tails

```text
P(t)=sum_(r=m)^(L-1) p_r t^r,
Q(t)=sum_(r=n)^(L-1) q_r t^r.                                (1)
```

For a low packet `A(t)=sum_(i<m)a_i t^i` with `a_0!=0`, put `X=A+P` and let
`Y=X^-1 mod t^L`.  For `k>0`, define the source-pure logarithmic coefficient

```text
ell_k(X)=[t^k] log(X/X(0)).                                  (2)
```

The finite sum defining `(2)` is algebraic in the unit-jet coordinates.  Define

```text
W^X_(P,Q)(A)=ell_(L-1)(A+P)-[t^(L-1)] A Q.                   (3)
```

Then:

1. The gradient equations of `(3)` are exactly the critical projective-horizon compatibility
   equations:

   ```text
   partial W^X_(P,Q)/partial a_i
     =[t^(L-1-i)]Y-q_(L-1-i),       0<=i<m.                  (4)
   ```

   Hence the vacuum scheme `Crit(W^X_(P,Q))` is the fiber over the fixed raw and reciprocal tails
   `(P,Q)`.

2. Its Hessian is the symmetric Hankel matrix

   ```text
   H^X_(i,j)=-[t^(L-1-i-j)]Y^2,                              (5)
   ```

   where negative coefficient indices mean zero.  Reversing its rows gives the critical
   raw-to-reciprocal Jacobian:

   ```text
   J_(r,j)=H^X_(m-1-r,j)=-[t^(n+r-j)]Y^2.                    (6)
   ```

   Therefore the Hessian discriminant of `(3)` is exactly the rectangular Schur caustic already
   proved for the observation map.

3. There is a dual potential with the horizon depths exchanged.  Write `Y=B+Q`, where
   `deg B<n`, and define

   ```text
   W^Y_(Q,P)(B)=ell_(L-1)(B+Q)-[t^(L-1)] B P.                (7)
   ```

   At every compatible state `XY=1 mod t^L`, the two critical values are negatives:

   ```text
   W^X_(P,Q)(A)+W^Y_(Q,P)(B)=0.                              (8)
   ```

Thus the same finite source constraint has complementary `m`-field and `n`-field vacuum
descriptions.  Their state schemes agree, their caustics agree after the Hessian row reversal, and
their on-shell actions differ by sign.

On the full pair of truncated raw and reciprocal jet spaces, equip tangent pairs with the
coefficient-residue symplectic form

```text
omega_L((delta X_1,delta Y_1),(delta X_2,delta Y_2))
  =[t^(L-1)](delta X_1 delta Y_2-delta X_2 delta Y_1).       (L)
```

The reciprocal tangent law makes `(L)` vanish identically on the graph of inversion.  Since that
graph has half the ambient dimension, it is Lagrangian; `(2)` supplies its local generating
function.  The two vacuum descriptions are therefore polarizations of one exact Lagrangian
constraint, not separate dynamical systems.

## Proof

For any variation `delta X=delta A`, formal logarithmic differentiation gives

```text
delta ell_(L-1)(X)=[t^(L-1)]Y delta A
  =sum_(i<m)[t^(L-1-i)]Y delta a_i.                          (9)
```

The derivative of the linear term in `(3)` is
`sum_(i<m)q_(L-1-i) delta a_i`.  This proves `(4)`.  Differentiating the static inverse constraint
`XY=1 mod t^L` gives `delta Y=-Y^2 delta X mod t^L`; substituting it into the derivative of `(4)`
proves `(5)`.  The identity `L=m+n` and the substitution `i=m-1-r` prove `(6)`.  The prior
rectangular Schur-caustic theorem then identifies the Hessian divisor.

For `(8)`, compatibility implies

```text
ell_(L-1)(X)+ell_(L-1)(Y)=0.                                 (10)
```

At degree `L-1`, the identity

```text
(A+P)(B+Q)=1 mod t^L                                        (11)
```

has no contribution from `AB`, because `deg(AB)<=L-2`, and no contribution from `PQ`, because
`ord(PQ)>=L`.  Hence

```text
[t^(L-1)](AQ+BP)=0.                                         (12)
```

Adding `(3)` and `(7)` and applying `(10)` and `(12)` proves `(8)`.  `QED`

## Physical meaning

This is a zero-dimensional, static field theory supplied by the source constraint itself.  A
finite observation horizon does not propagate a state: it asks for stationary points of `(3)`.
The Schur divisor is literally its massless-vacuum locus, because it is the vanishing determinant
of the Hessian `(5)`.  Horizon complementarity is an exact rank-level duality of two potential
descriptions, with particle/hole exchange in the pure-tail specialization and the sign reversal
`(8)` for arbitrary tails.

No quantum dynamics, Hilbert-space time evolution, black-hole identification, or holographic
entropy law is inferred.  The exact physical content is the vacuum/Hessian/duality structure.

## Novelty and significance audit

The pure-tail specialization collides with classical Grassmannian quantum cohomology and its
Landau--Ginzburg mirrors: binomial vacua, Schur functions, logarithmic potentials, Hessians, and
rank-level complementarity all have parent theories.  Those ingredients are not claimed as new.

The candidate new content is the all-tail statement: every critical raw/reciprocal HT observation
fiber is exactly the critical scheme of the source-defined potential `(3)`, and the two arbitrary
tail deformations have the exact on-shell sign duality `(8)`.  A targeted literature audit found
the pure Grassmannian construction but not this all-tail observation-family theorem.  This is only
provisional novelty, not proof of absence from the literature.

The theorem gives a canonical static physical structure for finite HT constraints, but no
infinite-depth invariant, classification of hypertranscendence, or new obstruction theorem yet
follows.  It therefore does not currently clear the significance gate and is not the endpoint of
the research lane.

## RH impact

Specializing to the zeta free jet gives a logarithmic vacuum model for each critical finite
observation fiber.  The construction depends only on generic jet coordinates and remains blind to
target translation; it does not mark the Euler source or distinguish the critical line.  Therefore
it has no RH consequence by itself.  Any useful RH refinement would need an arithmetic orientation
of the caustic or of its vanishing cycles, not merely the potential.

## Formal verification

`ProjectiveHorizonLogPotential.lean` defines the finite normalized logarithmic coefficient and both
vacuum potentials, proves the exact differential and reversed-reciprocal gradient `(4)` and `(9)`,
identifies the critical scheme with the compatibility equations, and proves the arbitrary-tail
on-shell sign duality `(8)`.  It also connects the finite definition to Mathlib's formal
power-series logarithm.

`ProjectiveHorizonLandauGinzburgDuality.lean` formalizes the symmetric Hessian `(5)`, its exact row
reversal to `(6)`, and the top-pairing cancellation `(12)`.
`ProjectiveHorizonExactLagrangian.lean` formalizes antisymmetry of `(L)` and exact isotropy of the
reciprocal tangent graph, while `ProjectiveHorizonPolarizationTower.lean` proves that the tangent
graph has half the ambient dimension.  Thus the full logarithmic-vacuum, Hessian, duality, and
Lagrangian theorem surface is formalized.

The three new modules elaborate directly and their dedicated Lake targets pass.  Axiom audits of
the principal gradient, duality, isotropy, and half-dimension theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.  The formal lint gate passes.  No full build was run.
