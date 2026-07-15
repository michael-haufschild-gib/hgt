# The coupled Mobius causal source is Fisher-flat at the critical boundary

- **ID:** `mobius-causal-fisher-connection-flatness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HT CURVATURE SELECTOR
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `not_new_scientific_knowledge/mobius-schur-causal-critical-graph-limit-law.md`
  - `not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
  - `../1-in-progress/calibrated-clock-curvature-class.md`
- **Statement:** The normalized squarefree channel has a nonzero four-unit critical Fisher
  tangent, but the exact coupled floor--Mobius causal source has a differentiable strong critical
  limit and its Fisher-scaled total parameter derivative tends strongly to zero.  Hence the
  contact tangent cannot be the derivative of the assembled causal vector.  It can survive only
  as the curvature created when a source-selected boundary/Sonin splitting prevents the two
  causal connection terms from cancelling.

## Exact causal multiplier

Put `sigma=1+2omega` and let

```text
F_omega(t)=e^(-(1+omega)t)E_omega(e^t).                  (1)
```

The proved coupled causal decomposition has Laplace transform

```text
M_omega(z)=L F_omega(z)
 =zeta(1+z)/[(1+omega+z)zeta(1+2omega+z)]
  -1/[(1+omega)z zeta(1+2omega)].                       (2)
```

The apparent singularity at `z=0` is removable.  The parent theorem proves

```text
M_omega->1/(1+z) in H2(Re z>0),
F_omega->e^(-t) in L2(0,infinity).                       (3)
```

## Differentiable critical limit `[PROVED HERE]`

The map `omega |-> M_omega` extends right-differentiably to `omega=0` as an `H2`-valued map.  Its
derivative is

```text
M_0'(z)
 =-1/(1+z)^2
  -2/(1+z) zeta'(1+z)/zeta(1+z)
  -2/z.                                                  (4)
```

The pole terms in `(4)` cancel at `z=0`, so the right side is holomorphic on `Re z>0` and belongs
to `H2`.

### Proof

Differentiate `(2)` for `omega>0`.  For the first term this gives

```text
zeta(1+z)/[(1+omega+z)zeta(1+2omega+z)]
 *[-1/(1+omega+z)
   -2zeta'(1+2omega+z)/zeta(1+2omega+z)].                (5)
```

Write `r(omega)=1/zeta(1+2omega)`.  The derivative of the second term in `(2)` is

```text
r(omega)/[(1+omega)^2z]
 -r'(omega)/[(1+omega)z].                                (6)
```

The Laurent expansion at the zeta pole gives

```text
r(omega)=2omega+O(omega^2),
r'(omega)=2+O(omega).                                    (7)
```

Equations `(5)`--`(7)` give `(4)` pointwise.

For `|z|` small, subtract the Laurent pole of zeta in `(2)` before differentiating.  The
remainders and their first `omega` derivatives are uniformly bounded, and the `2/z` terms from
`(5)` and `(6)` cancel uniformly.  On the boundary `z=i tau` with `|tau|` outside a fixed small
interval, the classical line-one estimates give a common majorant of the form

```text
C log(2+|tau|)^2/|tau|.                                  (8)
```

Its square is integrable there.  Dominated convergence on the boundary proves convergence of the
derivatives in `H2`, hence right differentiability and `(4)`. `QED`

Let `dot F_0` be the inverse Laplace transform of `(4)`.  The Laplace isometry gives

```text
partial_omega F_omega->dot F_0 in L2(0,infinity).        (9)
```

In particular,

```text
4omega partial_omega F_omega->0 strongly.               (10)
```

Since `epsilon=sigma-1=2omega` and `partial_sigma=(1/2)partial_omega`, equation `(10)` is exactly

```text
4epsilon partial_sigma F_omega->0 strongly.             (11)
```

## Normalized signed-coisometry form

Let

```text
Z_omega=sum_d mu(d)^2d^(-1-2omega),
R_omega Y_omega=F_omega/Z_omega                          (12)
```

be the exact pointed signed-coisometry identity.  Since

```text
Z_omega~1/(2omega zeta(2)),                              (13)
```

equations `(3)`, `(9)`, and `(13)` also give

```text
4epsilon partial_sigma(R_omega Y_omega)->0 strongly.     (14)
```

At every finite cutoff the derivative in `(14)` has the exact Leibniz decomposition

```text
4epsilon partial_sigma(RY)
 =4epsilon(partial_sigma R)Y
  +4epsilon R(partial_sigma Y).                          (15)
```

The first term contains the proved squarefree Fisher tangent.  Equation `(14)` says that after
the entire coupled incidence is assembled on the causal side, it is cancelled by the incidence
connection term.  This is compatible with the nonzero source QFI because Fisher energy measures
the motion of the pointed channel line before causal synthesis, not the derivative of the final
assembled vector.

## No-go and positive curvature theorem

The tempting identification

```text
completed contact tangent
 =critical parameter derivative of the coupled causal source
```

is false by `(11)`--`(14)`: the right side vanishes at Fisher scale.

The failure has a nontrivial positive consequence.  Let `P_(omega,delta,D,u)` be any
source-selected boundary/Sonin projection acting before the two terms in `(15)` are recombined.
Lueders pinching splits a finite connection observable into its retained and erased blocks.  If
the unsplit causal connection is flat as in `(14)`, its erased cross block is literally the
curvature of this splitting:

```text
causal Fisher term + causal incidence term=0,
boundary splitting of the two terms !=0.                 (16)
```

Thus the only surviving source architecture is

```text
moving signed Mobius line
  + complementary floor/tail incidence connection
  + Gamma/Sonin boundary projection before recombination
  -> off-diagonal connection curvature.                 (17)
```

The existing clock-curvature Bianchi and boundary-channel conservation laws apply algebraically
to `(17)`.  What remains open is the zeta-specific analytic identification of this curvature with
the anti-causal Xi seam and its four-unit relative-trace calibration.

**Positive general-HT statement.**  A constrained HT source may have nonzero projective Fisher
motion at every finite observation scale while its fully assembled causal realization is
connection-flat.  The global boundary datum is then not the source derivative but the curvature
created by resolving the cancelling connection terms in a different completion.  This gives a
concrete analytic instance of “the object is fixed by a constraint, not propagated by a flow.”

## Literature gate

Differentiation of Dirichlet/Laplace multipliers and projective Fisher geometry are standard.
Targeted searches have not located the combination `(11)`--`(17)` for the coupled shifted-Euler
source.  Project results used above are admissible inputs; novelty is tested only against external
literature.  Specialist audit remains open, and no novelty declaration is required for the route
selection.

## Gates

- [x] exact coupled causal multiplier used
- [x] differentiate the multiplier in the safe half-plane
- [x] prove the derivative has an `H2` critical limit
- [x] prove Fisher-scaled causal flatness
- [x] transfer flatness to the normalized signed coisometry
- [x] identify the cancelling Fisher/incidence connection pair
- [x] select boundary splitting curvature as the only survivor
- [ ] write the finite Gamma/Sonin curvature kernel from the incidence packets
- [ ] identify its relative trace with the anti-causal Xi seam
- [ ] prove its four-unit calibration
- [ ] independent specialist literature audit
- [ ] RH
