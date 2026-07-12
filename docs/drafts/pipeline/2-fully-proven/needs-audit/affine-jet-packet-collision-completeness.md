# Generic affine HT carriers have exactly the collision differential matroid

- **ID:** `affine-jet-packet-collision-completeness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GENERIC FUNCTIONAL TRANSCENDENCE LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Statement:** For every countable family of affine automorphisms of `C^d`, a residual set of
  entire functions has differentially algebraically independent pullbacks along all distinct
  automorphisms.  Consequently the complete differential-algebraic matroid of a generic affine
  orbit is exactly the collision matroid of the carrier action.

## Why this is the stronger law

Hypertranscendence of one function says only that its derivative tower has no finite algebraic
handle.  It does not determine what happens after the carrier is observed from many translated or
affine frames.  The law here determines the whole countable orbit at once:

> **Infinitesimal packet law.**  If a carrier can prescribe arbitrary finite jets at arbitrary
> finite point packets, then a generic source converts geometric distinctness of observation frames
> into complete differential-algebraic independence.  The only generic relations are the positive
> geometric relations `same frame = same observation`.

Thus the constraint is not a flow and not a special formula.  It is the collision geometry of the
carrier action, read through finite infinitesimal packets.

## Setup

Fix `d>=1`.  Write

```text
O_d=O(C^d),                 K=C(z_1,...,z_d),
partial=(partial_1,...,partial_d).                           (1)
```

Give `O_d` its compact-open Frechet topology.  Let `Lambda` be countable and let

```text
sigma_lambda(z)=A_lambda z+b_lambda,   A_lambda in GL_d(C),  (2)
```

be a family of affine automorphisms.  Repetitions are allowed.  For `f in O_d`, put

```text
F_lambda=f o sigma_lambda.                                  (3)
```

Two labels collide when their affine maps are equal:

```text
lambda ~ mu  iff  sigma_lambda=sigma_mu.                    (4)
```

## The affine jet-packet theorem `[PROVED HERE]`

There is a dense `G_delta` subset `R subset O_d` such that, for every `f in R`, every finite family
of pairwise noncolliding labels `lambda_1,...,lambda_m`, and every nonzero partial differential
polynomial

```text
P in K{Y_1,...,Y_m}_{partial_1,...,partial_d},               (5)
```

one has

```text
P(F_(lambda_1),...,F_(lambda_m)) != 0.                      (6)
```

Equivalently, the countable family indexed by distinct affine maps is differentially
algebraically independent over `K`.

For an arbitrary labelled family, the differential-algebraic matroid on `Lambda` therefore has
rank function

```text
r_f(E)=# {sigma_lambda:lambda in E}                          (7)
```

for every finite `E subset Lambda`.  This is exactly the partition/collision matroid induced by
(4).  In positive form: every distinct affine frame contributes one full differential
transcendence direction.

## Complete proof

### 1. Replace arbitrary coefficients by a countable determinant test

Introduce formal jet variables

```text
Y_(lambda,beta),   lambda in Lambda, beta in N^d.           (8)
```

A **decorated differential monomial** is

```text
M=z^alpha product_(lambda,beta) Y_(lambda,beta)^(e_(lambda,beta)),  (9)
```

with finite support.  Because `Lambda` and `N^d` are countable, the set of such monomials is
countable.

For every finite list `S=(M_1,...,M_q)` of distinct decorated monomials, we shall choose points
`x_1,...,x_q in C^d` and define

```text
Delta_S(f)=det(M_i(jet_partial(f o sigma)(x_j)))_(j,i).     (10)
```

If `Delta_S(f)!=0`, the analytic functions obtained from `M_1,...,M_q` are linearly independent
over `C`.  Requiring this for every `S` is countable.

It is also sufficient.  If (6) failed, clear the rational-function denominators in `P` and expand
every polynomial coefficient into coordinate monomials `z^alpha`.  After collecting equal terms,
one obtains a nontrivial finite `C`-linear relation among distinct monomials (9), contradicting one
of the determinants (10).

### 2. Every determinant can be made nonzero

Fix `S`.  Only finitely many labels and jet orders occur.  Regard the `M_i` as distinct ordinary
monomials in the coordinate variables `z` and finitely many independent jet variables `y`.  They
are linearly independent polynomials.  The elementary evaluation lemma therefore gives `q` pairs

```text
(x_j,y_j),  1<=j<=q,                                       (11)
```

for which the evaluation matrix `(M_i(x_j,y_j))_(j,i)` is nonsingular.  The points may moreover be
chosen so that

```text
sigma_lambda(x_j) != sigma_mu(x_k)                          (12)
```

whenever the two occurrences `(lambda,j)` and `(mu,k)` are distinct.  Indeed every forbidden
equality is a proper affine subvariety: equality on an open set would force both the row points and
the affine maps to coincide.  Removing finitely many such subvarieties leaves a nonempty Zariski
open set, and a nonzero evaluation determinant cannot vanish on that whole set.

For fixed `lambda`, the affine chain rule sends the finite jet of `f` at
`sigma_lambda(x_j)` invertibly to the finite jet of `f o sigma_lambda` at `x_j`, because
`A_lambda` is invertible.  Hence the target jet data `y_j` prescribe consistent arbitrary finite
jets of `f` at the pairwise distinct points in (12).

Multivariate Hermite interpolation now produces a polynomial `f_S in C[z_1,...,z_d]` with exactly
those jets.  One algebraic proof is the Chinese remainder isomorphism

```text
C[z]/intersection_p m_p^(N+1)  ->  product_p C[z]/m_p^(N+1), (13)
```

for the finitely many distinct packet points `p=sigma_lambda(x_j)`.  Consequently

```text
Delta_S(f_S)!=0.                                            (14)
```

Thus `Delta_S` is a nonzero continuous polynomial functional on `O_d`: it is a polynomial in
finitely many continuous derivative-evaluation maps.

### 3. Baire chooses one source for every finite packet

The nonvanishing set

```text
U_S={f in O_d:Delta_S(f)!=0}                                (15)
```

is open.  It is dense.  More generally, the zero set of a nonzero continuous complex polynomial
on a topological complex vector space has empty interior.  Given a centre `g`, if the polynomial
vanished on every line `g+t h`, it would vanish everywhere; on a line where it is nonzero it has
only finitely many zeros, so arbitrarily small perturbations leave the zero set.

The Frechet space `O_d` is complete and hence Baire.  Therefore

```text
R=intersection_S U_S                                       (16)
```

is dense `G_delta`.  Step 1 converts (16) into (6), proving the theorem. `QED`

## Linear-operator matroid corollary `[PROVED HERE]`

Assume now that the distinct maps form a countable translation action and commute with the partial
derivatives.  Put `S=C[partial_1,...,partial_d]`.  For finitely supported rows

```text
P_i=sum_lambda L_(i,lambda)(partial) T_lambda,  L_(i,lambda) in S, (17)
```

and `f in R`, one has

```text
dtrdeg_K K< P_1 f,...,P_m f >_partial
 =rank_(C(partial_1,...,partial_d)) (L_(i,lambda)).          (18)
```

To prove (18), treat the distinct translates as differential indeterminates, which the theorem
allows.  Row reduction over the fraction field `C(partial)` makes a maximal independent row family
part of an invertible linear differential change of variables after clearing finitely many
nonzero operator denominators.  Such denominators give differential-algebraic extensions in both
directions and do not change differential transcendence degree.  The independent rows therefore
contribute exactly their operator rank, while every remaining row is differentially algebraic over
them.  This proves (18).

Hence the theorem controls not only raw translates but the full nonlinear differential matroid of
all finite constant-coefficient observations of the orbit.

## Carrier generalization and the exact quasi-Abelian boundary

The proof used only one analytic property of `O(C^d)`:

```text
every finite point packet admits arbitrary finite jet interpolation.        (19)
```

The same proof applies verbatim to a Baire space of sections of a line bundle when its finite jet
maps are all surjective, using ratios of two sections and clearing the finite evaluation
denominators.  Therefore (19) is a sufficient geometric law for complete HT orbit freedom.

For noncompact quasi-Abelian varieties, Abe proves point separation and tangent separation for
sections of an ample automorphic factor, but the required all-order interpolation in one fixed
section space is not a published consequence.  This is now the exact boundary of the stronger
quasi-Abelian classification: generalized Riemann relations control existence; all-order packet
interpolation would control complete HT freedom.

## RH-facing constraint

Prime logarithms act by distinct translations.  The theorem says that an unconstrained
jet-complete analytic carrier assigns one full differential transcendence direction to every
distinct prime-translation frame.  Thus an RH-bearing carrier cannot obtain its arithmetic content
from hypertranscendence or translation distinctness alone.  It must positively supply a coherent
**packet defect**: source-defined determinant constraints which survive every finite prime packet
and sew the Euler and functional-equation faces.

For primes `p<=N`, the known horizontal crossover at `epsilon asymp 1/log N` sharpens this demand.
The selector cannot be a fixed-width or cutoff-only defect.  Its packet constraints must persist
cofinally through the `1/log N` layer and converge by a zero-preserving or quantized sewing law.
In route language:

```text
generic HT capacity = free prime frames;
RH information      = stable arithmetic packet defect selecting one nongeneric carrier.  (20)
```

This is a positive necessity statement about what a successful HT-based RH route must construct.

## Novelty and significance audit

Parent ingredients are Baire category, multivariate Hermite interpolation, the affine chain rule,
and elementary differential algebra.  The search boundary includes hypercyclic translation and
composition operators, generic algebras of entire functions, functional transcendence of special
functions, and differential/difference Galois theory.  The searches performed so far found
function-specific algebraic-independence theorems and generic hypercyclicity, but not the residual
all-derivative affine-orbit theorem, its exact collision matroid, or the operator-rank formula (18).

The theorem is not yet assigned a final novelty verdict.  Its provisional significance is
`75/100` **only if** exact-formulation searches and specialist audit confirm that the residual
functional-transcendence statement is absent.  The reason for that score is the combination of:

- one source simultaneously liberates every finite derivative packet of any prescribed countable
  affine action;
- the theorem gives an exact matroid, not merely existence of HT examples;
- the proof isolates a portable geometric criterion, all-order packet interpolation;
- the RH consequence identifies the missing selector as a stable arithmetic packet defect rather
  than another generic HT construction.

## Exact Lean boundary

No analytic part of this theorem is currently formalized.  Stage 3 requires unconditional Lean
definitions and proofs of:

1. finite multivariate jet/Hermite interpolation;
2. the nonzero evaluation-determinant lemma for linearly independent monomials;
3. nonzero continuous polynomial functionals having dense nonvanishing locus;
4. the countable Baire intersection in `O(C^d)` or an equivalent complete coefficient model;
5. conversion of decorated-monomial independence to differential algebraic independence;
6. the operator-rank corollary (18).

The card cannot move to Stage 3 on the strength of a finite combinatorial surrogate.

## Gates

- [x] exact stronger law stated
- [x] coefficient-uniform determinant reduction proved
- [x] finite affine jet packet separated by Hermite interpolation
- [x] one source selected for every countable packet by Baire category
- [x] collision differential matroid identified
- [x] constant-coefficient operator-rank corollary proved
- [x] positive RH packet-defect consequence stated
- [x] complete paper proof
- [ ] exact-formulation primary-literature audit
- [ ] independent specialist proof audit
- [ ] complete unconditional Lean formalization before Stage 3
