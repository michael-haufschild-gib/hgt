# Fixed-divisor full-complex translation freeness

- **ID:** `fixed-divisor-full-complex-translation-freeness`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; uncountable translation orbit; divisor fibers
- **Statement:** For every nonzero entire function `W`, a comeager set of zero-free gauges
  `exp(g)` makes *every* finite family of distinct complex translates of `W exp(g)`
  differentially algebraically independent over `C(z)`.  Thus every entire divisor supports the
  same free differential matroid for the full uncountable complex translation orbit.

## Medalist lens

The countable-shift theorem is a Baire bookkeeping bridge.  It does not control exceptional shifts
outside the named countable set.  The nontrivial question is whether an arbitrary complex shift can
create an isolated differential relation.

The replacement for countability is codimension.  A relation among `R` expanded differential
monomials forces a rank defect at every evaluation point.  Evaluating at sufficiently many points
makes the defect locus have codimension larger than the finite-dimensional configuration space of
the shifts.  Parametric jet transversality then removes *all* shift parameters simultaneously.

## Theorem `[PROVED HERE]`

Let `W` be a nonzero entire function.  For `g in O(C)`, define

`F_g(z)=W(z) exp(g(z))`.

There exists a comeager subset `G_full(W) subset O(C)` such that for every `g in G_full(W)`, every
integer `m>=1`, every tuple of pairwise distinct complex numbers `h_1,...,h_m`, and every nonzero
differential polynomial

`P in C(z){Y_1,...,Y_m}`,

one has

`P(T_(h_1)F_g,...,T_(h_m)F_g) != 0`.

Equivalently, the uncountable family

`{T_h F_g : h in C}`

is differentially algebraically independent over `C(z)`.

Every `F_g` has exactly the divisor of `W`.  Hence every locally finite effective divisor on `C`
supports continuum many entire functions whose full complex translation orbit has the maximal
differential-algebraic matroid.

## Proof

### 1. One finite differential support

Fix `m`, a jet order `r`, and a finite support of `R` distinct expanded differential monomials

`M_j(z,Y)=z^(k_j) prod_(i=1)^m prod_(ell=0)^r Y_(i,ell)^(alpha_(j,i,ell))`,

`1<=j<=R`.

Put `q=max_j k_j` and let

`Conf_m(C)={(h_1,...,h_m):h_i!=h_j for i!=j}`.

It is enough to prove that generically, for every `h in Conf_m(C)`, the `R` entire functions

`M_j(z, ((T_(h_i)F_g)^(ell))_(i,ell))`

are linearly independent over `C`.  Clearing rational denominators and expanding polynomial
coefficients reduces every differential relation over `C(z)` to one such finite support.

### 2. Local shift patches and regular evaluation points

Fix `h^0 in Conf_m(C)`.  Choose as many distinct evaluation points `z_1,...,z_N` as needed so that
all points

`z_a+h_i^0`, `1<=a<=N`, `1<=i<=m`,

are pairwise distinct and avoid the zero set of `W`.  By shrinking to a relatively compact
neighborhood `U` of `h^0` in `Conf_m(C)`, both properties remain true for every `h in U`.

For one row, the available jet space is

`X=(C^x)^m times C^(mr)`:

the value of each shifted `F_g` is nonzero at the chosen regular point, while every positive jet is
free.  The total evaluation-jet space is `X^N`.

### 3. Codimension amplification for the rank-defect locus

For fixed distinct `z_1,...,z_N`, let `B_(S,z) subset X^N` be the algebraic set of row jets
`x=(x_1,...,x_N)` for which the `N by R` matrix

`A(x)_(a,j)=M_j(z_a,x_a)`

has rank less than `R`.

Consider the incidence set

`I={(x,[c]) in X^N times P^(R-1) :`

`       sum_j c_j M_j(z_a,x_a)=0 for every a}`.

For fixed `[c]`, write

`P_c(z,Y)=sum_j c_j z^(k_j)Y^(alpha_j)`.

The set of `z` for which `P_c(z,Y)` is identically zero as a polynomial in `Y` has at most `q`
elements.  Indeed, after grouping equal `Y`-monomials, at least one nonzero coefficient polynomial
in `z` remains, and its degree is at most `q`.

Consequently at least `N-q` rows impose a nonzero polynomial equation on their independent copy of
`X`.  Each such row lowers complex dimension by at least one.  Therefore

`dim_C I <= N dim_C X -(N-q)+(R-1)`

and projection to `X^N` gives

`codim_C B_(S,z) >= N-q-R+1`.                              (1)

Choose

`N>m+q+R-1`.

Then every irreducible component of `B_(S,z)` has complex codimension strictly larger than `m`, the
complex dimension of `Conf_m(C)`.  Fix a Whitney stratification of this algebraic set; every stratum
has the same strict codimension bound.

### 4. The universal jet map is a submersion

Fix any `g_0 in O(C)`.  Let `V` be the finite-dimensional vector space of polynomials of degree
less than `Nm(r+1)`.  Define

`Psi: V times U -> X^N`

by sending `(p,h)` to the jets through order `r` of

`F_(g_0+p)=W exp(g_0+p)`

at all points `z_a+h_i`.

For each fixed `h in U`, Hermite interpolation says that

`p |-> (j^r_(z_a+h_i)p)_(a,i)`

is onto the product of the `Nm` jet spaces.  At a point where `W!=0`, the map from the jet of
`g_0+p` to the jet of `W exp(g_0+p)` is triangular, with nonzero diagonal coefficient equal to the
function value.  It is therefore a local biholomorphism onto `C^x times C^r`.

Thus the derivative of `Psi` in the polynomial direction is onto `T(X^N)` at every `(p,h)`.
The universal map `Psi` is a submersion and hence transverse to every stratum of `B_(S,z)`.

### 5. Parametric transversality removes every shift in the patch

The finite-dimensional parametric transversality theorem now says that a residual, in fact
full-measure, set of `p in V` makes the partial map

`Psi_p:U -> X^N`

transverse to every stratum of `B_(S,z)`.

By (1), each stratum has real codimension strictly larger than `2m=dim_R U`.  A transverse preimage
is therefore empty.  Hence

`Psi_p(U) intersect B_(S,z)=empty`.

For such a perturbation, the chosen evaluation matrix has rank `R` for every shift tuple in `U`, so
the supported monomials are linearly independent for every `h in U`.

Good perturbations are dense in the finite-dimensional space `V`.  They may therefore be chosen in
an arbitrarily small neighborhood of zero for the compact-open seminorms controlling any prescribed
neighborhood of `g_0`.  This proves density in `O(C)`.  Avoidance on a compact subset of `U` is open,
because the evaluation image is compact and the algebraic bad set is closed.

### 6. Countable exhaustion after the uncountable parameter is removed

For fixed `m` and support `S`, exhaust `Conf_m(C)` by countably many compact sets.  Cover each compact
set by finitely many patches of the form above.  The intersection of the corresponding open dense
sets of gauges is comeager and eliminates the support for every complex shift tuple.

Finally intersect over the countable collection of integers `m,r` and finite expanded-monomial
supports.  The resulting set is `G_full(W)`.  This proves the theorem.

### Formalization of the Baire passage

The topological backbone of steps 3–6 — that once each relation locus is shown to be nowhere dense
(closed with empty interior) in the Baire gauge space, the generic gauge avoids all countably many of
them — is formalized axiom-clean in `GaloisForLFunctions.BaireGenericAvoidance`:

```text
dense_setOf_forall_notMem_of_isNowhereDense :
  (forall n, IsNowhereDense (S n)) -> Dense {x | forall n, x notin S n}
dense_setOf_forall_notMem_of_isClosed_interior_empty :   -- cards' hypothesis form
  (forall n, IsClosed (S n)) -> (forall n, interior (S n) = empty)
    -> Dense {x | forall n, x notin S n}
exists_forall_notMem_of_isNowhereDense :                 -- nonempty gauge exists
  ... -> exists x, forall n, x notin S n
```

The comeager conclusion `G_full(W)` is the `Dense` set above with `S n` ranging over the enumerated
relation loci. The non-formal input is exactly the analytic hypothesis of steps 3–5 (codimension
amplification, submersion, parametric transversality) that each `S n` is closed with empty interior;
the passage to a dense/comeager avoidance set is then this pure-topology lemma.

## Attacks and boundaries

1. **Why the countable proof was insufficient.**  A relation can occur at an isolated irrational or
   nonreal shift while missing a chosen dense countable set.  Continuity does not repair exact
   algebraic dependence.
2. **Why codimension grows.**  One relation coefficient vector has only projective dimension
   `R-1`, while every additional active evaluation row costs one independent equation.  The fixed
   loss is `q+R-1`; the number of rows is unbounded.
3. **Why the divisor does not interfere.**  Each compact shift patch uses evaluation points avoiding
   the translated divisor.  No uniform evaluation set over all of configuration space is assumed.
4. **Why entire order is uncontrolled.**  Generic exponential gauges have unrestricted growth.
   The theorem does not preserve finite order, Euler products, positivity, or a canonical
   normalization.
5. **Why the theorem is not an RH proof.**  It proves orthogonality of divisor location and full
   transformal-differential freeness.  An RH-bearing law must use data outside this free field.

## Full-orbit divisor-blindness consequence

Choose two entire divisors, one supported on a designated critical line and another containing a
zero off that line.  The theorem produces entire functions `F_0,F_1` on those divisors such that
both full complex translation orbits are free differential families over `C(z)`.

Their generated differential-translation fields are isomorphic by the assignment

`(T_h F_0)^(n) |-> (T_h F_1)^(n)` for every `h in C`, `n>=0`.

Therefore the RH-type divisor predicate is not definable from the isomorphism class of the complete
full-complex differential-translation field, even when every translate and every derivative is
retained.  This strictly strengthens rational-gauge blindness and the countable-shift theorem.

## Exact route scope

The theorem excludes any implementation of Li, Weil, Hilbert--Polya, Connes, de Branges, or
Nyman--Beurling which claims that *full complex translation hypertranscendence itself*, or the
abstract differential-translation field it generates, supplies the missing zero selector.

It does not exclude the complete classical criteria.  Their positivity forms, Hilbert-space norms,
canonical products, spectral measures, and Euler normalization are not invariants of the free
differential-translation field.

## Novelty gate

- **Proof gate:** passes.  The incidence estimate was checked componentwise through its projective
  incidence variety; polynomial Hermite interpolation makes the universal jet map a submersion;
  standard finite-dimensional parametric transversality then gives empty preimages because every
  Whitney stratum has codimension greater than the shift-configuration dimension.
- **Significance gate:** provisionally passes.  The theorem removes the countability restriction and
  proves full uncountable transformal-differential freeness on every prescribed divisor.
- **Parent-theory gate:** open.  The mechanism combines finite Hermite interpolation, determinantal
  incidence geometry, and parametric transversality; it is not the direct Baire support count used
  by the predecessor bridge.
- **Literature gate:** preliminary exact searches found no theorem combining a prescribed complete
  divisor with differential algebraic independence for every finite tuple from the uncountable
  complex translation orbit.  Adjacent primary theories checked include van den Dries's DA
  interpolation genericity, Birkhoff/MacLane translation universality, hypercyclic algebras for
  convolution/composition operators, and Forstneric jet transversality for holomorphic maps from
  Stein manifolds.  A specialist MathSciNet/zbMATH and citation-chain audit remains required.
- **Rediscovery gate:** open.

No scientific-newness label is applied until all gates pass.

## Lean status

No Lean claim is made.  The complete theorem requires Baire category, algebraic codimension,
Whitney stratification, finite-dimensional parametric transversality, Hermite interpolation, and
holomorphic jet maps.  A partial finite-rank or polynomial lemma would not justify stage 3.

## Gates

- [x] 0 -> 1: exact full-complex theorem, codimension mechanism, proof architecture, and route scope
- [x] 1 -> 2: complete unconditional paper proof; retained in `needs-audit` pending independent review
- [ ] 2 -> 3: complete unconditional claim formalized in Lean
- [ ] 3 -> 4: publication-ready preprint with independent novelty review

## Log

- 2026-07-11 -- Replaced countable Baire bookkeeping by a configuration-space codimension theorem.
  Evaluation rows amplify rank-defect codimension beyond the shift-parameter dimension, and
  parametric Hermite transversality removes all complex shift tuples simultaneously while the
  divisor remains fixed.
- 2026-07-11 -- Completed the proof audit and preliminary literature search.  Exact prior art was
  not located, but scientific novelty remains unverified pending independent specialist review.

## Lean progress — the codimension engine: polynomial zero sets have Hausdorff dimension `n-1`

Step 5 of the proof removes the shift parameter by comparing the codimension of the rank-defect
locus with the dimension of shift-configuration space.  Formalized, that comparison is a Hausdorff
dimension count: mathlib's `dense_compl_of_dimH_lt_finrank` turns
`dimH (bad set of gauges) < dim_ℝ V` into the density that the Baire passage
(`GaloisForLFunctions.BaireGenericAvoidance`) consumes, and
`dimH_image_le_of_locally_lipschitzOn` transports the bound through the parametrisation.  The
missing quantitative input is the dimension of one rank-defect equation, i.e. of a polynomial zero
set.

`formal/GaloisForLFunctions/HTGeometry/PolynomialZeroSetDimension.lean` (umbrella-wired,
axiom-clean, `[propext, Classical.choice, Quot.sound]`) supplies it, for an arbitrary finite index
type:

> **`dimH_setOf_eval_eq_zero_le`.**  For a nonzero `P ∈ ℝ[x_v : v ∈ ι]` with `ι` finite,
> `dimH {x : ι → ℝ | eval x P = 0} ≤ card ι - 1`.

The proof needs no stratification and no implicit function theorem:

- `dimH_le_of_locally` — a Hausdorff dimension bound is local, by mathlib's `bsupr_limsup_dimH`;
- `hasDerivAt_mvPolynomial_eval_curve_real` — the chain rule for polynomial evaluation along a real
  curve, by induction on the polynomial;
- `exists_pderiv_inner_eq_zero` — between two zeros lying in a convex set, Rolle's theorem produces
  an interior point at which the gradient is orthogonal to their difference;
- `dist_le_of_zero_of_pderiv_bounds` — hence, on a region where one partial derivative is bounded
  below and all of them are bounded above, forgetting the corresponding coordinate is
  **antilipschitz** on the zero set;
- `dimH_regular_zeroSet_le` — so the noncritical part of the zero set has, by
  `AntilipschitzWith.le_dimH_image` and `Real.dimH_univ_pi`, dimension at most `card ι - 1`;
- `totalDegree_pderiv_lt`, `exists_pderiv_ne_zero` — the critical part lies in the zero set of a
  nonzero partial derivative of strictly smaller total degree, so induction on the total degree
  closes the bound.

This is the finite-dimensional core of steps 3–5.  What the card still needs on top of it is the
incidence bookkeeping — the rank-defect locus as a union over the projective coefficient parameter,
and the Hermite-interpolation submersion — and the passage from complex to real coordinates.
