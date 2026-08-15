# Fixed-divisor full-complex translation freeness

- **ID:** `fixed-divisor-full-complex-translation-freeness`
- **Stage:** 3-formalized / needs independent audit
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

**Complete, unconditional, axiom-clean** (`[propext, Classical.choice, Quot.sound]`).  The capstone
is `GaloisForLFunctions.HTGeometry.fixedDivisor_fullTranslationFreeness_denseResidual` in
`formal/GaloisForLFunctions/HTGeometry/FixedDivisorTranslationFreeness.lean`; see the assembly
section below for the module chain.

## Gates

- [x] 0 -> 1: exact full-complex theorem, codimension mechanism, proof architecture, and route scope
- [x] 1 -> 2: complete unconditional paper proof; retained in `needs-audit` pending independent review
- [x] 2 -> 3: complete unconditional claim formalized in Lean
- [ ] independent specialist proof and novelty audit (human gate; not a formalization item)

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

The passage to the complex jet coordinates is in the same module.  `rePoly` and `imPoly` take the
coefficientwise real and imaginary parts of a polynomial with complex coefficients
(`eval_rePoly`, `eval_imPoly`, `rePoly_ne_zero_or_imPoly_ne_zero`), `complexSplitSubst` is the
injective substitution `x_j ↦ x_{inl j} + i·x_{inr j}` (`complexSplitSubst_ne_zero`,
`eval_complexSplitSubst`), and `realifyPoint` reads a real point of the doubled index set as a
complex point, Lipschitz with constant `2` (`lipschitzWith_realifyPoint`).  Hence

> **`dimH_setOf_complex_eval_eq_zero_le`.**  For a nonzero `Q ∈ ℂ[x_v : v ∈ κ]` with `κ` finite,
> `dimH {z : κ → ℂ | eval z Q = 0} ≤ 2·card κ - 1`.

This is the finite-dimensional core of steps 3–5, in the coordinates the card uses.  What the card
still needs on top of it is the incidence bookkeeping — the rank-defect locus as a union over the
projective coefficient parameter, with one nontrivial equation per active evaluation row — and the
Hermite-interpolation submersion that converts that codimension into a bound on the gauge
parameter.

## Lean progress — the parametric codimension calculus

Hausdorff dimension alone does not survive the parametric step: an upper bound for `dimH (A × B)` in
terms of `dimH A` and `dimH B` is false in general, and the shift parameter `h` has to be crossed
with the rank-defect locus.  `formal/GaloisForLFunctions/HTGeometry/LipschitzCoveredDimension.lean`
(umbrella-wired, axiom-clean) replaces the dimension by a property that does survive products.

`IsLipschitzCovered k s` says that `s` is contained in a countable union of Lipschitz images of
subsets of `ℝ^k`.  Its calculus:

- `IsLipschitzCovered.dimH_le` — it implies `dimH s ≤ k`;
- `IsLipschitzCovered.mono`, `.union`, `.iUnion`, `.iUnion_countable`, `isLipschitzCovered_empty`;
- `IsLipschitzCovered.image` — stable under Lipschitz images, so it transports along any
  parametrisation;
- `isLipschitzCovered_pi` — every subset of a coordinate space of dimension at most `k`;
- **`IsLipschitzCovered.prod`** — `k` and `l` give `k + l`, via the `1`-Lipschitz surjection
  `ℝ^{k+l} → ℝ^k × ℝ^l`; this is the step Hausdorff dimension cannot supply;
- **`IsLipschitzCovered.piFin`** — hence a finite product of row sets is covered in the sum of their
  dimensions, which is the shape of the rank-defect locus `∏_a Z_a ⊆ X^N`;
- **`dense_compl_of_isLipschitzCovered`** — a bad parameter set covered in dimension `< dim_ℝ V` has
  dense complement.  This is the codimension replacement for parametric transversality, and it is
  exactly the hypothesis that `BaireGenericAvoidance` consumes.

The zero-set input is upgraded from a dimension bound to a parametrisation:
`lipschitzOnWith_invFunOn` and `subset_image_invFunOn` turn the antilipschitz projection of the
previous section into an actual Lipschitz chart, a countable subcover
(`TopologicalSpace.isOpen_iUnion_countable`) makes it global on the noncritical part, and induction
on the total degree gives

> **`isLipschitzCovered_setOf_eval_eq_zero`.**  The zero set of a nonzero `P ∈ ℝ[x_v : v ∈ ι]` is
> covered by countably many Lipschitz images of subsets of `ℝ^{card ι - 1}`.

With `IsLipschitzCovered.piFin` this gives the codimension of a product of `N` row conditions
directly.  In the exact shape of step 3 that is

> **`isLipschitzCovered_pi_zeroSets`.**  If on `J` of the `N` independent copies of the row jet space
> a nonzero polynomial equation is imposed, the solution set is covered in dimension
> `N · card ι − card J`.

This is inequality `(1)` of the card, in real codimension: since `N` is free, taking `N` past
`q + card J`-many rows makes the codimension exceed the real dimension `2m` of shift-configuration
space, and `dense_compl_of_isLipschitzCovered` converts that into density of the good gauges.  What
remains is the *fibered* form — the charts of the individual row conditions have to forget a jet
coordinate rather than a coefficient coordinate, so that the incidence set over the projective
coefficient parameter is a fiber product of charts over a common base — together with the Hermite
interpolation that makes the jet map a submersion.

## A stratification-free replacement for step 3: disjoint determinant blocks

The incidence variety over `P^(R-1)` in step 3 is what forces the fibered form.  It can be removed
entirely, at no cost in the conclusion.

Linear dependence of the `R` supported functions implies that **every** `R × R` minor of the
evaluation matrix vanishes.  Partition the `N` evaluation rows into `floor(N/R)` **disjoint** blocks
of `R` rows.  The minors of distinct blocks involve **disjoint** groups of row-jet variables, so the
rank-defect locus is contained in a decoupled system

```text
B  subset  {x in X^N : det_b(x)=0 for every block b},
```

one nonzero polynomial equation per block, on independent copies of `X`.  That is exactly the shape
of `isLipschitzCovered_pi_zeroSets`, so

```text
IsLipschitzCovered (N·dim_R X - floor(N/R)) B,
```

and choosing `N = R·(2m+1)` makes the codimension `2m+1`, strictly larger than the real dimension
`2m` of `Conf_m(C)`.  No projective parameter, no incidence variety, no Whitney stratification, and
no fibered covering calculus are needed.

The one input this needs is that each block determinant is a nonzero polynomial.  Treating the
evaluation points `z_a` as variables as well,

```text
det_b = sum_sigma sgn(sigma) prod_s z_s^(k_(sigma(s))) x_s^(alpha_(sigma(s))),
```

and two permutations produce the same monomial in `(z, x)` exactly when
`M_(sigma(s)) = M_(tau(s))` for every `s`, i.e. exactly when `sigma = tau`, because the `R`
expanded differential monomials are distinct.  So no cancellation occurs and `det_b` is a nonzero
polynomial in `(z, x)`; a choice of evaluation points off its zero set — which exists because a
nonzero polynomial does not vanish identically — makes `det_b(z, ·)` a nonzero polynomial in the
row jets.

With this replacement the remaining formalization of the theorem is:

1. distinct monomials give a nonzero block determinant (no-cancellation, above);
2. a choice of evaluation points making every block determinant nonzero in the jets;
3. `isLipschitzCovered_pi_zeroSets` on the disjoint blocks, then
   `dense_compl_of_isLipschitzCovered`;
4. Hermite interpolation making the polynomial-to-jet map a local diffeomorphism, to transport the
   bound from jet coordinates to gauge coordinates;
5. the reduction of an arbitrary differential relation over `C(z)` to a finite monomial support, and
   the countable Baire assembly, which `BaireGenericAvoidance` already provides.

### Lean progress — steps 1–3 of that route are closed, and the transport is in place

1. **The block determinant is a nonzero polynomial.**  Already corpus-owned:
   `GaloisForLFunctions.HTGeometry.blockMonomialMatrix_det_ne_zero` (`BlockMonomialDeterminant.lean`)
   proves exactly the no-cancellation statement — distinct monomials evaluated on disjoint variable
   blocks give a determinant whose permutation terms are pairwise distinct monomials, because the
   block exponent recovers the permutation (`blockExponent_injective`).  Taking the monomial variable
   type to be the evaluation-point slot together with the jet slots puts the card's
   `M_j(z,Y) = z^(k_j) Y^(alpha_j)` in exactly that form.

2. **A choice of evaluation points.**  `exists_partial_specialization_ne_zero`
   (`PolynomialZeroSetDimension.lean`): a nonzero polynomial stays nonzero after specializing any
   subset of its variables at a point where it does not vanish.  Applied to the block determinant
   with the evaluation-point variables specialized, this produces the `z_a` for which every block
   determinant is a nonzero polynomial in the row jets.

3. **The codimension.**  `isLipschitzCovered_pi_complex_zeroSets`
   (`LipschitzCoveredDimension.lean`): `B` independent complex row equations cut the real dimension
   by `B`.  With `J = univ` and one block determinant per block this is the card's `(1)`, in the
   form the Baire step consumes:
   `IsLipschitzCovered (B·(2 dim_C X) − B)` for the rank-defect locus, and
   `dense_compl_of_isLipschitzCovered` turns `B > 2m` into density of the good gauges.
   The complex layer rests on `isLipschitzCovered_setOf_complex_eval_eq_zero` and
   `isLipschitzCovered_univ_complex`.

4. **The transport from jets to gauges.**  `IsLipschitzCovered.preimage`: if every point of the
   parameter space has a neighbourhood on which the jet map admits a Lipschitz left inverse, the
   preimage of a covered set is covered in the same dimension.  The Hermite half of that hypothesis
   is corpus-owned and is even linear: `windowJetMap` is a linear isomorphism from the degree window
   `[N, N + K·m)` onto the jets of order `< m` at `K` distinct nonzero nodes
   (`windowJetMap_injective`, `windowJetMap_surjective`, `exists_windowLin_jets`, in
   `HighDegreeJetFreedom.lean`).

What is left is the analytic half of step 4 — the triangular local biholomorphism from the jets of
`g` to the jets of `W exp(g)` at a point where `W` does not vanish — together with the monomial
bookkeeping of step 5 (a differential relation over `C(z)` reduces to a finite expanded support) and
the countable Baire assembly, which `BaireGenericAvoidance` already supplies.

### The analytic half of step 4 needs only Leibniz, not Faa di Bruno

The card describes the jet map `p |-> j^r(W exp(g_0+p))` as triangular with diagonal the function
value.  Written that way it needs the Bell/Faa di Bruno expansion of `(exp g)^(l)`.  It does not:
only the *derivative* of the jet map is needed for the inverse function theorem, and that derivative
is linear with no exponential in it.

Along `p_t = p + t q`,

```text
d/dt|_0  W exp(g_0 + p + t q) = W exp(g_0+p) · q = F · q,
```

so the differential of `Psi_c : c |-> (j^r_{z_a+h_i} F)` is

```text
dPsi(c) : delta |-> ( j^r (F · windowLin delta) ).
```

That is the composition of two linear isomorphisms:

* `windowLin`/`windowJetMap`, which is a linear isomorphism from the degree window onto the jets at
  the nodes (`windowJetMap_injective`, `windowJetMap_surjective`, corpus-owned);
* the Leibniz map `j^r q |-> j^r (F q)` at one node, which is triangular in the jet order with
  constant diagonal `F(node)`, hence invertible exactly when `F` does not vanish at the node — which
  is how the evaluation points were chosen (`W != 0` there, and `exp` never vanishes).

So the only analytic inputs are the Leibniz rule for a finite jet, joint smoothness of
`c |-> j^r_{z}(W exp(g_0 + windowLin c))`, and mathlib's inverse function theorem; the hypothesis of
`IsLipschitzCovered.preimage` then holds and the codimension bound transports from jet coordinates
to gauge coordinates.  No Bell polynomials, no Whitney stratification, and no parametric
transversality theorem enter the formalization.

The Leibniz half is formalized in `formal/GaloisForLFunctions/HTGeometry/LeibnizJetMatrix.lean`
(umbrella-wired, axiom-clean):

```text
leibnizJetCoeff, leibnizJetMatrix
leibnizJetMatrix_blockTriangular
det_leibnizJetMatrix              : det = (value of the fixed factor)^m
det_leibnizJetMatrix_ne_zero      : invertible exactly when that value is nonzero
iteratedDeriv_mul_eq_leibnizJetMatrix
                                  : j^l (F·q) = sum_j (Leibniz matrix)_{l,j} · j^j q
```

so multiplication by the source is a linear isomorphism on jets of any finite order at any point
where the source does not vanish.  Composed with the corpus's `windowJetMap` isomorphism this is the
full derivative `dPsi(c)`, and the only remaining input for step 4 is the joint smoothness of the
parametrised jet together with mathlib's inverse function theorem.

### Lean progress — the exponential jet polynomials, and smoothness of the parametrised jet

The one remaining input of step 4 is that `c |-> j^r_{z_a}(W exp(g_0 + windowLin c))` is smooth with
invertible derivative.  Both follow from an explicit formula for the jets of an exponential
composite, now formalized in
`formal/GaloisForLFunctions/HTGeometry/ExpJetPolynomial.lean` (umbrella-wired, axiom-clean):

```text
jetShiftDeriv                     -- the derivation X_j |-> X_(j+1) of the jet ring
hasDerivAt_eval_jets              -- differentiating a polynomial in the jets applies that shift
expJetPoly                        -- B_0 = 1,  B_(l+1) = D B_l + B_l · X_1
iteratedDeriv_exp_comp            -- (exp o p)^(l)(x) = exp(p x) · eval (jets of p at x) B_l
differentiable_iteratedDeriv_of_entire
```

together with the triangularity that makes the jet map a polynomial shear:

```text
jetSub l                          -- the subalgebra generated by X_1, ..., X_l
jetShiftDeriv_mem_jetSub          -- the shift raises the level by one
pderiv_eq_zero_of_mem_jetSub      -- a derivative above the level kills that subalgebra
expJetPoly_eq_X_add               -- B_(l+1) = X_(l+1) + (element of jetSub l)
pderiv_expJetPoly_self            -- so the leading coefficient is 1
pderiv_expJetPoly_eq_zero         -- and B_l does not involve any jet variable above order l
```

Consequently the parametrised jet factors as

```text
c  --windowJetMap-->  jets of p   --E-->  jets of exp(p)   --Leibniz-->  jets of W exp(g_0) exp(p),
```

the first and third arrows being linear isomorphisms (`windowJetMap_injective/_surjective`,
`det_leibnizJetMatrix_ne_zero`), and the middle one being
`E(w)_l = exp(w_0) · eval w B_l`, whose Jacobian is triangular with constant diagonal `exp(w_0)`
by `pderiv_expJetPoly_self` and `pderiv_expJetPoly_eq_zero`, hence invertible everywhere.  So `Psi`
is smooth with everywhere invertible derivative, mathlib's inverse function theorem supplies the
local Lipschitz inverses, and `IsLipschitzCovered.preimage` transports the codimension bound to the
gauge parameter.

What remains is the assembly: the explicit composite `Psi`, its derivative computation from the two
triangular matrices, and the step-5 bookkeeping reducing a differential relation over `C(z)` to a
finite expanded monomial support.

## Lean assembly — the theorem is closed

The route that was actually formalized replaces the projective incidence variety, the Whitney
stratification and the parametric transversality theorem by the corpus's own compact-patch
codimension calculus, which already carries the same content in a stratification-free form:
`expandedEvaluation_compactPatchAvoidance_dense` (an in-tree unconditional theorem) turns a smooth
parametrised jet family whose probe derivative is onto into density of the rank-defect-avoiding
parameters, as soon as the real dimension of shift-configuration space is below the codimension
supplied by `expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional`.

What the card had to add was the analytic half for a gauged source `W·exp(g)` with a prescribed
divisor, and the gauge space itself.

**The gauge space** (`EntireGaugeSpace.lean`).  `EntireGauge` is the compact-open space of entire
functions, a closed complex subspace of `C(ℂ, ℂ)` by the Weierstrass theorem
(`isClosed_differentiable`), hence completely metrizable and `BaireSpace`.  Differentiation acts
continuously on it (`continuous_gaugeDeriv`, again Weierstrass), so every jet coordinate
`(g, z) ↦ g^{(k)}(z)` is jointly continuous (`continuous_gaugeJetEval`).

**Jets of an exponential** (`ExpJetJacobian.lean`).  Truncating the exponential jet polynomials
`B_l` at order `m` gives `expJetMap m : v ↦ (exp(v_0)·B_l(v))_{l<m}`.  Its Jacobian is triangular
with constant diagonal `exp(v_0)`: `B_l` involves no zeroth jet variable
(`pderiv_zero_expJetPoly`), none above level `l` (`pderiv_expJetPoly_eq_zero`), and has coefficient
`1` at level `l` (`pderiv_expJetPoly_self`).  Hence `det_expJetJacobian = exp(v_0)^m ≠ 0` and
`surjective_fderiv_expJetMap`: the exponential jet map is a submersion everywhere.  No Bell or
Faà di Bruno expansion is used, and no inverse function theorem.

**Jets of a gauged source** (`GaugeCarrierJets.lean`).  `iteratedDeriv_gaugeCarrier` is the master
formula
`j^r_ζ(W·e^g) = leibnizJetMatrix(j^·_ζ W) · expJetMap(j^·_ζ g)`,
obtained from `iteratedDeriv_mul_eq_leibnizJetMatrix` and `iteratedDeriv_exp_comp`.

**The probe** (`GaugeProbeJetFamily.lean`, `GaugeExpandedJetFamily.lean`).  Adding a polynomial
window to the exponent gives a finite-dimensional chart through any gauge.  Its derivative is the
composite of three surjections — `surjective_probeJetLin` (the corpus's `windowJetMap`
isomorphism at distinct nonzero nodes), `surjective_blockJetCLM` of the exponential Jacobians, and
`surjective_leibnizBlockLin` (invertible exactly where `W` does not vanish) — so
`surjective_fderiv_gaugeExpandedProbeJetFamily`.  Joint smoothness in the probe and the shift is
`contDiff_gaugeProbeJetPacket`.  `compact_gaugeExpandedActualEvaluation_avoidance_dense` then
transports finite-dimensional density to density in the gauge space along the continuous chart
`windowGaugeChart`.

**Admissible rows** (`GaugeRowPacketAtlas.lean`).  A row packet is admissible for a shift when the
whole row-by-shift node family is collision-free, nonzero, and off the divisor; all three are open
(`gaugeGoodCombinedRowPacketSet_isOpen`), and a translate of any collision-free packet by a point
outside a countable set achieves them, because the zero set of a nonzero entire function is
countable (`exists_translate_off_divisor`).  Compactness gives a finite atlas.

**The assembly** (`FixedDivisorTranslationFreeness.lean`).

```text
compact_injectiveShiftPatch_has_dense_completeAtlas_gauge
    -- one open dense set of gauges per compact shift patch
global_injectiveShifts_gaugeExpandedFullRankWitness_dense_residual
    -- sigma-compactness of the collision-free shift space, then Baire
allFinitePatterns_gaugeExpandedFullRankWitness_dense_residual
allFinitePatterns_gaugeExpandedRelationFree_dense_residual
    -- countably many finite differential patterns, then Baire again
not_familyDifferentiallyAlgebraicOn_gaugeCarrier_of_relationFree
    -- descent from pattern coefficients to a literal differential relation
fixedDivisor_fullTranslationFreeness_denseResidual        -- the theorem
exists_gauge_fixedDivisor_fullTranslationFreeness         -- existence form
exists_pair_fixedDivisor_fullTranslationFreeness          -- divisor blindness
analyticOrderAt_gaugeCarrier                              -- the divisor is unchanged
```

The capstone reads: for every nonzero entire `W` the set of entire gauges `g` for which every
finite family of distinct complex translates of `W·exp(g)` satisfies no algebraic differential
relation over the coordinate is **dense and residual** in the compact-open gauge space, every
`W·exp(g)` is entire, and `analyticOrderAt (W·exp g) = analyticOrderAt W` at every point, so the
divisor is exactly that of `W`.

The three earlier sections of this log (`PolynomialZeroSetDimension.lean`,
`LipschitzCoveredDimension.lean`, `LeibnizJetMatrix.lean`, `ExpJetPolynomial.lean`,
`ExpLocalInverse.lean`) remain in the tree as an independent, self-contained Hausdorff-dimension
and Lipschitz-covering calculus for polynomial zero sets; they are not on the critical path of the
proof above, which routes the codimension through the corpus's own rank-defect stratification
instead.
