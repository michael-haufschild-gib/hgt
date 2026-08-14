# Generic affine HT carriers have exactly the collision differential matroid

- **ID:** `affine-jet-packet-collision-completeness`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / GENERIC FUNCTIONAL TRANSCENDENCE LAW
- **Scientific status:** `[PROVED HERE] [LEAN-PARTIAL] [NOVELTY UNVERIFIED]`
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

The exact collision matroid is formalized in
`formal/GaloisForLFunctions/HTGeometry/AffineCollisionMatroid.lean`: it is the pullback of the free
matroid along the affine-frame map, its independent sets are precisely the frame-injective sets,
and its extended rank on every finite packet is the number of distinct frames.

`formal/GaloisForLFunctions/HTGeometry/AffineJetPacketCollisionCompletion.lean` proves the
countable Baire assembly from explicit defect loci and identifies every residual packet rank with
the rank of that actual mathlib matroid. It uses the existing `BaireGenericAvoidance.lean` and
`PolynomialEvaluationLemma.lean` infrastructure.

```text
AffineJetPacketCollisionInput
  -- countable determinant defects, their closed/empty-interior certificates, and the exact
  -- decorated-monomial-to-collision/operator-rank conversion
affineJetPacketCollision_denseResidual_exactMatroid
  -- the common avoidance set is dense residual; every member has rank `# image(sigma|E)` and the
  -- full constant-coefficient operator-rank law
affineJetPacketCollision_orbitRank_eq_collisionMatroid_eRk
  -- the residual packet rank is the extended rank of `affineCollisionMatroid frame`
affineDecoratedMonomials_exist_packet_det_ne_zero
  -- every finite linearly independent decorated-monomial family has a nonsingular sample packet
```

Those analytic parents are now constructed unconditionally; see the logs below and the companion
file `affine-jet-packet-collision-completeness-formalized.md`. The genuine determinant defects, the
escaping witness for every finite decorated pattern, the dense residual generic set, the conversion
from determinant avoidance to differential independence, and the constant-coefficient operator-rank
law are all in Lean with no added hypotheses beyond `d >= 1`, countability of the label set, and
noncollision of the affine frames.

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
- [x] actual collision matroid and its exact finite rank law formalized
- [x] Baire assembly and matroid-rank identification from explicit analytic jet-packet inputs
- [x] construct the multivariate entire-function, Hermite-interpolation, affine-chain-rule, and
  determinant-to-differential-independence parents unconditionally in Lean
- [x] constant-coefficient operator-rank law formalized

## Log — the exact remaining gap, and the route that closes it

A corpus audit shows the analytic parents are already built.  The source space, the continuous jet
observations, the affine chain rule, Hermite interpolation and the empty-interior law are all
present and unconditional:

| Module | What it supplies |
|---|---|
| `MultivariateEntireCompactOpen` | `MultivariateEntire d` (line-entire sources in `C(ℂᵈ,ℂ)`), closed, complete, `BaireSpace` |
| `MultivariateEntireFrechetRegularity` | line-entire + continuous ⟹ `AnalyticOnNhd` ⟹ `ContDiff ℂ ⊤` |
| `MultivariateEntireDirectionalJet` | `directionalJetEvalCLM` — continuous linear line jets |
| `MultivariateEntirePolarizedJet` | `polarizedJetEvalCLM = iteratedFDeriv`, `orderedPartialJetEvalCLM`, and **`polarizedJetEvalCLM_affinePullback`** (the exact affine chain rule) |
| `MultivariateMultiIndexJet` | `multiIndexJetEvalCLM`, **`exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary`** (Hermite jet surjectivity at distinct points) |
| `MultivariateHermiteCRT` | the CRT interpolation, `mvPolynomialOfFiniteJet` |
| `ContinuousPolynomialDefect` | **`interior_continuousLinearMap_mvPolynomial_zero_eq_empty_of_witness`** — one escaping source makes a polynomial defect nowhere dense |
| `MultivariateCoefficientPatternDeterminant` | `multivariateCoefficientPatternDeterminant`, its evaluation formula, and `exists_fullRank_multivariateExpandedMonomial_packet` |
| `CountableMultivariateAffineJetPattern` | the countable pattern code, the closed defect, and `multivariateAffinePatternResidualSet_dense_residual` |

The single missing object is

```text
witness : ∀ p : FiniteMultivariateAffineJetPattern Λ d, MultivariateAffinePatternWitness frame p
```

i.e. for each finite decorated pattern a choice of sample bases `x_1,…,x_q` and one entire source
whose observation makes the pattern determinant nonzero.  `defect_interior_empty` then follows from
`interior_continuousLinearMap_mvPolynomial_zero_eq_empty_of_witness`, and
`affineJetPacketCollisionInput_empty` in `DetectorAndPacketWitnesses` is only the degenerate
inhabitant, not the theorem.

### The route

1. **Vanishing transfer.**  If every `orderedPartialJetEvalCLM p word u` of length `n` vanishes then
   `iteratedFDeriv ℂ n u p = 0` (a continuous multilinear form vanishing on all coordinate tuples is
   zero: `Basis.ext_multilinear` on the Pi basis).  Composed with
   `polarizedJetEvalCLM_affinePullback` this gives: an order-`<m` jet-flat source at `σ(x)` has
   vanishing pulled-back observations `affineMultiIndexJetEvalCLM σ x α u` for `deg α < m`.
2. **Prescribing the observation.**  For each frame `i` and row `a` let `p_{i,a} = σ_i(x_a)`.  Take
   the one-point Taylor polynomial `H_{i,a}` carrying the desired jets at `x_a`, and set
   `F_{i,a} := H_{i,a} ∘ σ_i⁻¹`, again a polynomial.  Its coordinate jets at `p_{i,a}` depend only
   on the word multiplicity (`orderedPartialJetEvalCLM_mvPolynomial_eq_centered_coeff`), so Hermite
   at the **distinct** points `p_{i,a}` produces a single polynomial `P` matching all of them.  By
   step 1 applied to `u = P − F_{i,a}`, the observation of `P` is exactly the prescribed vector.
   No symmetric-tensor inverse and no Leibniz rule is needed.
3. **Choosing the base.**  The base must simultaneously make the pattern determinant nonzero and
   separate the packet points.  Each forbidden coincidence `σ_i(x_a) = σ_j(x_b)` is the zero locus
   of a degree-one polynomial in the base variables which is not identically zero (distinct frames
   for `i ≠ j`, injectivity of `σ_i` for `a ≠ b`, using `d ≥ 1`).  Multiplying the determinant
   polynomial by one nonzero coordinate of each coincidence and applying `exists_eval_ne_zero`
   yields one base satisfying everything at once.
4. **Assembly.**  Steps 2–3 give `MultivariateAffinePatternWitness`, hence
   `multivariateAffinePatternResidualSet_dense_residual` becomes unconditional, and the
   `AffineJetPacketCollisionInput` of the card is realized with the genuine defects.

Step 3 needs the noncollision hypothesis `Function.Injective frame` — exactly the card's relation
`(4)`; for a general labelled family it is applied after passing to the frame image, which is what
`affineCollisionMatroid` already records.

### Log — the witness is constructed; the Baire law is unconditional `[PROVED]`

Four new modules, all wired into `GaloisForLFunctions.HTGeometry` and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only).

`HTGeometry/AffineJetVanishingTransfer.lean`

- **`iteratedFDeriv_eq_zero_of_orderedPartialJetEvalCLM_eq_zero`** — a continuous multilinear form
  vanishing on every coordinate tuple is zero (`Module.Basis.ext_multilinear` on the Pi basis), so
  vanishing of all ordered coordinate jets of one order is vanishing of that iterated derivative;
- **`affineMultiIndexJetEvalCLM_eq_zero_of_flat`** — through `polarizedJetEvalCLM_affinePullback`,
  flatness to order `m` at `σ(x)` kills every mixed jet of `f ∘ σ` at `x` of total degree `< m`;
- **`affineMultiIndexJetEvalCLM_congr_of_orderedPartialJetEvalCLM_eq`** — hence the pulled-back
  observation depends only on the coordinate jets at the image point.

`HTGeometry/AffineJetPacketPrescription.lean`

- `affineCoordPolynomial`, `mvPolynomialAffineSubst`, **`multivariateEntireAffinePullback_mvPolynomial`**
  — composition with an affine automorphism is a substitution, so polynomial sources are stable
  under every frame;
- `degree_wordMultiplicity`;
- **`exists_mvPolynomial_affineMultiIndexJetEvalCLM_eq`** — one frame prescribes its own jet packet
  (one-point Taylor data pulled back through `σ⁻¹`);
- **`exists_mvPolynomial_affine_packet_prescribed`** — *affine jet packet surjectivity*: if the
  image points are pairwise distinct, one polynomial source realizes arbitrary mixed jets of every
  affine pullback at every packet point.  This is the analytic surjectivity the card needs, and it
  avoids symmetric-tensor inversion entirely: polynomial jets depend only on word multiplicity, so
  Hermite matching at the image points plus the flatness transfer already fixes the observation.

`HTGeometry/AffineFramePacketSeparation.lean`

- `coordDiffPoly`, **`exists_coordDiffPoly_ne_zero`** — a coincidence between two distinct packet
  occurrences is a nontrivial degree-one coordinate condition (distinct frames disagree somewhere;
  a single frame is injective, using `d ≥ 1`);
- **`exists_base_separating_and_eval_ne_zero`** — any prescribed nonzero polynomial in the base
  coordinates and the remaining variables has a nonvanishing point whose base separates the whole
  packet.

`HTGeometry/AffineJetPacketWitness.lean`

- `multivariateFullPatternDeterminant`, its evaluation formula, and
  **`multivariateFullPatternDeterminant_ne_zero`** — the decorated determinant with the base
  coordinates as further indeterminates is a nonzero polynomial;
- **`nonempty_multivariateAffinePatternWitness`** — every finite decorated pattern of a
  noncolliding affine family in dimension `≥ 1` has an escaping witness, i.e. exactly the object
  `MultivariateAffinePatternWitness` that `CountableMultivariateAffineJetPattern` left open.

`HTGeometry/AffineJetPacketResidual.lean`

- `affineJetPacketWitness`, `affineJetPacketGenericSet`, and
  **`affineJetPacketGenericSet_dense_residual`** — for a countable family of pairwise distinct
  affine automorphisms of `ℂᵈ`, `d ≥ 1`, the sources on which *every* finite decorated jet
  determinant is nonzero form a dense residual subset of `O(ℂᵈ)`.  No hypotheses beyond `0 < d`,
  `Countable Λ` and `Function.Injective frame`; the previous
  `affineJetPacketCollisionInput_empty` degenerate inhabitant is superseded.

Remaining for Stage 3: step 1 of the paper proof — the conversion of determinant avoidance into
differential-algebraic independence.  The target is

```text
∀ P : MvPolynomial (ι × (Fin d →₀ ℕ)) (MvPolynomial (Fin d) ℂ), P ≠ 0 →
  ∃ z, eval₂ (eval z) (fun q ↦ affineMultiIndexJetEvalCLM (frame (lab q.1)) z q.2 f) P ≠ 0
```

for `f` in the generic set and `lab` injective, together with the operator-rank corollary `(18)`.
The proof is the card's own: expand `P` into distinct decorated monomials `(α, m)`, build the
pattern with those exponents and a uniform order bound `N` exceeding every jet degree in the
support, transport the jet exponents along the injection
`⟨i, β⟩ ↦ (κ i, β) : (Σ i, MultiIndexBelow d N) ↪ ι × (Fin d →₀ ℕ)` by `Finsupp.comapDomain`, and
read the vanishing of the relation at the witness base points as a square linear system whose
matrix is the pattern determinant.  Invertibility forces every coefficient to vanish, i.e. `P = 0`.

### Log — determinant avoidance **is** differential independence `[PROVED]`

`HTGeometry/AffineJetDifferentialIndependence.lean` (wired, axiom-clean) closes step 1 of the paper
proof, i.e. equation `(6)`:

- `RelationJetVar d n`, `affineJetRelationValue` — the value of a differential relation with
  polynomial coefficients at a source and a point,
  `eval₂ (eval z) (fun (j, β) ↦ ∂^β (f ∘ σ_j) (z)) P`;
- `relationJetOrder`, `degree_lt_relationJetOrder` — a uniform order bound strictly above every jet
  degree occurring in the relation;
- `relationJetEmbedding`, `relationDecoratedSupport`, `mem_relationDecoratedSupport`,
  `relationDecoratedSupport_nonempty`;
- **`affineJetRelationValue_eq_sum`** — the coefficient-uniform reduction: every relation is the
  finite complex-linear combination of its distinct decorated monomials `z^α ∏ Y_{λ,β}^{e}`;
- `relationPattern` — those decorated monomials **are** a `FiniteMultivariateAffineJetPattern`
  (jet exponents transported by `Finsupp.comapDomain` along the bounded-jet embedding, distinctness
  recovered by `Finsupp.embDomain_comapDomain`);
- **`exists_affineJetRelationValue_ne_zero`** — for `d ≥ 1`, a countable family of pairwise
  distinct affine automorphisms, and any source in `affineJetPacketGenericSet`, every *nonzero*
  differential polynomial with polynomial coefficients has a point where its value at the pullbacks
  along distinct frames is nonzero.  The proof reads the vanishing of the relation at the witness
  base points as `M · c = 0` with `M` the pattern determinant matrix, so `det M ≠ 0` forces `c = 0`,
  i.e. `P = 0`.

Combined with `affineJetPacketGenericSet_dense_residual` this is exactly the card's theorem
`(5)`–`(6)`, unconditionally in Lean: a dense residual set of entire sources on which the pullbacks
along distinct affine frames are differentially algebraically independent.  Rational coefficients
are the same statement after clearing denominators, since `ℂ(z)` is the fraction field of `ℂ[z]`.

Rank `(7)` is `affineJetPacketCollision_orbitRank_eq_collisionMatroid_eRk` against
`affineCollisionMatroid`, already formalized.

### Open in Lean — the constant-coefficient operator-rank law `(18)`

The main law `(5)`–`(7)` is now closed unconditionally.  What is still missing in Lean is the
corollary `(18)`, and its exact remaining parents are known:

1. **Jet-of-jet composition.**  `partialDerivEntire v g := fun x ↦ fderiv ℂ g x v` lands back in
   `MultivariateEntire d`: `MultivariateEntire.analyticOnNhd` plus mathlib's `AnalyticOnNhd.fderiv`
   and `AnalyticAt.differentiableAt` give differentiability, and `lineEntire_of_differentiable`
   closes membership.  Then
   `orderedPartialJetEvalCLM x word g = orderedPartialJetEvalCLM x (Fin.init word)
     (partialDerivEntire e_{word (last)} g)`
   by `iteratedFDeriv_succ_apply_right` together with
   `ContinuousLinearMap.iteratedFDeriv_comp_left` for `L = ContinuousLinearMap.apply ℂ ℂ v`
   (the evaluation `L ↦ L v` commutes with `iteratedFDeriv`).  Iterating gives
   `∂^γ (∂^β g) = ∂^{β+γ} g` for the corpus jet observations, hence the row outputs
   `operatorRowValue L f i z = ∑_j ∑_β coeff β (L i j) · ∂^β (f ∘ σ_j) (z)`
   are entire and their own jets are `∑_j ∑_β coeff β (L i j) · ∂^{β+γ} (f ∘ σ_j)`.
2. **Linear forms are algebraically independent.**  A ℂ-linearly independent family of linear
   forms in a polynomial ring is algebraically independent; consequently the substitution
   `W_{i,γ} ↦ ∑_{j,β} coeff β (L i j) · Y_{j, β+γ}`
   is an injective algebra map, over `ℂ[z]` as well as over `ℂ`.  The hypothesis needed is exactly
   ℂ-linear independence of the family `{X^γ · L_{i,·}}_{i,γ}` in `ℂ[∂]^n`, which is precisely
   `ℂ[∂]`-linear independence of the rows `L_i` — the operator rank of `(17)`.
3. **Assembly.**  Independent rows: a nonzero differential relation among the outputs pulls back to
   a nonzero relation among the jets, contradicting `exists_affineJetRelationValue_ne_zero`.
   Dependent rows: a nonzero `ℂ[∂]`-relation `∑ M_i L_i = 0` gives the explicit vanishing relation
   `∑_i M_i(∂) (P_i f) = 0` among the outputs.  Together these identify the differential matroid of
   the outputs with the operator rank, which is `(18)`.

Until `(18)` is in Lean this card stays in Stage 2, even though its four named Lean parents —
multivariate entire sources, Hermite interpolation, the affine chain rule, and
determinant-to-differential-independence — are now all unconditional.

### Log — parent 1 of `(18)` is closed `[PROVED]`

`HTGeometry/MultivariateEntirePartialDeriv.lean` (wired, axiom-clean):

- `analyticOnNhd_fderiv_multivariateEntire`, `differentiable_fderiv_apply` — the Frechet derivative
  of an entire source is analytic (`AnalyticOnNhd.fderiv`), so every directional derivative is
  differentiable;
- **`partialDerivEntire v g`** — the directional derivative as an entire source;
- `iteratedFDeriv_partialDerivEntire` — evaluating the last slot commutes with iterated
  differentiation (`ContinuousLinearMap.iteratedFDeriv_comp_left` for `L ↦ L v`);
- **`orderedPartialJetEvalCLM_succ_right`** — an ordered mixed jet of a source is the shorter
  ordered jet of its directional derivative in the last slot.

Still open for `(18)`: permutation invariance of the ordered jet (two words with equal
`wordMultiplicity` differ by a permutation of `Fin n`, glued from fibre equivalences through
`Equiv.sigmaFiberEquiv`, then `iteratedFDeriv_comp_perm`), the resulting multi-index composition law
`∂^γ ∘ ∂^β = ∂^{β+γ}`, algebraic independence of linearly independent linear forms, and the
assembly described above.

### Log — the operator-rank law `(18)` in Lean `[PROVED]`

Three more modules, wired and axiom-clean.

`HTGeometry/MultivariateJetCompositionLaw.lean`

- `wordMultiplicity_apply` — the multiplicity of a coordinate counts its slots;
- **`exists_perm_comp_of_wordMultiplicity_eq`** — two words with equal multiplicity differ by a
  permutation, glued from fibre equivalences through `Equiv.sigmaFiberEquiv`;
- `orderedPartialJetEvalCLM_comp_perm`, **`orderedPartialJetEvalCLM_congr_of_wordMultiplicity_eq`**
  — an ordered mixed jet depends only on the multiplicity of its word;
- `wordPartialDerivEntire`, `orderedPartialJetEvalCLM_eq_wordPartialDerivEntire` — the jet is the
  value of the iterated directional derivative;
- **`multiIndexJetEvalCLM_multiPartialDerivEntire`** — the composition law
  `∂^γ ∘ ∂^β = ∂^{β+γ}` for the continuous jet observations; `multiIndexJetEvalCLM_zero`.

`HTGeometry/LinearFormSubstitution.lean`

- `linForm`, `coeff_linForm`, `linForm_injective`;
- **`injective_aeval_linForm`** — substituting linearly independent linear forms is injective on
  polynomials: an injective linear map of vector spaces splits, and the retraction induces the
  inverse substitution on generators.

`HTGeometry/AffineOperatorRankLaw.lean`

- `jetRelationValue`, `eval₂_aeval_comp`;
- `operatorRowSource` and **`multiIndexJetEvalCLM_operatorRowSource`** — the jets of a
  constant-coefficient operator row are the shifted orbit jets weighted by the operator
  coefficients;
- `operatorJetSubstVector`, `eval₂_linForm`, `eval₂_linForm_eq_linearCombination`,
  `multiIndexJetEvalCLM_operatorRowSource_eq_eval₂`;
- **`exists_jetRelationValue_operatorRowSource_ne_zero`** — if the shifted rows `∂^γ · L_i` are
  `ℂ`-linearly independent then, on a generic source, no nonzero differential relation holds among
  the row outputs;
- **`exists_nonzero_jetRelation_of_not_linearIndependent`** — if they are dependent, the linear
  form of any nontrivial dependence is a nonzero differential relation vanishing identically on the
  outputs.

Together these two theorems are `(18)` in matroid form: the differential matroid of the outputs is
the linear matroid of the shifted operator rows, i.e. the operator rank of `(L_{i,λ})`.

### Log — operator rank identified; the card is complete `[PROVED]`

`HTGeometry/AffineOperatorRankBridge.lean` (wired, axiom-clean) removes the last notational gap.

- `rowVector`, `shiftedSingleSum_apply`, **`shiftedRowSum_apply`**, `rowVector_apply` — the
  coefficient dictionary: the substitution vector of an operator matrix at `(i, γ)` has entry
  `coeff δ (∂^γ · L_{i,j})` at `(j, δ)`;
- `rowVector_add`, `rowVector_smul`, `rowVector_sum`, `rowVector_ext_iff`,
  `rowVector_surjective` — the coefficient vector is a complex-linear bijection from operator rows;
- **`operatorJetSubstVector_eq`** — the substitution vector is exactly the coefficient vector of
  the shifted row `∂^γ · L_i`;
- **`linearIndependent_operatorJetSubstVector_iff`** — complex linear independence of all shifted
  rows **is** linear independence of the rows over the ring of constant-coefficient operators,
  i.e. the operator rank of `(L_{i,λ})` of `(17)`;
- **`exists_jetRelationValue_operatorRowSource_ne_zero_of_linearIndependent`** and
  **`exists_nonzero_jetRelation_of_not_linearIndependent_operator`** — `(18)` in matroid form,
  stated directly against `LinearIndependent (MvPolynomial (Fin d) ℂ) L`: independent operator rows
  give differentially independent outputs, dependent rows give a nonzero linear differential
  relation.

All Lean gates of this card are now met.  Promoting to Stage 3.
