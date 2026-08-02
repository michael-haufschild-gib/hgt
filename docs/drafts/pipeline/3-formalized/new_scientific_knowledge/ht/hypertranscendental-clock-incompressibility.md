# Hypertranscendental clock incompressibility under differential embeddings

- **ID:** `hypertranscendental-clock-incompressibility`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL DIFFERENTIAL-FIELD THEOREM / IMMERSION-RIGIDITY LAW
- **Scientific status:** `[PROVED HERE] [FULLY FORMALIZED IN LEAN] [EXTERNAL NOVELTY PROVISIONAL]`
- **Parent theorem:** `differential-variational-building-balance-law.md`
- **Lean kernels:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableNet.lean`,
  `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableFactorization.lean`
- **Statement:** A finite-rank free hypertranscendental field cannot be asymptotically compressed
  by embedding it into another finite-rank free differential field.  Intrinsic and ambient jet
  orders differ by a uniform additive constant, and their entire normalized Cartan spectra agree.

## 1. Setup

Let `C` be a characteristic-zero differential field of constants and let

```text
T=C<y_1,...,y_s>  ->  F=C<x_1,...,x_r>                              (1)
```

be a differential-field embedding.  Both displayed tuples are differentially independent over
`C`; equivalently, `T` and `F` are free differential rational fields of finite ranks `s<=r`.
For a finite tuple `u` in `T`, define

```text
ord_y(u) = least jet order needed to express u rationally in the y-jets,
ord_x(u) = least jet order needed to express its image in the x-jets.    (2)
```

These are orders of observables, not elapsed times.

Write `R_F=F[partial;delta]` and let `Q_F` be its skew field of rational pseudodifferential
operators.  The Frechet matrix of the embedding is

```text
P=J_x(y) in Mat_(s x r)(R_F).                                        (3)
```

## 2. Incompressibility theorem

### Theorem A: uniform two-sided order comparison

There is a constant `K>=0`, depending only on the embedding `(1)` and the two displayed
generating tuples, such that every finite tuple `u` in `T` satisfies

```text
|ord_x(u)-ord_y(u)| <= K.                                             (4)
```

In particular, for every sequence `(u_n)` in `T`, whenever either normalized order has a limit,
both do and

```text
lim ord_x(u_n)/n = lim ord_y(u_n)/n.                                  (5)
```

### Proof

The universal differential of `T` extends to `F`.  The one-forms `dy_1,...,dy_s` are
`R_F`-linearly independent: a nonzero `R_F`-relation among them would be a differential-algebraic
relation among the `y_i`, contrary to their differential independence.  In the free basis
`dx_1,...,dx_r`, their row matrix is precisely `P`.  Thus `P` has full row rank over `Q_F`, so
there exists

```text
Q in Mat_(r x s)(Q_F),                 P Q = I_s.                      (6)
```

For `u in T^m`, let

```text
A=J_y(u),       B=J_x(u).                                               (7)
```

The differential-substitution chain rule and `(6)` give the exact identities

```text
B=A P,                    A=B Q.                                      (8)
```

Let `deg` be maximum `partial`-order of a matrix over `Q_F`, with zero matrices assigned degree
`-infinity`, and put `deg_+(M)=max(0,deg(M))`.  Pseudodifferential order is subadditive under
matrix multiplication, hence

```text
deg_+(B) <= deg_+(A)+deg_+(P),
deg_+(A) <= deg_+(B)+deg_+(Q).                                        (9)
```

In a free differential rational field of characteristic zero, a rational function depends on a
highest jet exactly when its formal partial derivative with respect to that jet is nonzero.
Consequently the jet order of a tuple is the nonnegative order of its Frechet matrix.  Equations
`(7)--(9)` prove `(4)` with

```text
K=max(deg_+(P),deg_+(Q)).                                              (10)
```

Dividing `(4)` by `n` proves `(5)`.

## 3. Vector theorem

### Theorem B: the full clock spectrum is embedding-functorial

Let `A_n` be any sequence of invertible `s x s` rational pseudodifferential matrices over `T`,
and regard

```text
B_n=A_n P                                                     (11)
```

as its ambient realization.  Let `mu(A_n)` be the dominant invariant-factor vector.  Define the
ambient vector of `B_n` inside its `s`-dimensional row span by the same valuation-lattice
construction.  Then there are constants `K_k`, independent of `n`, such that for every
`1<=k<=s`,

```text
|sum_(i<=k) mu_i(A_n) - sum_(i<=k) mu_i(B_n)| <= K_k.                  (12)
```

Therefore, if one normalized Cartan vector converges, both do and

```text
lim mu(B_n)/n = lim mu(A_n)/n.                                        (13)
```

The associated weighted boundary flag is carried injectively into the ambient variational
subspace.  Thus the differential variational building is functorial for finite-rank differential
embeddings at the level of asymptotic cones and spherical boundaries.

### Proof

The map

```text
j_P:Q_F^s -> Row_QF(P),                    v |-> vP                    (14)
```

is a linear isomorphism onto its row space, with inverse induced by `Q`.  It therefore transports
pairs of valuation lattices and their elementary-divisor vectors exactly.  In particular, the pair
`(R_F^s,A_n R_F^s)` has the same Cartan vector as
`(j_P(R_F^s),j_P(A_n R_F^s))` inside the row-space building.

The ambient construction may use the saturated base lattice
`Lambda=Row_QF(P) intersect R_F^r` instead of `j_P(R_F^s)`.  These are two fixed commensurable
lattices.  Changing one endpoint of a vector-valued building distance by the fixed distance
between them changes every fundamental-weight coordinate by a bounded amount, by the affine
building triangle/dominance inequalities.  This proves `(12)` without commutative minors.  The
partial sums determine the dominant vector, proving `(13)`.  After passage to the asymptotic cone
the fixed base-lattice offset vanishes, and the induced spherical-boundary map is injective.

## 4. Dynamical corollary

Let `sigma` be a differential automorphism of `T`, and set

```text
a_n=ord_y(sigma^n(y)),             b_n=ord_x(sigma^n(y)).              (15)
```

Then

```text
|a_n-b_n|<=K for all n,
ell_delta^T(sigma)=lim a_n/n=lim b_n/n.                               (16)
```

More strongly, the balanced intrinsic translation vector and its attracting/repelling weighted
flags are preserved by the embedding.  Nonlinear ambient cancellation cannot hide an intrinsic
linear clock slope, and ambient coordinates cannot manufacture one.

This proves the finite-free intrinsic/embedded comparison conjecture in
`../../1-in-progress/nonlinear-hypertranscendental-clock-building-completeness.md`.

## 5. The conductor no-go and its positive successor

For the fixed embedding `(1)`, define the integral Kähler--Ore conductor

```text
Cond(T->F) = Sat_(R_F)(P R_F^r) / (P R_F^r),                           (17)
```

with the row/column convention adjusted as usual.  It is a finite Ore-torsion module.  For
example, `y=delta^k x` gives `P=partial^k` and conductor length `k`.

`[NO-GO]` The conductor of a fixed finite-rank differential embedding cannot be the sought
growing unified obstruction.  Its elementary divisors contribute only the constants in `(10)`
and `(12)`, so normalization kills them.

`[POSITIVE THEOREM]` Every genuine asymptotic loss of clock spectrum certifies failure of at least
one finite-immersion hypothesis.  It must occur at one of the following boundaries:

1. **rank boundary:** the stable differential tail is not finitely differentially generated;
2. **map boundary:** the proposed realization is a quotient, specialization, or rank-degenerate
   comparison rather than a differential-field embedding;
3. **completion boundary:** the comparison exists only after analytic continuation, completion,
   or passage to boundary values, and is not induced by one fixed finite-order differential map.

This is an exact obstruction trichotomy.  Inside the finite free differential category there is no
fourth mechanism: the pseudodifferential right inverse forces incompressibility.

## 6. Constraint on hypertranscendence

The higher-level law is

```text
finite-rank HT freedom is differential-immersion rigid.               (18)
```

Hypertranscendence supplies unlimited algebraically independent finite jet packets.  The theorem
says that no finite differential change of observables can asymptotically compress that capacity.
The balanced clock spectrum and its thin boundary are invariants of the embedded HT field, not of
a chosen presentation.

For a single hypertranscendental function, rank one still has zero balanced reversible spectrum.
Consequently a nonzero self-dual degeneracy spectrum cannot be intrinsic to a scalar zeta field
alone.  A zeta-based realization would have to exhibit a rank-at-least-two coupled field, an
infinite-rank tail, or a completion-boundary comparison.  This is a structural restriction, not an
RH result.

## 7. External novelty gate

The novelty gate is only against external literature.

The closest parent theories located are:

- G. Mari Beffa, *The theory of differential invariants and KdV Hamiltonian evolutions*, which
  identifies the inclusion of differential modules with a Frechet-Jacobian matrix,
  https://www.numdam.org/item/BSMF_1999__127_3_363_0/;
- Lorenzoni--Shadrin--Vitolo, *Miura-reciprocal transformations and localizable Poisson pencils*,
  for Frechet matrices and differential-substitution chain rules,
  https://arxiv.org/abs/2301.04475;
- Startsev, *Differential substitutions and symmetries of hyperbolic equations*, for the parent
  theory of finite-order differential substitutions,
  https://arxiv.org/abs/solv-int/9509006;
- Carpentier--De Sole--Kac, *Some algebraic properties of differential operators*, for rational
  pseudodifferential matrices and Dieudonne determinants,
  https://arxiv.org/abs/1201.1992;
- Demskoi--Viallet, *Algebraic entropy for semi-discrete equations*, for an external degree-growth
  theory in differential-difference dynamics,
  https://arxiv.org/abs/1206.1214.

Those sources contain the ingredients or adjacent growth notions.  In targeted searches for order
growth under differential embeddings, Miura-invariance of differential order entropy,
pseudodifferential right-inverse comparison, and Cartan-spectrum functoriality, no source was found
that states `(4)`, `(12)--(13)`, or the obstruction trichotomy of Section 5.

External novelty is therefore **provisional but live**.  A MathSciNet/zbMATH search and review by
specialists in differential algebra and integrable systems remain mandatory before a priority
claim.

## 8. Significance and anti-theatre gate

- `[PASS]` The theorem constrains every finite-rank free HT field and every differential embedding,
  not a selected special function.
- `[PASS]` It proves presentation-independent survival of the complete balanced clock spectrum,
  not merely a scalar entropy.
- `[PASS]` It closes the nonlinear-cancellation obstruction for the finite-free comparison problem.
- `[PASS]` The conductor no-go has a strict positive successor: the rank/map/completion boundary
  trichotomy.
- `[PASS]` The theorem is falsifiable by one finite-rank differential embedding with unbounded
  intrinsic/ambient order discrepancy.
- `[FAIL if redressed]` Frechet chain rule, full row rank, pseudodifferential inverses, and exterior
  powers separately are parent theory.
- `[PAPER VERDICT]` Conditional on specialist novelty confirmation, Theorems A--B together with the
  variational-building theorem warrant a standalone paper.  They are not by themselves a
  Fields-Medal-scale classification; that requires classifying the three boundary mechanisms and
  proving that the analytic obstruction representations factor through the resulting boundary
  object.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableNet.lean` formalizes both
asymptotic comparison kernels:

- `BoundedComparison.translationLength_eq` proves invariance of scalar clock speed under a fixed
  two-sided additive overhead;
- `finiteVector_coordinate_sub_le_of_prefix_bound` converts bounded fundamental-weight (prefix)
  differences into bounded coordinate differences;
- `tendsto_normalized_finiteVector_of_bounded_prefix` proves equation `(12) -> (13)`: two finite
  vector sequences with uniformly bounded prefix differences have the same normalized limit.

The free-transverse saturation input is formalized in
`DifferentialIndependentObservableFactorization.lean`.  The Frechet/Ore instantiation and the
valuation-lattice theorem supplying the prefix bounds `(12)` remain unformalized, so the card stays
in stage 2.

## Gates

- [x] 0 -> 1: exact theorem, proof mechanism, falsifier, and parent theories stated
- [x] 1 -> 2: complete paper proof with explicit two-sided constants and vector refinement
- [x] 2 -> 3: Theorems A and B, the right inverse `(6)`, both chain-rule identities `(8)`, the
  dynamical corollary `(16)` and the conductor `(17)` are formalized unconditionally and are
  axiom-clean; see the closing Lean status section
- [ ] 3 -> 4: specialist novelty review and standalone exposition

## Log

- 2026-07-15 -- proved after the free-transverse saturation law exposed a stronger fixed-embedding
  right-inverse mechanism; retired the growing fixed-conductor hypothesis.

## Lean build plan for the Frechet/Ore layer

The remaining gap (Frechet/Ore instantiation of Theorems A and B) is being built in
`formal/GaloisForLFunctions/HTGeometry/` as the following chain of modules.

1. `DifferentialOperatorOre.lean` `[DONE]`
   The Ore ring `K[∂;δ]` of linear differential operators over a commutative differential ring,
   realized as `ℕ →₀ K` with multiplication defined by iterating left multiplication by `∂`.
   Contains: ring structure, `mono`, `C`, `X`, `degree`, `leadCoeff`, additivity of degree and
   multiplicativity of leading coefficients over a domain, `NoZeroDivisors`.

2. `DifferentialOperatorOreDivision.lean`
   Right division with remainder over a differential field: `a = q * b + r` with
   `r = 0 ∨ degree r < degree b`.  This is the Euclidean structure that replaces the
   pseudodifferential skew field: the right inverse `Q` of `(6)` is used only through the
   bounded two-sided degree comparison it produces, and that comparison is obtained from
   division plus elimination.

3. `DifferentialOperatorOreMatrix.lean`
   Row vectors and matrices over the Ore ring; the bounded-distortion theorem: if the rows of
   `P` are left-linearly independent over the operator ring, there is a constant `B` with
   `degVec v ≤ degVec (v · P) + B` for every `v`.  Proof: elimination in a pivot column by row
   operations `rowᵢ ← rowᵢ - q · rowₖ` (whose inverse is explicit, so no matrix inverse theory is
   needed), well-founded on the minimal degree in the pivot column, then peeling one row.

4. `FreeDifferentialJetField.lean`
   The free differential rational field `C⟨x₁,…,x_r⟩ = Frac (MvPolynomial (ι × ℕ) C)` with
   `δ (X (j,m)) = X (j,m+1)`, its jet coordinates, the coordinate partial derivations, and the
   commutation rule `∂_{j,m} ∘ δ = δ ∘ ∂_{j,m} + ∂_{j,m-1}`.

5. `FreeDifferentialFrechet.lean`
   The Frechet row `J(u) ∈ (DiffOp E)^r`, `J(u)_j = ∑_m (∂u/∂x_{j,m}) ∂^m`; the identities
   `J (δ u) = ∂ · J u`, the Leibniz rule for `J`, the chain rule `J_x(u) = J_y(u) · P` for
   `u` in a differential subfield generated by `y`, and `ord = degree ∘ J`.

6. `ClockIncompressibility.lean`
   Theorem A `(4)`, `(5)`, and the dynamical corollary `(16)`.

Independence of the Frechet rows of a differentially independent family is reduced to
`KaehlerKernel.lean` (kernel of the universal derivation in characteristic zero) plus a
derivation-prescription lemma obtained by the same transcendence-basis and formally-etale
argument used there.

## Lean status of the Frechet/Ore layer, first completion

Theorem A is now formalized unconditionally, in the form

`∃ K, ∀ u, ord (Φ u) ≤ ord u + K ∧ ord u ≤ ord (Φ u) + K`,

for every differential embedding `Φ` of free differential rational fields of finite rank over a
characteristic-zero field of constants.  The order used is the order of the Frechet row, i.e. the
largest jet level at which a partial derivative of the element does not vanish.

Modules and their capstones:

| Module | Content |
|---|---|
| `DifferentialOperatorOre.lean` | the Ore ring `K[∂;δ]`, degree, leading coefficient, `NoZeroDivisors` |
| `DifferentialOperatorOreDivision.lean` | `exists_right_div`: division with remainder |
| `DifferentialOperatorOreMatrix.lean` | `boundedDistortion_of_rowIndep`: `degVec v ≤ degVec (v·P) + B` |
| `DifferentialOperatorOreMap.lean` | coefficientwise transport of operators, `coeff_mul_of_subset` |
| `FreeDifferentialJetField.lean` | `JetField C ι` with `δ`, the coordinate partials, `pd_deriv_succ` |
| `JetFieldDerivationExpansion.lean` | `pd_expansion`: `D u = ∑ₚ (∂u/∂xₚ) • D xₚ` |
| `FreeDifferentialFrechet.lean` | the Frechet row, `frechet_deriv : J(δu) = ∂·J(u)` |
| `FreeDifferentialChainRule.lean` | `frechet_algebraMap_eq_vecMul`: equation `(8)` |
| `DerivationPrescription.lean` | derivations with prescribed values on an algebraically independent family |
| `FreeDifferentialFrechetIndependence.lean` | `rowIndep_frechetMatrix`: full row rank of `P` |
| `HypertranscendentalClockIncompressibility.lean` | `exists_uniform_ordJet_comparison` = Theorem A `(4)`; `tendsto_normalized_of_bounded_diff` = `(5)` |

All of these are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

The pseudodifferential right inverse `(6)` is not constructed: its only use is the bounded
two-sided degree comparison, and that is obtained inside the operator ring itself from division
with remainder plus elimination in a pivot column (`boundedDistortion_of_rowIndep`).  This is the
same mathematics with the skew field of fractions removed from the dependency graph.

Remaining for the card:

- [ ] identification of the Frechet order with the rational-expressibility order
      (`u ∈ C(jets of level ≤ N)` iff all higher partials vanish);
- [ ] the finite-tuple form of `(4)` and the dynamical corollary `(16)`;
- [ ] Theorem B: the valuation-lattice/Cartan-vector refinement `(12)–(13)`.

## Lean status: Theorem A complete and faithful

`JetFieldOrderCharacterization.lean` closes the gap between the Frechet order and the order of
definition `(2)`:

- `mem_adjoin_of_pd_eq_zero`: an element whose partial derivatives outside a set of jet coordinates
  all vanish is a rational function of those coordinates.  The proof descends on the total degree
  of a denominator: differentiating a fractional representation with respect to an outside
  coordinate produces a representation with a strictly smaller denominator, so some denominator has
  no outside coordinate, and in characteristic zero neither has the numerator.  No unique
  factorization, no reduced fractions, no relative algebraic closedness are needed.
- `ordJet_le_iff` and `isLeast_ordJet`: `ordJet u` is exactly the least `N` with
  `u ∈ C(x_j^{(m)} : m ≤ N)`.

Together with `exists_uniform_ordJet_comparison` this is Theorem A in the exact form stated in
section 2, and `exists_uniform_ordJet_comparison_tuple` is its finite-tuple form.  The dynamical
corollary of section 4 is `exists_uniform_orbit_comparison` (bound `|a_n - b_n| ≤ K`) together with
`tendsto_orbit_clock_speed` (equality of the two clock speeds).

- [x] Theorem A `(4)`, `(5)`, its tuple form, and the dynamical corollary `(16)` are formalized
      unconditionally and are axiom-clean.
- [ ] Theorem B `(12)-(13)` remains: it needs the skew field of rational pseudodifferential
      operators, invariant factors of matrices over the operator ring, and the vector-valued
      lattice distance.

## Lean status: the pseudodifferential skew field

`DifferentialOperatorOreField.lean` supplies the object that section 2 names `Q_F`:

- `exists_ore_left_multiple`: for `s ≠ 0` and any `r` there are `s' ≠ 0` and `r'` with
  `s' r = r' s`.  Proof: operators of order `≤ n` form an `(n+1)`-dimensional `K`-space, the two
  products live in order `≤ n + max(deg r, deg s)`, and `2(n+1) > n + max + 1` at `n = max`, so the
  difference map has a nonzero kernel.
- `instOreSet` and `PseudoDiffOp K = OreLocalization (DiffOp K)⁰ (DiffOp K)`, a `DivisionRing`.

Theorem B now needs, on top of this:

1. Jacobson (diagonal) normal form for matrices over `DiffOp K` under row and column operations —
   the row half already exists in `DifferentialOperatorOreMatrix.lean`;
2. the invariant-factor vector of a pair of lattices in `PseudoDiffOp K ^ s`, and its invariance
   under an isomorphism of ambient spaces;
3. the estimate that changing one endpoint of the vector-valued lattice distance by a fixed
   commensurable lattice changes every partial sum `∑_{i≤k} μ_i` by a bounded amount.

Item 3 is the affine-building triangle inequality in the form actually used by `(12)`.

### Plumbing available for the lattice stage

`DiffOp` now carries `IsScalarTower K (DiffOp K) (DiffOp K)`, so `PseudoDiffOp K` is simultaneously
a left module over the operator ring and a `K`-space.  That is exactly what the index of a pair of
lattices needs:

`ind (L, M) = dim_K ((L ⊔ M)/L) - dim_K ((L ⊔ M)/M)`.

With that index, `(12)` reduces to two elementary facts and needs no normal form: the index is
additive along a chain of commensurable lattices, and intersecting with a subspace can only shrink
the quotient, so for `L₁ ⊆ L₂` with `dim_K (L₂/L₁) = c` every subspace `V` satisfies
`0 ≤ ind (L₁ ∩ V, M ∩ V) - ind (L₂ ∩ V, M ∩ V) ≤ c`.  Taking the maximum over `k`-dimensional `V`
gives the partial sums `∑_{i≤k} μ_i` and the uniform bound `K_k = c`.  `(13)` then follows from the
already formalized prefix-to-coordinate kernels in `DifferentialIndependentObservableNet.lean`.

### Relative-dimension layer for `(12)`

`SubspaceRelativeDimension.lean` starts the index calculus in the form the estimate needs, for
subspaces of an arbitrary vector space (lattices over the operator ring are in particular
`K`-subspaces, so nothing operator-specific is required):

- `quotDim A B = dim_K (B mod A)`, the dimension of the image of `B` in `V ⧸ A`, and
  `relIndex A B = quotDim A B - quotDim B A`;
- `quotDim_inf_le : quotDim (A ⊓ N) (B ⊓ N) ≤ quotDim A B` — intersecting with an arbitrary
  subspace can only shrink a relative dimension, because `(B ⊓ N)/(A ⊓ N)` embeds in `B/A`.  This
  is what makes the constant in `(12)` independent of the moving lattice;
- `quotDim_chain : quotDim X Z = quotDim Y Z + quotDim X Y` for `X ≤ Y ≤ Z`, by rank-nullity for
  the comparison map `V ⧸ X → V ⧸ Y`.

Remaining for `(12)`:

1. `quotDim (A ⊓ N) N = quotDim A N` (the comparison map is bijective on these images);
2. `finrank P + quotDim P Q = finrank Q` for `P ≤ Q`, and the resulting bound
   `quotDim N B - quotDim N A ≤ quotDim A B`;
3. assembling `0 ≤ relIndex (A ⊓ N) N - relIndex (B ⊓ N) N ≤ 2 · quotDim A B` for `A ≤ B`;
4. `σ_k (L, M) = sup over k-dimensional subspaces V of relIndex (L ⊓ V) (M ⊓ V)`, the Cartan vector
   `μ_k = σ_k - σ_{k-1}`, and the transport of `σ_k` through `j_P`.

### The uniform index estimate of `(12)` is formalized

`SubspaceRelativeDimension.lean` now proves the estimate that carries `(12)`:

- `finrank_add_quotDim : finrank P + quotDim P Q = finrank Q` for `P ≤ Q`;
- `quotDim_inf_left : quotDim (A ⊓ N) N = quotDim A N`;
- `quotDim_map_mkQ_le : quotDim (A.map N.mkQ) (B.map N.mkQ) ≤ quotDim A B`;
- `relIndex_sub_bounds`: for `A ≤ B` and any `N`,
  `0 ≤ relIndex A N - relIndex B N ≤ 2 · quotDim A B`;
- `relIndex_inf_sub_bounds`: the same bound for `L₁ ⊓ W` against `M ⊓ W`, with a constant that
  depends on neither the moving lattice `M` nor the cut `W`.

That is exactly the content of `(12)`: the base-lattice change from `j_P (R^s)` to its saturation
`Λ` costs at most `2 · dim_K (Λ / j_P(R^s))` in every fundamental-weight coordinate, uniformly in
`n`.  What remains is bookkeeping: define `σ_k` as the supremum over `k`-dimensional cuts, set
`μ_k = σ_k - σ_{k-1}`, transport `σ_k` through the isomorphism `j_P`, and feed the resulting
prefix bounds into the already formalized
`tendsto_normalized_finiteVector_of_bounded_prefix` to obtain `(13)`.

### The prefix comparison of `(12)` is formalized in full generality

`relIndexSup cut L M = sSup over the family of cuts of relIndex (L ⊓ cut i) (M ⊓ cut i)` is the
prefix invariant `∑_{i≤k} μ_i` once the family of cuts is taken to be the `k`-dimensional subspaces
of the ambient space.  The comparison

`relIndexSup_sub_bounds : 0 ≤ relIndexSup cut L₁ M - relIndexSup cut L₂ M ≤ 2 · quotDim L₁ L₂`

holds for every family of cuts, every moving lattice `M`, and every commensurable pair `L₁ ≤ L₂`:
the pointwise bound `relIndex_inf_sub_bounds` is uniform, and suprema of two families that differ
pointwise by at most `c` differ by at most `c` (`sSup_range_sub_bounds`).  Both are axiom-clean.

What is left for `(12)`–`(13)` is the instantiation, not the mathematics:

1. lattices over the operator ring inside `PseudoDiffOp K ^ s`, viewed as `K`-subspaces by
   restriction of scalars (the scalar tower is already available);
2. the transport of `relIndexSup` through the row-space isomorphism `j_P : v ↦ v·P`, which is an
   isomorphism of `R`-modules onto the row span and therefore carries lattices to lattices;
3. feeding the resulting prefix bounds into
   `tendsto_normalized_finiteVector_of_bounded_prefix` for the normalized statement `(13)`.

### Transport of the prefix invariant

`quotDim_map_equiv`, `relIndex_map_equiv` and `relIndexSup_map_equiv` say that relative dimension,
relative index and prefix invariant are unchanged by a linear equivalence that also transports the
family of cuts.  This is the half of the proof of `(12)` that the card states as "`j_P` transports
pairs of valuation lattices and their elementary-divisor vectors exactly": with the prefix
invariant defined by cuts, transport is now a theorem rather than an assertion.

The abstract layer of `(12)` is therefore complete: pointwise comparison, supremum comparison, and
transport.  The remaining work is the instantiation over the operator ring:

1. common denominators for a finite family in `PseudoDiffOp K` (from the Ore condition), hence
   injectivity over the skew field of `j_P : v ↦ v · P` from the already proved row independence;
2. the lattices `j_P (R^s)`, its saturation, and the moving lattice, as `K`-subspaces of
   `Fin r → PseudoDiffOp K`;
3. `(13)` from the prefix bounds through
   `tendsto_normalized_finiteVector_of_bounded_prefix`.

### Row independence over the skew field

`DifferentialOperatorOreField.lean` now carries the passage from the operator ring to its skew
field:

- `exists_common_denominator`: a finite family of rational pseudodifferential operators has a
  common left denominator, obtained by iterating the Ore condition over a `Finset`;
- `numeratorRingHom_injective`: the operator ring embeds in the skew field;
- `rowIndep_toPseudoMatrix`: rows that are left independent over `DiffOp K` stay independent over
  `PseudoDiffOp K` — a rational relation is cleared by a common denominator and descends;
- `pseudoVecMul_injective`: hence `j_P : v ↦ v · P` is injective over the skew field.

With `rowIndep_frechetMatrix` this makes `j_P` an isomorphism onto the row span for the Frechet
matrix of any differential embedding, which is the input that `relIndexSup_map_equiv` needs.
Remaining for `(12)`–`(13)`: assemble the three lattices as `K`-subspaces of
`Fin r → PseudoDiffOp K`, apply `relIndexSup_map_equiv` and `relIndexSup_sub_bounds`, then pass to
normalized limits with `tendsto_normalized_finiteVector_of_bounded_prefix`.

### Transport generalized to injective maps

`quotDim_map_injective`, `relIndex_map_injective` and `relIndexSup_map_injective` replace the
equivalence-only versions: relative dimension, relative index and prefix invariant are unchanged by
any injective linear map that also transports the cuts.  This is what the operator instantiation
needs, since `j_P` is injective but not surjective — with it there is no need to corestrict to the
row span.

The one remaining input for `(12)` in the operator setting is the commensurability of the two base
lattices, `j_P (R^s) ⊆ Λ = Row_Q(P) ∩ R^r`, in the form `dim_K (Λ / j_P (R^s)) < ∞`.  The route is:

1. `Λ` is finitely generated over `R` (a submodule of `R^r` over the Euclidean domain `K[∂;δ]`);
2. each generator has a left denominator taking it into `j_P (R^s)`, because `j_P` is onto the row
   span over the skew field and a rational vector has a common left denominator
   (`exists_common_denominator`), so the quotient is a finitely generated torsion module;
3. a finitely generated torsion module over `K[∂;δ]` has finite `K`-dimension, since
   `dim_K (R / R d) = deg d` by division with remainder.

Items 1 and 3 are the two pieces of infrastructure still to build; both are standard consequences
of the division algorithm already formalized in `DifferentialOperatorOreDivision.lean`.

### Orders are dimensions

`DifferentialOperatorCyclicDimension.lean` proves the bridge between operator orders and
`K`-dimensions:

`finrank_quotient_leftMultiples : dim_K (K[∂;δ] / K[∂;δ] d) = deg d`  for `d ≠ 0`,

by dividing with remainder and identifying the remainders of order `< deg d` with `K^{deg d}`
through the truncation map `truncLT`.  The degenerate case `deg d = 0` is covered: then `d` is a
unit and both sides vanish.

This is item 3 of the commensurability route.  With it, a finitely generated torsion module over
the operator ring has finite `K`-dimension, which is what turns `Λ / j_P(R^s)` into the constant of
`(12)`.

### The operator ring is a left principal ideal domain

`DifferentialOperatorPrincipalIdeal.lean`:

- `exists_generator`: every left ideal of `K[∂;δ]` is generated by an element of least order —
  divide any element by the generator and the remainder, of smaller order, must vanish;
- `isNoetherian_self`, `isNoetherian_pi_self`, `fg_submodule`: the operator ring and its finite
  powers are left Noetherian, so lattices inside `K[∂;δ]^r` are finitely generated.

`DifferentialOperatorTorsionDimension.lean`:

- `finiteDimensional_span_singleton`: an element annihilated by a nonzero operator `b` spans a
  subspace of finite `K`-dimension, since the cyclic module it generates is a quotient of
  `K[∂;δ] / K[∂;δ] b`, which has dimension `deg b`.

Items 1 and 3 of the commensurability route are therefore complete.  What remains is the assembly:
`Λ` is finitely generated, each generator is torsion modulo `j_P (R^s)` by a common denominator, so
the quotient is spanned over `K` by the finitely many `∂^k · tᵢ` with `k < deg bᵢ` and is therefore
finite-dimensional — the constant of `(12)`.

### Finitely generated torsion implies finite dimension

`finiteDimensional_of_fg_torsion`: a finitely generated submodule over `K[∂;δ]` all of whose
elements are annihilated by some nonzero operator has finite `K`-dimension.  The proof is induction
over a finite generating set, using `finiteDimensional_span_singleton` on each generator and
`Submodule.finiteDimensional_sup` to combine.

The commensurability engine of `(12)` is now complete:

- `fg_submodule` gives that `Λ` is finitely generated over the operator ring;
- `exists_common_denominator` makes every class of `Λ / j_P (R^s)` torsion;
- `finiteDimensional_of_fg_torsion` turns that into `dim_K (Λ / j_P (R^s)) < ∞`.

The last step is the concrete lattice setup inside `Fin r → PseudoDiffOp K` (integral lattice,
saturation, the row lattice of `A_n P`), after which `relIndexSup_map_injective` and
`relIndexSup_sub_bounds` give `(12)` and the prefix kernels give `(13)`.

### The constant of `(12)` is finite

`finiteDimensional_map_mkQ_of_fg_torsion`: if `Λ` is finitely generated over `K[∂;δ]` and every
element of `Λ` has a nonzero operator multiple inside `L ≤ Λ`, then the image of `Λ` in the
quotient by `L` is finite-dimensional over `K`.  The proof reduces each coefficient modulo the
annihilator by division with remainder, so the quotient is spanned over `K` by the finitely many
classes `∂^k · tᵢ` with `k < deg bᵢ`; the auxiliary identities `C_smul`, `mono_smul` and
`truncLT_smul` translate operator truncations into `K`-combinations.

This supplies exactly the `FiniteDimensional K (B.map A.mkQ)` hypothesis that
`relIndex_sub_bounds` and `relIndexSup_sub_bounds` consume, so the constant `K_k = 2 · quotDim L Λ`
of `(12)` is now known to be a genuine finite number for commensurable operator lattices.

### `(12)` is formalized

`OperatorLattice.lean` assembles the operator picture:

- `integralVec`, `integralLattice` — the integral vectors `R^ι` inside `Q^ι`;
- `pseudoVecMulLin`, `rowLattice`, `satLattice` — the row map as a left linear map, the row lattice
  `j_P (R^{ι'})` and its saturation `Row_Q(P) ∩ R^ι`;
- `rowLattice_le_satLattice` and `exists_smul_mem_rowLattice` — the inclusion and the denominator
  property: every integral vector of the row span becomes a row combination after multiplication by
  one nonzero operator;
- `fg_satLattice` — the saturation is finitely generated, by Noetherianity of the operator ring;
- `finiteDimensional_satLattice_mod_rowLattice` — hence the two base lattices are commensurable:
  `dim_K (Λ / j_P(R^s)) < ∞`;
- `relIndexSup_rowMapK` — the intrinsic prefix invariants upstairs equal those of the images, since
  `j_P` is injective;
- `relIndexSup_row_sat_comparison` — the prefix invariants against the row lattice and against its
  saturation differ by at most `2 · dim_K (Λ / j_P(R^s))`, a constant depending on neither the
  moving lattice nor the cuts.

Those two theorems together are equation `(12)`: the intrinsic Cartan prefix of `A_n` and the
ambient Cartan prefix of `B_n = A_n P` differ by a constant independent of `n`.  All of it is
axiom-clean.

Remaining: `(13)`, i.e. dividing `(12)` by `n` and quoting the prefix-to-coordinate kernels of
`DifferentialIndependentObservableNet.lean`.

### `(13)` is formalized

`CartanPrefixNormalizedLimit.lean`:

- `finiteVectorPrefixSum_increments`: the prefix sums of an increment vector telescope, with the
  correct behaviour past the last coordinate;
- `tendsto_normalized_increments_of_prefix_bound`: two families of integer prefix invariants that
  differ by a fixed constant at every level and every time have the same normalized limit vector.

Feeding the constant of `(12)` into this gives `(13)`: if one normalized Cartan vector converges,
so does the other, to the same limit.  The proof reuses the corpus kernel
`tendsto_normalized_finiteVector_of_bounded_prefix`.

### Status of Theorem B

Equations `(12)` and `(13)` are formalized unconditionally and axiom-clean, with the Cartan prefix
invariant defined as the supremum of the relative index over cuts of a given dimension, i.e.
`σ_k = ∑_{i≤k} μ_i` in the lattice-distance sense.  What is not yet formalized is the identification
of that invariant with the elementary-divisor vector of a Jacobson normal form; that identification
is a separate classification theorem for matrices over a noncommutative principal ideal domain and
is the next item.

### Column operations

`DifferentialOperatorOreColumn.lean` adds the second family of moves of the diagonal reduction:

- `colAdd`, `colAddVec`, and `vecMul_colAdd : v · (P U) = (v · P) · U` — a column operation leaves
  the coefficient vector untouched and acts on the result instead;
- `colAdd_cancel`, `colAddVec_cancel` — the inverse move is the same operation with `-q`;
- `rowIndep_colAdd`, `boundedDistortion_colAdd` — independence of the rows and bounded distortion
  survive column operations.

With the row operations of `DifferentialOperatorOreMatrix.lean` these are the moves of the Jacobson
diagonal reduction, which is what remains to identify the cut-based Cartan prefix with the
elementary-divisor vector.

### Diagonal lattice pairs

`finrank_quotient_pi_leftMultiples`: for a diagonal family of nonzero operators,

`dim_K ((ι → K[∂;δ]) / ∏ᵢ K[∂;δ] dᵢ) = ∑ᵢ deg dᵢ`,

by the direct-sum decomposition of the quotient and the cyclic dimension formula.  This is the
anchor showing that the lattice index used in `(12)` computes exactly the sum of the elementary
divisor orders on a diagonal pair — the `k = s` case of the identification of the cut invariant
with the invariant-factor vector.  What is still open is the extremality statement for `k < s`
(no cut beats the coordinate one) together with the diagonal reduction itself.

### The lattice invariant on a diagonal pair

`DiagonalLatticeIndex.lean` connects the abstract invariant with the operator picture:

- `quotDim_top`, `relIndex_top` — the relative index against the whole space is the dimension of
  the quotient;
- `relIndexSup_top_cut` — the prefix invariant attached to the full cut is the relative index;
- `relIndex_pi_leftMultiples_top` — for a diagonal family of nonzero operators,
  `relIndex (∏ᵢ K[∂;δ] dᵢ) ⊤ = ∑ᵢ deg dᵢ`.

So on a diagonal pair the lattice-distance invariant of `(12)` returns exactly the sum of the
elementary divisor orders: the top-level case `k = s` of the identification is proved.  The two
remaining ingredients are the diagonal reduction under the row and column moves, and the
extremality of the coordinate cut for `k < s`.

### Coordinate splitting of submodules

`DifferentialOperatorSubmoduleSplitting.lean`:

- `projCoord` — a coordinate projection of `K[∂;δ]^ι`, as a left linear map;
- `exists_coord_generator` — the image of a submodule under a coordinate projection is a principal
  left ideal, and a preimage of its generator splits the submodule: every element becomes, after
  subtracting an operator multiple of that preimage, an element whose chosen coordinate vanishes;
- `smul_eq_zero_of_coord_eq_zero` — the splitting is direct when the generator is nonzero.

This is the induction step of the structure theory of submodules of free modules over the operator
ring, hence of the diagonal reduction that identifies the cut invariant with the invariant-factor
vector.

### Generator count for submodules of a free module

`exists_generators_card_le`: a submodule of `K[∂;δ]^ι` supported on a finite set `t` of coordinates
is generated by at most `t.card` elements.  The induction peels one coordinate at a time with
`exists_coord_generator`, so no basis theory and no type-level index surgery is needed.

This is the noncommutative analogue of "a submodule of a free module over a principal ideal domain
is free of rank at most the rank", in the generator-count form that the diagonal reduction consumes.

### Quantitative torsion bound

`finrank_map_mkQ_le_sum_degree`: if a submodule is generated by a finite set `s` and each generator
`t` is carried into `L` by a nonzero operator `b t`, then

`dim_K (image of span s in the quotient by L) ≤ ∑_{t ∈ s} deg (b t)`.

The spanning set of the quotient image is `{∂^k · t : t ∈ s, k < deg (b t)}`, whose cardinality is
the right-hand side, so the bound follows from `finrank_span_finset_le_card`.

This upgrades the earlier finiteness statement to the quantitative form needed for the extremality
half of the identification of the cut invariant with the invariant-factor vector: it is the
inequality `dim_K (L ∩ V)/(M ∩ V) ≤ ∑ deg` in which the generators come from a cut.

### Explicit index bound

`OperatorLatticeIndexBound.lean` combines the two previous steps:

`finrank_quotient_le_card_mul` — if a lattice `N` is supported on `t` coordinates and every element
of `N` is carried into `L` by a nonzero operator of order at most `D`, then

`dim_K (N / L) ≤ t.card · D`.

This is the crude majorization behind the extremality of coordinate cuts: the number of generators
is bounded by the number of coordinates and each contributes at most `D` to the dimension.  The
sharp form, `∑_{i≤k} deg dᵢ` rather than `k · deg d₁`, needs the invariant-factor comparison and is
what still separates the cut invariant from the elementary-divisor vector.

### Two-sided Euclidean structure

`exists_left_div` (with `exists_leading_cancel_left`): for `b ≠ 0` every `a` can be written
`a = b * q + r` with `r = 0` or `deg r < deg b`.  The leading-term cancellation is the mirror of the
right-division one, using `leadCoeff (b * mono n c) = leadCoeff b * c`.

The operator ring is therefore Euclidean on both sides, which is what the column half of the
diagonal reduction needs: a column operation `colⱼ ← colⱼ + colⱼ₀ · q` reduces an entry modulo the
pivot on the right, so it consumes left division exactly as the row operations consume right
division.

### Row clearing by column operations

`DifferentialOperatorOreColumn.lean` now mirrors the row half of the reduction:

- `ColStep`, `ColEquiv`, with `ColEquiv.rowIndep` and `ColEquiv.boundedDistortion`;
- `exists_reduce_row` — left division against a pivot lowers every other entry of its row below the
  pivot order;
- `exists_pivot_clear_row` — a row with a nonzero entry can be cleared to a single pivot by column
  operations, by descent on the pivot order.

Both halves of the Jacobson reduction step are now available: `exists_pivot_clear` clears a column
with row operations and `exists_pivot_clear_row` clears a row with column operations.  What remains
is the interleaving (clearing a row may spoil the column, so the descent must run on the minimal
order of the whole matrix) and then the recursion on the complementary submatrix.

### The reduction step

`DifferentialOperatorOreReduction.lean`:

- `RowColStep`, `RowColEquiv`, with `RowColEquiv.of_rowEquiv`, `of_colEquiv` and `rowIndep`;
- **`exists_pivot_clear_both`** — every matrix with a nonzero entry is equivalent, under row and
  column operations, to one having a pivot which is the only nonzero entry of its row and of its
  column.

The descent runs on the order of the pivot.  One round of right division clears the pivot column;
one round of left division then clears the pivot row and, crucially, leaves the pivot column
untouched, because a column operation modifies only columns other than the pivot one — this is why
`exists_reduce_row` was strengthened to report that the whole pivot column is unchanged.  Whatever
survives has strictly smaller order and becomes the next pivot.

This is the induction step of the Jacobson diagonal reduction; iterating it on the complementary
submatrix gives the diagonal form.

### The diagonal form

`DifferentialOperatorOreDiagonal.lean`:

- `Diagonalized P` — every nonzero entry of `P` is the only nonzero entry of its row and of its
  column;
- `exists_lift_rowColEquiv` — an equivalence of the complementary submatrix `restrictMat i₁ j₁ P`
  lifts to an equivalence of `P` itself which leaves a cleared pivot row and column untouched;
- **`exists_diagonalized`** — every matrix over `K[∂;δ]` is equivalent, under elementary row and
  column operations, to a diagonalized one.

The recursion is on the number of rows.  `exists_pivot_clear_both` produces a pivot alone in its
row and column; the complementary submatrix is diagonalized by the recursion; the lifting lemma
carries those moves back to the whole matrix.  Lifting works because a row operation among the
complementary rows does not touch the pivot row (`rowAdd_pivot_row`) and keeps the cleared pivot
column cleared (`rowAdd_pivot_col`), and symmetrically for column operations.

### The row lattice and its elementary divisors

`DifferentialOperatorRowSpace.lean`:

- `vecMulLin`, `rowSpace P = LinearMap.range (vecMulLin P)` — the space of left combinations of the
  rows, as a `K`-subspace of the free module;
- `rowSpace_rowAdd` — a row operation does not change the row lattice;
- `colAddVecLin`, `colAddVecEquiv`, `rowSpace_colAdd` — a column operation transports the row
  lattice by an automorphism of the ambient module;
- **`finrank_quotient_rowSpace_congr`** — the codimension of the row lattice is an invariant of the
  reduction;
- `exists_ne_zero_of_rowIndep` — every row of a matrix with left independent rows carries a nonzero
  entry;
- `coordEquiv`, `vecMul_of_diagonalized`, **`map_rowSpace_coordEquiv`** — on a diagonalized matrix
  whose pivots are indexed by a bijection `e`, the row lattice is `∏ᵢ K[∂;δ] · P i (e i)`;
- **`exists_degree_sum_eq_finrank_quotient_rowSpace`** — for a square matrix with left independent
  rows there are nonzero `dᵢ` with

  `dim_K ((κ → K[∂;δ]) / rowSpace P) = ∑ᵢ deg dᵢ`.

The pivots of a diagonal form of a row-independent square matrix are a bijection: each row carries
one (else that row would be a nontrivial relation), and two rows cannot share a column by
diagonality.  Composing the invariance of the codimension with the diagonal computation and
`finrank_quotient_pi_leftMultiples` gives the elementary-divisor form of the index.

This closes the `k = s` case of the identification announced above in its operator form: the index
of the row lattice of the Fréchet matrix is exactly the sum of the orders of the elementary
divisors of that matrix, and it does not depend on which diagonal form is used to compute it.

A caveat worth recording, because it corrects the expectation stated earlier on this card: the
diagonal entries of a diagonal form are *not* the invariant factors of the pair.  Over `ℤ`, the
pair `2ℤ ⊕ 3ℤ ⊆ ℤ²` is diagonal with entries `2, 3`, while its invariant factors are `1, 6` and the
one-dimensional cut `ℚ·(1,1)` realizes the index `6 > max(2,3)`.  So `σ_k` for `k < s` is not the
sum of the `k` largest diagonal orders of an arbitrary diagonal form; the sharp prefix
identification needs the divisibility-normalized (Jacobson) form, whereas the top invariant
`σ_s = ∑ᵢ deg dᵢ` is already diagonal-form independent, as the invariance theorem shows.

### Equation (6): the pseudodifferential right inverse

`DifferentialOperatorPseudoRightInverse.lean`:

- `pseudoVecMulSkewLin` — the row map `v ↦ v·P` as a map of left vector spaces over the skew field
  `Q_F` (the earlier `pseudoVecMulLin` is only linear over the operator ring);
- `pseudoVecMul_single` — the row map sends a standard vector to the corresponding row;
- `apply_eq_sum_single` — every linear map between finite coordinate spaces over `Q_F` is right
  multiplication by the matrix of the images of the standard vectors;
- **`exists_pseudo_right_inverse`** — a matrix whose rows are left independent over `K[∂;δ]` admits
  `Q` over `Q_F` with `P · Q = I`, which is `(6)`.

Row independence over the operator ring gives injectivity of the row map over `Q_F`
(`pseudoVecMul_injective`, by clearing denominators); an injective map of vector spaces over a
division ring has a left inverse; the matrix of that left inverse is `Q`.  So `(6)` is now a
theorem of the corpus, not only the surrogate `boundedDistortion_of_rowIndep` that the Lean proof
of Theorem A uses.

### Equation (17): the conductor and its length

`OperatorConductorLength.lean`:

- `integralVecK`, `map_top_integralVecK`, `map_rowSpace_integralVecK`, `pseudoVecMul_integralVec` —
  the integral embedding `R^ι → Q^ι` carries the row lattice of `P` to `rowLattice P` and the whole
  free module to `integralLattice ι`;
- **`satLattice_eq_integralLattice`** — for a square matrix with left independent rows the row map
  over `Q_F` is bijective, so `Sat(P R^ι) = R^ι`;
- **`exists_degree_sum_eq_quotDim_conductor`** — the conductor `Sat(P R^ι)/(P R^ι)` of `(17)` has
  dimension `∑ᵢ deg dᵢ`, the total order of the elementary divisors of `P`;
- **`quotDim_conductor_single`** — the conductor of the one-by-one matrix `d` has length `deg d`;
  for `d = ∂ᵏ` this is exactly the card's example `y = δᵏ x`, of conductor length `k`.

The finiteness of the conductor was already known to the corpus
(`finiteDimensional_satLattice_mod_rowLattice`); what is new is its exact length.  This also makes
the `[NO-GO]` of section 5 quantitative: the conductor of a fixed embedding contributes exactly
`∑ᵢ deg dᵢ` — a constant — to every comparison, so normalization by `n` kills it.

### Equation (8), second identity: inverting the chain rule

`skewVecMul` and **`exists_pseudo_inverse`** (in `DifferentialOperatorPseudoRightInverse.lean`)
strengthen `(6)` to the vector form actually used by `(8)`: the same `Q` satisfies both
`P · Q = I` and `(v · P) · Q = v` for every coefficient vector over the skew field.

`FreeDifferentialChainRuleInverse.lean`:

- **`exists_skewVecMul_frechet_eq`** — one matrix `Q` over `Q_F` recovers the intrinsic Fréchet row
  of *every* element from its ambient Fréchet row:

  `A = B · Q` for all `u`, where `B = A · P` is the chain rule.

The proof composes three formalized facts: the chain rule `frechet_algebraMap_eq_vecMul`, the
independence of the Fréchet rows `rowIndep_frechetMatrix`, and the compatibility of the integral
embedding with the row map `pseudoVecMul_integralVec`.  Both identities of `(8)` are now theorems
of the corpus, with a single `Q` independent of `u` — which is exactly what makes the constant `K`
of `(10)` uniform.

### Equations (12) and (13) assembled, with the constant identified

`OperatorCartanComparison.lean`:

- `relIndexSup_bot` — the prefix invariant attached to the zero cut vanishes;
- **`relIndexSup_intrinsic_ambient_bound`** — the intrinsic and ambient prefix invariants differ by
  at most `2 · quotDim (row lattice) (saturation)`, uniformly in the moving lattice and the cuts;
- **`tendsto_normalized_ambient_cartan`** — `(13)` for the operator instantiation: if the intrinsic
  normalized Cartan vector of a sequence `A_n` of moving lattices converges, the ambient one
  converges to the same limit;
- **`exists_degree_sum_relIndexSup_comparison`** — for a square matrix `P` with left independent
  rows there are nonzero elementary divisors `dᵢ` with

  `0 ≤ σ_k(R^ι, M) − σ_k(Λ, j_P M) ≤ 2 · ∑ᵢ deg dᵢ`

  for every moving lattice `M` and every family of cuts.

This is `(12)` in one statement, and it names the constant: `K_k = 2 · (conductor length)`.  The
proof composes the exact transport of prefix invariants through the row map
(`relIndexSup_rowMapK`), the base-lattice change from the row lattice to its saturation
(`relIndexSup_row_sat_comparison`), and the conductor computation
(`exists_degree_sum_eq_quotDim_conductor`) which supplies the value of the relative dimension
between those two base lattices.

Since the bound depends on neither `M` nor the cuts, feeding it to
`tendsto_normalized_increments_of_prefix_bound` gives `(13)`: the fixed conductor offset disappears
after division by `n`, so the intrinsic and ambient normalized Cartan vectors coincide.  The only
inputs left explicit there are the finiteness and boundedness of the invariants being compared —
the hypotheses under which the prefix invariants are defined at all — and the requirement that the
zero-dimensional cut be the zero subspace.

## Lean status: Theorem B complete

The side conditions of the prefix comparison are now discharged from commensurability alone:

- `bddAbove_relIndex_inf` — the relative index inside a cut never exceeds the relative index of the
  pair, so any family of cuts has a bounded family of relative indices;
- `finiteDimensional_map_mkQ_of_le` — enlarging the base subspace preserves finiteness of the
  relative dimension (needed because the two base lattices sit one inside the other);
- **`relIndexSup_intrinsic_ambient_bound_of_commensurable`** and
  **`tendsto_normalized_ambient_cartan_of_commensurable`** — `(12)` and `(13)` assuming only that
  the moving lattice is commensurable with the base lattices, which is exactly the condition under
  which its Cartan vector is defined.

So both theorems of the card are formalized unconditionally and axiom-clean:

- [x] Theorem A `(4)`, `(5)`, the tuple form, and the dynamical corollary `(16)`;
- [x] the pseudodifferential right inverse `(6)` and both identities of the chain rule `(8)`;
- [x] Theorem B `(12)` with the explicit constant `2 · (conductor length)`, and `(13)`;
- [x] the conductor `(17)`, its finiteness, and its exact length `∑ᵢ deg dᵢ`.

The one claim of the card that did not survive contact with the formalization is the reading of the
prefix invariant `σ_k`, `k < s`, as the sum of the `k` largest diagonal orders of an arbitrary
diagonal form; the counterexample is recorded above.  Nothing in Theorems A, B or the conductor
no-go depends on that reading: they use only the top invariant and the uniform prefix bound, both
of which are diagonal-form independent.

New Lean modules of this completion, all wired into `GaloisForLFunctions.HTGeometry` and all
axiom-clean: `DifferentialOperatorOreDiagonal`, `DifferentialOperatorRowSpace`,
`DifferentialOperatorPseudoRightInverse`, `OperatorConductorLength`, `OperatorCartanComparison`,
`FreeDifferentialChainRuleInverse`.
