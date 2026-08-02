# Hypertranscendental clock incompressibility under differential embeddings

- **ID:** `hypertranscendental-clock-incompressibility`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL DIFFERENTIAL-FIELD THEOREM / IMMERSION-RIGIDITY LAW
- **Scientific status:** `[PROVED HERE] [LEAN ASYMPTOTIC KERNEL FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL]`
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
- [ ] 2 -> 3: scalar and finite-vector bounded-comparison kernels and free-transverse saturation
  are formalized; the Frechet/Ore instantiation and valuation-lattice derivation of `(12)` remain
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
