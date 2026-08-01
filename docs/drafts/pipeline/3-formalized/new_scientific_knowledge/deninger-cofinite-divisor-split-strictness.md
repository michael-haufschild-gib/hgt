# Cofinite divisor splitting and mixed-topology strictness

- **ID:** `deninger-cofinite-divisor-split-strictness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) · LEAN 4 THEOREM
- **Label:** `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Lean:** `GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorSplitting`
- **Statement:** on every cofinite arithmetic open, the weight-one
  generic-to-prime divisor row is canonically split exact; the same
  splitting remains strict in the mixed weighted \(L^1/L^2\) topology.

## Arithmetic setup

Let
\[
 U_N=\operatorname{Spec}\mathbb Z[1/N],
 \qquad
 S_N=\{p:p\mid N\},
 \qquad
 \mathcal P_N=\{p:p\nmid N\}.
\]
Write
\[
 D=\bigoplus_{p}\mathbb R[p],\qquad
 D_{S_N}=\bigoplus_{p\mid N}\mathbb R[p],\qquad
 D_{\mathcal P_N}=\bigoplus_{p\nmid N}\mathbb R[p].
\]
Unique factorization gives canonical identifications
\[
 \mathbb Q^\times/\{\pm1\}\otimes_{\mathbb Z}\mathbb R
 \simeq D,                                                         \tag{1}
\]
\[
 \mathbb Z[1/N]^\times/\{\pm1\}\otimes_{\mathbb Z}\mathbb R
 \simeq D_{S_N}.                                                   \tag{2}
\]
Under `(1)`, the Rost--Schmid divisor map on \(U_N\) is coordinate
restriction
\[
 \partial_N:D\longrightarrow D_{\mathcal P_N},
 \qquad
 (x_p)_p\longmapsto(x_p)_{p\nmid N}.                               \tag{3}
\]

## Split exactness

`[PROVED HERE] [DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS]`

Extension by zero defines maps
\[
 \iota_N:D_{S_N}\hookrightarrow D,
 \qquad
 \sigma_N:D_{\mathcal P_N}\hookrightarrow D.
\]
Then
\[
 0\longrightarrow D_{S_N}
 \xrightarrow{\iota_N}D
 \xrightarrow{\partial_N}D_{\mathcal P_N}
 \longrightarrow0                                                \tag{4}
\]
is split exact, with
\(\partial_N\sigma_N=\mathrm{id}\).  Via `(1)`--`(2)`, `(4)` is
precisely
\[
 0\longrightarrow
 \mathbb Z[1/N]^\times/\{\pm1\}\otimes\mathbb R
 \longrightarrow
 \mathbb Q^\times/\{\pm1\}\otimes\mathbb R
 \xrightarrow{\oplus_{p\nmid N}\operatorname{ord}_p}
 \bigoplus_{p\nmid N}\mathbb R
 \longrightarrow0.                                                \tag{5}
\]

### Proof

Every positive rational has a unique finite expression
\[
 q=\prod_p p^{n_p},\qquad n_p\in\mathbb Z.
\]
This proves `(1)`.  Such a rational is a unit of
\(\mathbb Z[1/N]\) exactly when \(n_p=0\) for every \(p\nmid N\),
which proves `(2)` and identifies the kernel of `(3)` with
\(D_{S_N}\).  Coordinate extension by zero is a right inverse of
`(3)`, proving surjectivity and `(4)`.

## Strict mixed completion

Fix positive weights \(w_p>0\); the Deninger normalization is
\(w_p=\log p\).  On finitely supported coordinates put
\[
 \|x\|_{1,w}=\sum_p w_p|x_p|,
 \qquad
 \|x\|_{2,w}^2=\sum_p w_p|x_p|^2,
 \qquad
 \|x\|_{\mathrm{mix}}=\|x\|_{1,w}+\|x\|_{2,w}.                    \tag{6}
\]
Let \(E_{\mathrm{mix}}\), \(E_{\mathrm{mix},S_N}\), and
\(E_{\mathrm{mix},\mathcal P_N}\) be the corresponding completions.
Coordinate restriction and both extension-by-zero maps have operator
norm at most one for each norm in `(6)`.  They therefore extend to
continuous maps, still satisfying
\[
 \partial_N\sigma_N=\mathrm{id},\qquad
 \ker\partial_N=\operatorname{im}\iota_N.                          \tag{7}
\]
The first identity makes \(\partial_N\) an open split surjection.
The second makes its kernel closed.  Hence the completed version of
`(4)` is strict exact in the complete locally convex category.  Since
\(S_N\) is finite, its kernel is finite-dimensional.

No assertion about Deninger's coarse invariant sheaf is used in this
proof.  The theorem closes the arithmetic divisor algebra and its
mixed-topology strictness after an analytic comparison has identified
the source row with these coordinates.

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerArithmeticCofiniteDivisorSplitting.lean` proves the split
exact row `(4)`--`(5)`:

- `deningerInsideDivisorEmbedding` : `ι_N`, extension by zero from the primes dividing `N`;
- `deningerOutsideResidue` : `∂_N`, coordinate restriction to the primes not dividing `N`;
- `deningerOutsideResidueSection` : `σ_N`, extension by zero from the complement;
- `deningerOutsideResidue_section` : `∂_N σ_N = id`, the splitting;
- `deningerOutsideResidue_surjective`, `deningerInsideDivisorEmbedding_injective` : the two ends
  of `(4)`;
- `deningerOutsideResidue_comp_insideDivisorEmbedding` : `∂_N ι_N = 0`;
- `deningerCofiniteDivisor_exact` : exactness in the middle, `ker ∂_N = im ι_N`.

### What is formalized and what is not

Formalized: the whole of `(4)`, hence `(5)` under the identifications `(1)`--`(2)`.  Those two
identifications are themselves formalized elsewhere in the corpus: `(1)` is
`deningerRatExp_existsUnique` in
`GaloisForLFunctions.RHTower.DeningerRationalPrimeFactorization` together with
`deningerRatExpTensorReal`, and the description of `ℤ[1/N]`-units in `(2)` is the same statement
restricted to the primes dividing `N`.

The weighted quantities of `(6)` and the operator-norm estimates are in
`GaloisForLFunctions/RHTower/DeningerWeightedMixedDivisorNorms.lean`:

- `deningerWeightedL1`, `deningerWeightedL2Sq`, `deningerWeightedMix` : `‖x‖_{1,w}`, `‖x‖_{2,w}²`
  and `‖x‖_mix` on finitely supported coordinates, for arbitrary weights `w`;
- `deningerRestrictCoords` : coordinate restriction, which is `∂_N` for `P = (· ∤ N)` and is also
  what realizes `ι_N` and `σ_N` on their images;
- `deningerWeightedL1_filter_le`, `deningerWeightedL2Sq_filter_le`,
  `deningerWeightedMix_filter_le` : restriction decreases each of the three quantities, i.e.
  operator norm at most one for each norm in `(6)`;
- `deningerWeighted_filter_of_support` : a vector already supported in `P` is unchanged by
  restriction, so extension by zero is isometric for all three;
- `deningerRestrictCoords_add_compl` : restriction to `P` and to its complement decompose a
  vector, so the row is split by coordinate maps, and
  `deningerRestrictCoords_compl_apply_eq_zero` says the two components are disjointly supported;
- `deningerWeightedMix_split_bounded` : both components have mixed quantity at most that of the
  vector.  This is what "strict" amounts to at the pre-completion level — the split surjection is
  open, with splitting bounded by one.

The bridge to the completion is under construction in
`GaloisForLFunctions/RHTower/DeningerWeightedCountingMeasure.lean`.  The weighted mixed space is
not a new Banach space to build: it is the mixed `L¹/L²` space of the weighted counting measure
`∑_p w_p δ_p` on the primes, and that space, its completeness, its dense injection into `L²` and
its continuous integral functional are already in
`GaloisForLFunctions.RHTower.DeningerAdelicKummerGelfandTriple` for an arbitrary measure.  So far:

- `deningerWeightMeasure w` : the measure `∑_p w_p δ_p`;
- `deningerWeightMeasure_lintegral` : its lower integral is the weighted sum
  `∑' p, w_p f p`;
- `deningerWeightMeasure_lintegral_abs` : on a finitely supported vector this is exactly the
  weighted `L¹` quantity `deningerWeightedL1`;
- `deningerWeightMeasure_lintegral_sq` : the same for the square and `deningerWeightedL2Sq`;
- `deningerWeightedMix_eq_lintegrals` : hence `deningerWeightedMix` is the sum of the two, read
  off the lower integrals of the weighted counting measure.

- `deningerWeightedL1_eq_eLpNorm` and `deningerWeightedL2_eq_eLpNorm` : the two quantities of
  `(6)` are literally `eLpNorm · 1` and `eLpNorm · 2` for the weighted counting measure.

So `‖·‖_{1,w}` and `‖·‖_{2,w}` are not merely analogues of `Lᵖ` norms, they are those norms, for
the measure `∑_p w_p δ_p`.  This is the identification the completion argument needs.

- `deningerMemLp_one`, `deningerMemLp_two` : a finitely supported vector lies in both `Lᵖ`
  spaces of that measure;
- `deningerToMixed` : hence it defines an element of `DeningerMixed (deningerWeightMeasure w)`,
  the mixed `L¹/L²` Banach space of the weighted counting measure;
- `deningerToMixed_norm` : and its norm there is exactly `deningerWeightedMix w x`.

So the ambient completed space of `(7)` is not a new construction: the weighted divisor
coordinates sit isometrically inside `DeningerMixed (deningerWeightMeasure w)`, which
`GaloisForLFunctions.RHTower.DeningerAdelicKummerGelfandTriple` already proves is a Banach space,
densely embedded in `L²`, carrying a continuous integral functional.

The operator that `(7)` needs on the completed space is built in
`GaloisForLFunctions/RHTower/DeningerLpIndicator.lean`.  Coordinate restriction on the completion
is multiplication by the indicator of the prime set:

- `deningerLpIndicatorFun` and `deningerLpIndicatorFun_coeFn` : the map on almost-everywhere
  classes and its defining description;
- `deningerLpIndicatorFun_add`, `deningerLpIndicatorFun_smul` : linearity;
- `deningerLpIndicatorFun_norm_le` : it does not increase the `Lᵖ` norm;
- `deningerLpIndicator` : hence a bounded operator `Lp ℝ p μ →L[ℝ] Lp ℝ p μ` of norm at most
  one, with `deningerLpIndicator_norm_le`;
- `deningerLpIndicator_add_compl` : the restrictions to a set and its complement decompose the
  identity — the completed form of `deningerRestrictCoords_add_compl`.

This is stated for an arbitrary measure and exponent, so it applies to both factors of the mixed
space at once.

`GaloisForLFunctions/RHTower/DeningerMixedIndicator.lean` induces that operator on the mixed
space:

- `deningerMixedIndicatorAmb` : the indicator applied in both components of the ambient product,
  bounded by one;
- `deningerMixedIndicatorAmb_mem` : the mixed carrier is stable, because the two components of a
  mixed element agree almost everywhere and are hit by the same indicator;
- `deningerMixedIndicator` : hence a bounded operator of norm at most one on
  `DeningerMixed μ`;
- `deningerMixedIndicator_add_compl` : restriction to a set and to its complement decompose the
  identity of the mixed space.

That is `(7)` on the completed space, in operator form: `∂_N` is `deningerMixedIndicator` for the
primes not dividing `N`, `ι_N` is the same for the primes dividing `N`, they are bounded by one,
and they split the identity — so the row is strict, its kernel is closed and is the image of the
complementary projection.

The split itself is then read off:

- `deningerMixedIndicator_idem` : restriction is idempotent, which is `∂_N σ_N = id` — `σ_N` is
  the inclusion of the range, and `∂_N` is the identity on it;
- `deningerMixedIndicator_compl_comp` : restricting to a set and then to its complement is zero,
  i.e. `∂_N ι_N = 0`;
- `deningerMixedIndicator_range_eq_ker_compl` : the image of one restriction is exactly the kernel
  of the complementary one, which is `ker ∂_N = im ι_N` after completion;
- `deningerMixedIndicator_isClosed_ker` : that kernel is closed.

So `(7)` holds on the completed space: the maps are bounded by one, the splitting is bounded, the
kernel is closed and is the image of the complementary projection — the row is strict.  The two
summands `E_{mix,S_N}` and `E_{mix,P_N}` are the ranges of the two projections.

### Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticCofiniteDivisorSplitting.lean`
  — passes with no errors and no warnings.
- Cached module build:
  `lake build GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorSplitting` completes.
- Scratch `#print axioms` on the five theorems of the splitting module and on all eleven
  declarations of the weighted-norm module: only the Lean/mathlib standard `propext`,
  `Classical.choice`, and `Quot.sound`.
- Cached module build of the weighted-norm module:
  `lake build GaloisForLFunctions.RHTower.DeningerWeightedMixedDivisorNorms` completes
  (1996 jobs).
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: divisor row isolated on a cofinite open
- [x] 1 → 2 fully-proven: split exactness and mixed strictness proved
- [x] 2 → 3 formalized, split exact row `(4)`--`(5)`
  (`GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorSplitting`)
- [x] 2 → 3 formalized, the weighted quantities of `(6)` and the operator-norm-at-most-one
  estimates (`GaloisForLFunctions.RHTower.DeningerWeightedMixedDivisorNorms`)
- [x] 2 → 3 formalized, the bounded splitting of `(4)` in the mixed quantities
  (`deningerRestrictCoords_add_compl`, `deningerWeightedMix_split_bounded`)
- [x] 2 → 3 formalized, the weighted counting measure and the identification of both quantities
  of `(6)` with `eLpNorm` (`GaloisForLFunctions.RHTower.DeningerWeightedCountingMeasure`)
- [x] 2 → 3 formalized, the isometric placement of the weighted divisor coordinates in the mixed
  `L¹/L²` Banach space (`deningerToMixed`, `deningerToMixed_norm`)
- [x] 2 → 3 formalized, the completed restriction operator
  (`GaloisForLFunctions.RHTower.DeningerLpIndicator`)
- [x] 2 → 3 formalized, `(7)` on the completed space
  (`GaloisForLFunctions.RHTower.DeningerMixedIndicator`)
- [ ] 3 → 4 publication-ready: integrate with the analytic comparison that identifies the source
  row with these coordinates

## Consequence for the source conjecture

Sub-conjecture `DAC_COFINITE_SUSPENSION_SECTION_AMPLITUDE` now splits
into:

1. `[CLOSED]` algebraic divisor exactness on every \(U_N\);
2. `[CLOSED]` strictness of the mixed coordinate completion;
3. `[OPEN CORE]`
   `DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON`: construct a
   functorial quasi-isomorphism from derived sections of Deninger's
   already-formed coarse invariant sheaf to the two-row analytic
   Kummer complex whose weight-one horizontal row is `(5)`.

Only item 3 is geometric.  Exodromy, derived group invariants, a bar
complex, and quotient-stack cohomology do not enter.

## Hostile audit

- A finite-stage endpoint complex supported only on \(S_N\) is not
  `(5)`: the residue target consists of primes outside \(S_N\).
- Split exactness of `(5)` does not compare pro-Stein derived sections
  with ordinary derived sections on the nonproper coarse suspension.
- The theorem treats the weight-one divisor row.  It does not prove
  the analytic row-\(0/1\) identification, real signature boundary,
  cup duality, Lefschetz trace, or Hodge positivity.
- Bare \(L^2\) still does not encode the product formula.  Strictness
  here uses the mixed topology containing the \(L^1\) norm.
- No zeta zero, \(\Xi\)-defined space, RH premise, or numerical
  computation occurs.

**Verdict:** `FULLY PROVEN ON PAPER; ABSTRACT PRIME-COORDINATE EXACTNESS
FORMALIZED UNCONDITIONALLY; ARITHMETIC UFD INSTANTIATION AND ANALYTIC
COMPARISON REMAIN FOR LEAN/SOURCE CLOSURE`.

## References

- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Perverse homotopy heart and MW-modules*:
  https://arxiv.org/abs/2210.14832
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-27 — extracted the actual cofinite-open divisor sequence,
  corrected the inside/outside-prime orientation of the earlier finite
  endpoint page, and proved strict mixed-topology splitting.

## Log

- 2026-08-01 — Verified and axiom-audited the existing module, which proves the split exact row
  `(4)`--`(5)` in full.  Split the formalization gate: the mixed-topology strictness `(6)`--`(7)`
  is still open and needs the weighted mixed norm bundled as a normed space.
- 2026-08-01 — Added the weighted mixed norms and the three contraction estimates of `(6)`.
- 2026-08-01 — Ran the deferred verification of that module: cached build green, axiom audit
  clean on all eleven declarations.  `(6)` is now fully formalized; only the completions and
  `(7)` remain.
- 2026-08-01 — Added the bounded splitting: restriction to a prime set and to its complement
  decompose a coordinate vector, and both components are bounded by the whole in the mixed
  quantity.  That is the strictness content of `(7)` before completion.  Recorded that the
  completion itself can reuse the mixed `L¹/L²` Banach space already in the corpus, taken over the
  weighted counting measure, rather than being rebuilt.
- 2026-08-01 — Started the completion bridge rather than rebuilding a normed space: introduced the
  weighted counting measure, computed its lower integral as a weighted sum, and identified the
  weighted `L¹` quantity with it.  The `L²` identification is the same computation for the square
  and is the next step; after it, `(7)` follows from the mixed `L¹/L²` Banach space already built.
- 2026-08-01 — Completed the measure-side identification: both summands of `(6)` are now proved
  to be lower integrals of the weighted counting measure.  What is left for `(7)` is `eLpNorm`
  bookkeeping, not analysis.
- 2026-08-01 — Identified both quantities of `(6)` with `eLpNorm` for the weighted counting
  measure, so the weighted mixed norm is the mixed `L¹/L²` norm of an actual measure.  What is
  left for `(7)` is assembling the isometry, not further analysis.
- 2026-08-01 — Placed the weighted divisor coordinates isometrically inside the mixed `L¹/L²`
  Banach space of the weighted counting measure, so the completed ambient space of `(7)` is
  inherited rather than constructed.  Remaining: the closures of the two coordinate subspaces and
  transport of the two identities by continuity.
- 2026-08-01 — Located the single remaining obstruction for `(7)`: coordinate restriction must
  exist as a bounded operator on the completed space, i.e. the indicator endomorphism of `Lᵖ`.
  Verified that mathlib has both ingredients (`MemLp.indicator`, `eLpNorm_indicator_le`), so this
  is construction rather than search.  Not started here rather than started and left half-built.
- 2026-08-01 — Built the completed restriction operator: multiplication by the indicator of a
  measurable set is a bounded linear operator of norm at most one on `Lᵖ`, and the operators of a
  set and its complement decompose the identity.  Stated for an arbitrary measure and exponent, so
  it covers both factors of the mixed space.
- 2026-08-01 — Induced the restriction operator on the mixed space: bounded by one, carrier
  stable, and the operators of a set and its complement split the identity.  `(6)`--`(7)` are now
  formalized in operator form; what remains is naming the two summand subspaces, not mathematics.
- 2026-08-01 — Closed `(7)`: idempotency gives `∂σ = id`, the complementary composite is zero,
  the image of one restriction is the kernel of the other, and that kernel is closed.  Both halves
  of the card — the split exact row and its mixed-topology strictness — are now unconditional in
  Lean 4.
