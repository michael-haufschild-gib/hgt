# SC: complete-family realization and coupling

- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-0111/route-SC.md`.
- **Goal:** Resolve the seven main obligations and four heat obligations, with unconditional Lean proofs.

## Current obligations

1. Realize rational correlation Grams by smooth packets of the complete Weil family, including normalization and the boost-mass-zero constraint. Distinguish a multiple chosen for each finite family from one multiple valid for every family.
2. Exclude bounded cone coupling with unattained maximal zero width.
3. Exclude finite nonzero Weil index.
4. Transfer finite-sieve Hodge positivity to the global inter-tower form.
5. Prove an arithmetic finite-index ceiling.
6. Prove a square decomposition for the dilation form itself.
7. Prove glued index at most one, equivalently bounded two-prime lattice coupling.

Heat: certified upper-time calibration; subcritical heat count; uniform heat count; absence of index jumps on `(0, 1/8]`.

## Verified boundary

`exists_ratCorr_completeWeil_gram_limit` realizes each finite rational Gram as a normalized complete-matrix compression using the smooth unit Steklov profile at `2K·loglog N·(logloglog N)²`, with the positive atom mass restored. Its `K` depends on that family; it does not provide a universal fixed multiple.

`riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log` gives the smooth complete-family receiver at `2(log N)^α`, every `α>0`. Neither result proves positivity.

## Complete-matrix normalization

Set `φ(u)=2·steklovDCProfile(2u−1)`, `w=c/N`, and `G=∫φ(u/w)² du>0`.
An atomic coefficient vector `x` becomes `v_n=x_n/w` in the complete matrix.
Its mixed Weil pairing is exactly `G⟨A_N(c)v_i,v_j⟩`. Thus the existing rational
Gram limit at dilation `N/(K·dcScale N)` gives a literal complete-matrix
compression limit at overlap `2K·dcScale N`.

Lean: `TransMetzlerWeilPositivity/ReceiverRate/ABoundedOverlapRateSeesASemilocalWindow.lean`,
`exists_ratCorr_completeWeil_gram_limit`.
Direct compilation passed; only `propext`, `Classical.choice`, and `Quot.sound`.
Exact preservation of the boost
hyperplane is not yet supplied by this Gram limit.

The global hyperplane implication can instead pass through inertia: positivity
on one real hyperplane bounds the complexified matrix index by one; compression
and finite-Gram limits retain that bound. The rational Weil index equals the
zeta index, whose nonzero values are at least two. This avoids requiring the
packet approximation to preserve the pole moment. Lean inputs:
`hermQuad_map_ofReal`, `hermNegIndex_le_negIndexOn_ker_add_one`,
`eventually_le_hermNegIndex`, `negIndex_ratCorr`, `negIndex_zetaKernel_le_one_iff`.
The resulting receiver quantifies over every fixed critical multiple.
`riemannHypothesis_iff_steklovUnitProfile_hodgeIndex_critical` and
`ratCorr_hyperplane_nonneg_iff_steklovUnitProfile_hodgeIndex_critical` in
`RenormalizedIntersectionTheory/TheHodgeIndexAtCriticalOverlap.lean` pass direct
Lean verification with only `propext`, `Classical.choice`, and `Quot.sound`.
The leaf is wired into its umbrella. Positivity at this scale and a single
universal multiple remain unproved.

## Universal-multiple conjecture

Construct one smooth unit profile `ψ`, supported in `[-1,1]`, with
`∀ B>0, ∃ A, ∀q, ∫|ψ⁽q⁾| ≤ A·B^q·q!·log(q+3)^(2q)`.
The synthesis threshold is `K>24e·B·blockSize(R+1)`, while `A` affects only
the error constant. Choosing `B` after the finite support radius `R` would
therefore realize every rational Gram at the same `K=1` with this fixed profile.

Candidate construction: Steklov averages with telescoping radii
`r_j=(1/√log(j+3)−1/√log(j+4))/8`. The sum is at most `1/8`.
The log increment bound and rationalization of the square roots give
`r_j≥1/(16(j+4)·log(j+4)·√log(j+4))`. Consequently,
`∏_{j<q}r_j⁻¹ ≤ (64/√log(q+3))^q·dcLogWeight(q)`.
Uniform derivative limits give the displayed profile estimate; the
factor `64/√log(q+3)` tends to zero and finitely many derivative orders are
absorbed into `A`. This changes the profile, not the complete Weil form or
the prescribed critical scale.

`AProfileAtEveryLogarithmicType.lean` formalizes the radius bound, nonnegative
smooth limit, unit mass, and `exists_beurlingDCProfile_bound`. Compilation and
the displayed transitive axiom audits pass with only `propext`,
`Classical.choice`, and `Quot.sound`. The universal-multiple complete Gram
realization and hyperplane equivalence await verification.

## Heat calibration

`negIndex_heatArchState_eq_one_of_eighth_le` already gives index one for
every `c>0` and `t≥1/8` in `TheHeatDeformedArchimedeanState.lean`.
This supplies the requested upper-time calibration at the classical bound;
its transitive axiom audit uses only `propext`, `Classical.choice`, and
`Quot.sound`. The same audit passes for
`riemannHypothesis_iff_negIndex_heatArchState_const`. The subcritical count,
uniform count, and no-jump obligations remain separate.

`exists_nonrealZeroCount_and_collisionMass_le_twoThirds` bounds the count by
`C·R(t)·log(2+3R(t))`, where `R(t)=max(X₀,2π·exp((2/3+ε)/t))+1`.
The `2/3` improves the coefficient of `1/t`, not its power; this does not
supply the requested `exp(A·t^(−a))` with `a<1`.

## Cone obstruction

The existing double-pole argument requires an attained maximal real part.
Below the supremum its geometric expansion diverges for deeper zeros.
Continuation across the boundary does not by itself isolate residues of an
infinite accumulating pole series. A quantitative lower weight versus joint
two-prime spacing estimate remains necessary for that argument.

`two_prime_alias_bound_in_Δ` supplies the arithmetic separation
`|Δ log p−2πk₁| log q + |Δ log q−2πk₂| log p ≥ c·min(|Δ|,(2+|Δ|)^(−C))`.
It controls the two phase clocks, but does not bound cancellation of spline
residues as their real parts approach an unattained supremum.

`le_norm_paperFT_upow` already gives the spline transform bound
`(|sinh(Im z)|/‖z‖)^4 ≤ |B̂(z)|`. Thus polynomial nonvanishing away from the
critical line is available. The missing comparison concerns approach to the
width supremum versus height and cancellation; neither this bound nor the
two-prime separation estimate supplies it.

## Gates

- [x] Exact requested scope recorded.
- [x] Complete-family realization at family-dependent multiples and the all-multiples hyperplane equivalence audited.
- [ ] A single universal critical multiple, if required by obligation 1.
- [x] Existing heat calibration audited at `t≥1/8`.
- [ ] Remaining source estimates proved.
- [ ] Exact Lean statements, direct checks, standard-only axiom audits, umbrella imports.
