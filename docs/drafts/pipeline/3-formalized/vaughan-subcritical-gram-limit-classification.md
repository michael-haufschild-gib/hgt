# Subcritical Vaughan Gram limits form a discrete set away from zero

- **ID:** vaughan-subcritical-gram-limit-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Verification:** All 39 public targets in five supporting leaves passed final direct checks and transitive axiom audits, with only standard axioms.
- **Source:** ../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Below half damping, all moving-cutoff normalized Gram limits form a countably infinite compact family of rank at most one whose only accumulation point is zero.

## Goal

Classify every possible limit of the actual centered Vaughan Gram after division
by its trivial power. This is a consequence of the uniform smooth Gram law and
does not provide a fixed power saving or resolve Q-I.

## Statement

For `0<ε<1/2`, put `β=1-2ε`, `c=subHalfZetaCoeff(ε)`,
`H_N=Σ_(d≤N)μ(d)/d`, and `s=(0,0,-1,1,0)`. Define

`S={H_U²H_V² : U,V∈ℕ}`.

All finite limits of
`G^c(H(t);U(t),V(t))/H(t)^β`, with `H(t)→∞`, are exactly

`{(c²/β) a ssᵀ : a∈S}`.

The same limit set results if both cutoff schedules must remain positive.
The arithmetic set `S` is compact and countably infinite, contained in
`[0,1]`, containing `0` and `1`, with `0` as its only accumulation point.
Every positive value is isolated. A nonzero limiting matrix forces the cutoff
pair eventually to lie in one fixed finite fiber
`{(U,V) : H_U²H_V²=a}`. In particular, both cutoffs remain eventually bounded
and the leading amplitude is eventually exactly constant. Positive limits have
rank one; the zero limit has rank zero.

## Proof mechanism

The checked uniform Gram theorem gives, for every `i,j`,

`G^c_ij(H(t);U(t),V(t))/H(t)^β
 = (c²/β) a_t s_i s_j + o(1)`,

where `a_t=H_(U(t))²H_(V(t))²∈S`; the error is uniform in the cutoffs.
The checked harmonic facts are `H_0=0`, `H_1=1`, `|H_N|≤1`, `H_N→0`, and
`H_N≠0` for positive `N`. The read `subHalfZetaCoeff_ne_zero` gives `c≠0`;
thus `c²/β>0`.

**Finiteness away from zero.** Fix `δ>0`. Since `H_N→0`, choose `N_δ`
so that `|H_N|<sqrt(δ)` for `N≥N_δ`. If `H_U²H_V²≥δ`, then
`H_U²≥δ` and `H_V²≥δ`, because each other squared factor is at most one.
Hence both `U,V<N_δ`. The set of cutoff pairs with amplitude at least `δ`
is finite, so its set of amplitudes is finite.

**Compactness and accumulation.** The set `S` lies in `[0,1]`. Any nonzero
candidate accumulation point `a>0` has a neighborhood whose intersection with
`S` lies in the finite set `S∩[a/2,1]`; hence it is not an accumulation point.
For the same reason, every nonzero point outside `S` has a neighborhood
avoiding `S`. Points below zero or above one are excluded by the interval
bound, and zero is already in `S`. Thus `S` is closed and bounded, hence
compact. It is countable as the image of `ℕ²`. Taking `V=1` gives the positive
values `H_N²→0` for positive `N`. They cannot form a finite set, since a finite
set of positive reals has positive minimum. Therefore `S` is infinite and
zero is its unique accumulation point.

**Necessity for matrix limits.** Suppose the normalized Gram tends entrywise
to `L`. Since `s_2²=1`, its `(2,2)` entry and the uniform error show
`a_t→a=(β/c²)L_22`. Closedness of `S` gives `a∈S`. Every other entry then
gives `L_ij=(c²/β)a s_i s_j`.

**Attainment.** For `a>0` in `S`, any representing cutoff pair is positive
and constant schedules attain the proposed matrix by the uniform Gram law.
For zero, choose the positive cutoffs `U(t)=V(t)=t+1`; the separate horizon
and product-divergence theorem gives the zero matrix for every `H(t)→∞`.
Thus requiring positive cutoffs does not change the limit set.

**Rigidity at a nonzero limit.** If `a>0`, then eventually `a_t≥a/2`, so
both cutoffs lie in one fixed finite rectangle. Since `a` is isolated in `S`
and `a_t→a`, eventually `a_t=a` exactly. The pair therefore eventually lies
in the fixed finite fiber over `a`. Rank one for positive `a` follows from
the nonzero vector `s`; rank zero at `a=0` is immediate.

## New insight

Below half damping, the complete set of limiting normalized Grams is an
arithmetic compact set, discrete away from zero. The set is independent of
positive subcritical damping after division by `c²/β`. Moving cutoffs cannot
produce a new nonzero limiting amplitude: every such amplitude already occurs
at fixed positive cutoffs. This differs from the continuum of critical
harmonic Gram limits in the half-damping paper. Neither statement establishes
a fixed power saving.

## Gates

- [x] Source-pure conjecture and proof mechanism recorded.
- [x] Corpus novelty search and statement audit.
- [x] Dependency-closed paper proof.
- [x] Exact Lean formalization and transitive axiom audit.
- [x] Final direct leaf checks and corpus integration.

## Lean verification

All modules belong to `GaloisForLFunctions.BezoutValuationIncidence`.

| Lean module | Public targets | Exact coverage |
| --- | --- | --- |
| [TheCompactArithmeticAmplitudesOfVaughanGrams](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheCompactArithmeticAmplitudesOfVaughanGrams.lean) | 14 | Interval bounds, endpoints, compactness, countable infinitude, cutoff control, finite-fiber rigidity, positive-cutoff escape equivalence. |
| [TheSubcriticalVaughanGramLimitSet](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheSubcriticalVaughanGramLimitSet.lean) | 8 | Diagonal recovery, exact limit classification and positive-cutoff attainment, zero-limit converse, convergence dichotomy, finite-fiber rigidity, independent-horizon packet-energy decay. |
| [TheOnlyAccumulationOfVaughanAmplitudesIsZero](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheOnlyAccumulationOfVaughanAmplitudesIsZero.lean) | 4 | Finiteness above a positive level, isolation, unique scalar accumulation point, mutual exclusion of the convergence alternatives. |
| [TheRanksOfSubcriticalVaughanLimits](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheRanksOfSubcriticalVaughanLimits.lean) | 4 | Zero matrix, outer-product rank bound, rank one at positive amplitude, exact rank dichotomy. |
| [TheTopologyOfSubcriticalVaughanGramLimits](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheTopologyOfSubcriticalVaughanGramLimits.lean) | 9 | Continuous injective matrix map, compactness, countability, infinitude, unique zero accumulation, exact positive/arbitrary-cutoff attainment, normalized damping independence. |

The complete finite limit set is `pmPronicVaughanCentredGram_limit_set_eq`;
its set-valued forms are `mem_pmVaughanSmoothLimitSet_iff` and
`mem_pmVaughanSmoothLimitSet_iff_arbitrary_cutoffs`. The exact rank is
`rank_pmVaughanSmoothLimitMatrix`. The matrix topology and normalization are
`accPt_pmVaughanSmoothLimitSet_iff` and
`normalized_pmVaughanSmoothLimitSet_independent`.

Each leaf passed `lake --old env lean` directly from `formal/`. Every listed
target has a `#print axioms` audit containing only `propext`, `Classical.choice`,
and `Quot.sound`. All five imports are wired into the programme umbrella;
the owned proof scratches were removed. No theorem uses a proof placeholder,
trusted-computation shortcut, raised limit, or additional analytic premise.

The corpus search found the older fixed-cutoff and leading-mean Gram laws,
but no matching complete subcritical limit-set classification. This is an
internal audit, not an external novelty claim. Full Q-I remains open.
