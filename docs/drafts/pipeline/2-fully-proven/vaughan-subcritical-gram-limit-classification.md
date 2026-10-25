# Subcritical Vaughan Gram limits form a discrete set away from zero

- **ID:** vaughan-subcritical-gram-limit-classification
- **Stage:** 2-fully-proven
- **Type:** CLAIM (Lean verification pending)
- **Verification:** UNPROVED. The argument below is not a certified result until its Lean proof and transitive axiom audit pass; checked component lemmas are identified separately.
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs
- **Statement:** Below half damping, all moving-cutoff normalized Gram limits form a countably infinite compact rank-one family whose only accumulation point is zero.

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

## Dependency-closed paper proof

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
- [ ] Exact Lean formalization and transitive axiom audit.
- [ ] Final direct leaf checks and corpus integration.

## Status

The corpus search found the fixed-cutoff and leading-mean Gram laws, but no
matching subcritical limit-set classification. This is an internal novelty audit;
no external novelty claim. The harmonic nonvanishing and boundedness leaves are
checked. The uniform Gram theorem is fully checked in
`UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean`. The arithmetic set's
fourteen targets are fully checked in `TheCompactArithmeticAmplitudesOfVaughanGrams.lean`:
bounds, countability, compactness, finite
cutoff control away from zero, arbitrarily small positive amplitudes, and
infinitude, exact eventual amplitude and finite-fiber rigidity, and the positive-cutoff
escape equivalence. Producing and final direct checks passed; all fourteen
transitive axiom audits contain only standard axioms. The module is wired and
its scratch removed. Eight targets in
`TheSubcriticalVaughanGramLimitSet.lean` prove diagonal recovery,
the full matrix classification, nonzero-limit rigidity, the zero-limit escape
equivalence, the convergence dichotomy, attainment with positive cutoffs, and
the already stated independent-horizon packet-energy limit. Corrected producing
and final direct checks passed, with only standard transitive axioms. The module
is wired and its scratch removed. Four targets in
`TheOnlyAccumulationOfVaughanAmplitudesIsZero.lean` prove finiteness above a positive
level, isolation of positive amplitudes, and the exact accumulation-point
classification, plus the paper's mutual exclusion of product escape and an
eventually fixed positive amplitude. Producing and final direct checks passed,
with only standard transitive axioms; the module is wired and its scratch removed.
Four targets in `/tmp/QIVaughanLimitMatrixRankTools.lean` draft
the zero matrix, the outer-product rank bound, positive-amplitude rank one, and
the complete rank dichotomy. Two rank targets need corrected elaboration before certification.

The matrix-family topology stated above still needs exact Lean declarations:
the existing topology draft treats the scalar amplitude set only. The additional
leaf `TheTopologyOfSubcriticalVaughanGramLimits` must transfer compactness,
countability, infinitude, and the unique accumulation point through the actual
smooth matrix map, whose positive diagonal coefficient makes it injective.
Nine targets are now drafted in `/tmp/QIVaughanMatrixTopologyTools.lean`:
continuity, diagonal injectivity, compactness, countability, infinitude, unique
zero accumulation, exact attainment with positive or arbitrary cutoffs, and
damping independence after the stated scalar normalization. The neighborhood
proof uses continuous diagonal recovery to transfer scalar isolation. All nine
remain uncompiled. This closes draft coverage of an existing paper obligation;
it certifies no consequence until Lean checks pass.
