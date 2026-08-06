# Groskin archimedean tail order without numerical certification

- **ID:** `groskin-archimedean-tail-order-no-computation`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Akiva Groskin, arXiv:2607.02828, Lemma 3.1 and Theorem 3.2
- **Statement:** Past an analytically produced finite threshold, the omitted CCM archimedean tail is an explicit positive-semidefinite Cauchy--Stieltjes Gram increment; no numerical value of the digamma density is used.

## Goal

Import the exact finite tail-order mechanism used by Route B while respecting the corpus rule that
no numerical computation may discharge a sign. The theorem gives a source-defined Loewner-positive
archimedean correction against which the local rectangular boundary charge can be compared. It
does not assert Weil positivity or RH.

## Gates

- [x] 0 → 1 in-progress: source-faithful statement, exact carrier, analytic proof strategy
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, `lake env lean` and final module build green
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate

## Source objects

Put

\[
  h_+(T)=\Re\psi\!\left(\frac14+\frac{iT}{2}\right)-\log\pi.
\]

For a positive scale `rho`, a finite real node family `x_i`, and `T/rho` outside every node, put

\[
  p_T(i)=\frac1{T/\rho-x_i},\qquad
  q_T(i)=\frac1{T/\rho+x_i}.
\]

For `0 < L`, the exact Groskin density is

\[
  K_T(i,j)=
  \frac{h_+(T)\sin^2(LT/2)}{\pi^2\rho}
  \bigl(p_T(i)p_T(j)+q_T(i)q_T(j)\bigr).
\]

The tail increment on `[T1,T2]` is its entrywise integral.

## Paper proof

`[PROVED HERE]`

### 1. Eventual positivity of the literal digamma density

The corpus theorem `re_digamma_vertical_tendsto_atTop` gives

\[
  \Re\psi\!\left(\frac14+i t\right)\longrightarrow +\infty.
\]

Composition with `t=T/2`, which tends to `+∞`, and subtraction of the constant `log pi` give

\[
  h_+(T)\longrightarrow +\infty.
\]

Hence there is a finite `T0` such that `0 < h_+(T)` for every `T ≥ T0`. This replaces Groskin's
interval-certified value `h_+(7)>0` by a purely analytic, noncomputational threshold. It weakens
only the explicit cutoff `7`; the source density and all later identities are unchanged.

### 2. Pointwise Gram identity

For every coefficient vector `c`, direct expansion gives

\[
  \sum_{i,j}\overline{c_i}K_T(i,j)c_j
  =
  \frac{h_+(T)\sin^2(LT/2)}{\pi^2\rho}
  \left(
    \left|\sum_i c_i p_T(i)\right|^2+
    \left|\sum_i c_i q_T(i)\right|^2
  \right).
\]

Past `T0`, and while `T/rho` avoids the finite node set, every scalar factor is nonnegative.
Therefore `K_T` is positive semidefinite.

### 3. Integrated Loewner order

On a compact interval `[T1,T2]` lying strictly past the threshold and the node poles, every entry is
continuous and integrable. Entrywise integration preserves Hermitian positive semidefiniteness,
so

\[
  \Delta_{T_1,T_2}=\int_{T_1}^{T_2}K_T\,dT\succeq0.
\]

This is the unconditional Loewner-order part of Groskin Theorem 3.2. Strict positive definiteness
and strict total positivity are separate stronger claims requiring rational separation and the
Cauchy determinant/Andreief argument; they are not asserted by this card.

## Approach

1. Reuse the corpus's unconditional vertical-digamma limit.
2. Define the literal `h_+`, `p_T`, `q_T`, rank-two kernel, and compact-interval increment.
3. Reuse `HTGeometry.integralMatrixKernel_posSemidef` for the integrated order theorem.
4. Wire the finished module into `RHTower.lean`.

## No-go closure

- **Exact killing theorem/mechanism:** the published cutoff `7` depends on an interval evaluation of `h_+(7)` and is disallowed under the no-computation rule.
- **Strongest positive survivor:** eventual literal-density positivity and the exact source-specific Cauchy--Stieltjes Gram increment need no numerical input.
- **New insight:** Route B needs the tail's order and budget mechanism, not the special integer `7`; an analytic threshold preserves the mechanism.
- **Status:** dependency-closed paper proof of the semidefinite Loewner order; ready for Lean. Strictness and total positivity are separate follow-on claims.

## Log

- 2026-08-01 — created in 1-in-progress from exact external theorem; computation-certified cutoff replaced by analytic eventual threshold.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/GroskinArchimedeanTailOrder.lean`
(wired into `GaloisForLFunctions/RHTower.lean`).

| Paper step | Lean declaration |
|---|---|
| **the card's Statement line, as one theorem** | `RHTower.groskinArchimedeanTailStatement` |
| literal density `h_+` | `RHTower.groskinArchimedeanDensity` |
| §1 divergence of the literal density | `RHTower.tendsto_groskinArchimedeanDensity_atTop` |
| §1 analytic (noncomputational) threshold | `RHTower.exists_groskinArchimedeanDensity_pos_threshold`, `RHTower.groskinArchimedeanPositivityThreshold`, `RHTower.groskinArchimedeanDensity_pos_of_threshold` |
| Cauchy features `p_T`, `q_T` | `RHTower.groskinArchTailMinusFeature`, `RHTower.groskinArchTailPlusFeature` |
| exact rank-two density `K_T` | `RHTower.groskinArchTailKernel` |
| §2 pointwise Gram positivity | `RHTower.groskinArchTailKernel_posSemidef` |
| pole-free window | `RHTower.groskinArchTail_denominators_pos`, `RHTower.continuousOn_groskinArchTailKernel_apply`, `RHTower.integrable_groskinArchTailWindowKernel_apply` |
| §3 integrated Loewner order `Δ ⪰ 0` | `RHTower.groskinArchTailIncrement_posSemidef` |
| **the kernel of the increment's form**: it vanishes at a vector exactly when the Cauchy Gram vanishes a.e. on the window | `RHTower.groskinArchTailIncrement_quadraticForm_eq_zero_iff`, `.groskinArchTailScalarGram`, `.integrableOn_groskinArchTailScalarGram` |
| **the kernel annihilates both Cauchy features** off the sine zeros | `RHTower.groskinArchTailIncrement_quadraticForm_eq_zero_annihilates` |
| **the increment's Cauchy--Stieltjes representation**: `x* Δ x = ∫_window w(T)(\|Σ x p_T\|² + \|Σ x q_T\|²) dT` | `RHTower.groskinArchTailIncrement_quadraticForm` |
| **§2 displayed Gram identity** `Σ c̄ K c = w(\|Σ c p\|² + \|Σ c q\|²)` | `RHTower.groskinArchTailKernel_quadraticForm` |
| the density has rank at most two | `RHTower.groskinArchTailKernel_rank_le_two` |
| **the density has rank exactly two** | `RHTower.groskinArchTailKernel_rank_eq_two` |
| **its column space is exactly the span of the two Cauchy features** | `RHTower.range_groskinArchTailKernel_eq_span` |
| the two Cauchy features are independent when two nodes differ | `RHTower.linearIndependent_groskinArchTailFeatures`, `RHTower.cauchyPair_combination` |
| the scalar density is nonzero off the sine zeros | `RHTower.groskinArchTailWeight_ne_zero` |
| strict Cauchy--Schwarz: the Gram determinant of an independent pair (absent from mathlib) | `GaloisForLFunctions.HTGeometry.gramDet_pos_of_linearIndependent` |
| a two-term Gram sum of independent features has rank exactly two | `GaloisForLFunctions.HTGeometry.rank_gramPair_eq_two`, `.span_pair_le_range_gramPair` |
| nonzero scaling preserves the rank | `GaloisForLFunctions.HTGeometry.rank_smul_eq` |
| **nonvacuity of the exact rank**: a legal cutoff off the sine zeros always exists | `RHTower.exists_groskinArchTailKernel_rank_eq_two`, `RHTower.exists_sin_ne_zero_ge` |
| **its column space is spanned by the two Cauchy features** | `RHTower.range_groskinArchTailKernel_le_span` |
| the action of a Cauchy outer product | `RHTower.vecMulVec_mulVec_self`, `RHTower.smul_mulVec_eq` |
| rank subadditivity, finite sums and scaling (absent from mathlib) | `GaloisForLFunctions.HTGeometry.rank_add_le_rank_add_rank`, `.rank_sum_le`, `.rank_smul_le` |
| **the tail order itself**: shrinking the window lowers the increment in the Loewner order | `RHTower.groskinArchTailIncrement_mono` |
| **nonvacuity**: every scale and node family admits a legal window | `RHTower.exists_groskinArchTailWindow` |
| **nonvacuity of the order**: that window carries a positive semidefinite increment | `RHTower.exists_groskinArchTailIncrement_posSemidef` |
| entrywise integration is additive on differences | `HTGeometry.integralMatrixKernel_sub` |

All four headline declarations report
`[propext, Classical.choice, Quot.sound]` under `#print axioms`; no numerical
evaluation, no added axiom, no open hypothesis beyond the stated finite geometry
(`0 < ρ`, threshold, node-freeness of the window).

- 2026-08-05 — Lean surface verified green (`lake env lean`), axioms clean, card advanced to 3-formalized.
- 2026-08-06 — §2's displayed Gram identity and the rank-two property proved.  The positive
  semidefiniteness had been obtained from the outer-product form directly; the identity itself, and
  the statement that the column space is spanned by the two Cauchy feature vectors, are what make
  the increment an *explicit* rank-two Cauchy--Stieltjes Gram rather than an unstructured positive
  matrix.  Rank subadditivity `rank (A + B) ≤ rank A + rank B` and `rank (c • A) ≤ rank A` are
  absent from mathlib and were built from the column-space modular law
  (`formal/GaloisForLFunctions/HTGeometry/MatrixRankSubadditive.lean`).
- 2026-08-06 — the order in the card's title formalized: for nested cutoff windows the increments
  are Loewner-monotone, `Δ_{T₁',T₂'} ⪯ Δ_{T₁,T₂}`, because their difference is the integral of the
  same density over the discarded part of the window, where it is still positive semidefinite.  The
  supporting additivity of entrywise integration was added to `PSDMatrixSpectralHankel`.
- 2026-08-06 — the rank layer completed with the finite-sum bound `rank (∑ A_a) ≤ ∑ rank (A_a)`,
  which is the general shape behind the rank-two claim: an explicitly presented finite Gram sum has
  rank at most the total rank of its terms.
- 2026-08-06 — nonvacuity certified.  The Loewner theorems carry three hypotheses (positive scale,
  window past the analytic threshold, window past every scaled node); the threshold is an
  unspecified analytic constant, so it is worth knowing the hypotheses are jointly satisfiable.  For
  every positive scale and finite node family a legal window exists, and on it the increment is
  positive semidefinite -- so the card's theorems are statements about a nonempty situation.
- 2026-08-06 — the structural half of "rank-two Cauchy--Stieltjes" made explicit: every column of the
  density lies in the span of the two Cauchy feature vectors, with no positivity or threshold
  hypothesis.  The rank bound is a consequence; the span statement is the shape.
- 2026-08-06 — "exactly rank two" upgraded from the bound to the equality.  The lower bound needs the
  two Cauchy features to be independent, which holds as soon as two nodes differ: a vanishing
  combination gives `(T/ρ)(s+t) + x_i(s-t) = 0` at every node, so two distinct nodes force `s = t`
  and then `s = t = 0`.  The general step -- a sum of two outer products of independent vectors has
  rank exactly two -- needed strict Cauchy--Schwarz for the dot product, which mathlib does not
  carry; it is proved by completing the square, and the resulting invertible Gram matrix exhibits
  both features in the column space.  The column-space inclusion is therefore an equality.
- 2026-08-06 — the exact-rank theorem certified nonvacuous.  It carries a fourth hypothesis beyond
  the Loewner ones -- the modulating sine must not vanish at the cutoff -- so it is worth knowing
  the four are jointly satisfiable.  They are, for every nonzero modulating frequency: a sine and
  its quarter-period translate cannot vanish together, so past any threshold there is a legal
  cutoff.  For `L = 0` the density is identically zero and the rank is `0`, which is why the
  frequency hypothesis is necessary rather than cosmetic.
- 2026-08-06 — the increment's Stieltjes representation proved.  The corpus had the pointwise Gram
  identity and the integrated Loewner order, but the increment's own quadratic form had never been
  displayed: it is the integral over the cutoff window of the pointwise Cauchy Gram, the scalar
  density times the sum of the two squared Cauchy features.  That identity is what makes the omitted
  tail an explicit *Cauchy--Stieltjes Gram increment* rather than an unstructured positive matrix,
  and positivity is now visible as an integral of squares rather than inferred from the order.
- 2026-08-06 — the degeneracy of the Loewner order located.  With the increment's form written as an
  integral of a nonnegative Cauchy Gram, the vanishing set of the form is exactly the set of
  coefficient vectors whose Gram vanishes almost everywhere on the cutoff window.  This is the
  sharpest statement available without the rational-separation and Cauchy-determinant input the card
  explicitly leaves out: it does not assert strict positive definiteness, it says precisely what
  would have to fail for it.
- 2026-08-06 — the kernel identified concretely.  A coefficient vector on which the increment's form
  vanishes annihilates *both* Cauchy feature vectors at almost every cutoff where the modulating
  sine is nonzero.  That is precisely the hypothesis the excluded strictness argument would have to
  contradict, so the card's boundary is now sharp on both sides: the Loewner order is proved, and
  what strictness would require is stated exactly, without being claimed.
- 2026-08-06 — the card's Statement line compiled as one object.  `groskinArchimedeanTailStatement`
  asserts, for every positive scale and finite node family: a legal cutoff window exists past the
  analytic threshold and past every scaled node; on it the increment is positive semidefinite; its
  quadratic form is the Cauchy--Stieltjes integral of the pointwise Cauchy Gram; and the generating
  density has its column space inside the span of the two Cauchy features.  The threshold entering
  it is the analytic one, so the no-computation constraint is visible in the statement itself.
