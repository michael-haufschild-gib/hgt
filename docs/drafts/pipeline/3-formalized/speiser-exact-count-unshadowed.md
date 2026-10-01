# Exact Speiser count between unshadowed heights

- **ID:** SPEISER-EXACT-COUNT
- **Stage:** 3-formalized
- **Type:** THEOREM (unconditional); a Levinson–Montgomery comparison without error term at good heights
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 68; builds on MUST-595/596 (`R:SpeiserLocalDisk`)
- **STATUS:** MUST-600

## Statement

**Definition.** A height `T` is *unshadowed* if `(Re ρ − ½)² ≤ (T − Im ρ)²` for every zero `ρ` of `ξ`.
Equivalently, `T` lies in no Speiser shadow `[γ − |β−½|, γ + |β−½|]` (the corpus `xiShadow`, in
`ξ`-coordinates).

**Theorem A.** Let `100 ≤ T₁ < T₂` be unshadowed. Then `ζ` and `ζ'` have the same number of zeros,
counted with multiplicity, in the half-strip window `0 < Re s < ½`, `T₁ < Im s < T₂`.

**Corollary B (Speiser, eventual form).** If `ζ'` has no zero in `0 < Re s < ½`, `Im s ≥ 100`, then
there is `T*` such that `ζ` has no zero in `0 < Re s < ½`, `Im s ≥ T*`. Together with MUST-595 this
gives eventual RH ⟺ eventual Speiser.

## Proof of A

Let `g = ζ'/ζ`, `c = 1/(60 log(T₂+1))`, and `R = [c, ½−δ] × [T₁, T₂]` with `δ > 0` small.

1. **Horizontal edges.** At an unshadowed height every point `σ + iT`, `0 < σ < ½`, is outside all
   Speiser disks: `(β−½)² ≤ (T−γ)² < (σ−½)² + (T−γ)²`. MUST-596 then gives `ζ ≠ 0` and
   `Re g ≤ −½ log(T/2π) + 1/10 < 0`.
2. **Left edge `σ = c`.** A Speiser disk reaches `Re s = c` only if its zero violates the zero-free
   region (`deriv_riemannZeta_ne_zero_of_re_lt` argument). So `Re g < 0` there.
3. **Right edge `σ = ½ − δ`.**
   - On the critical line `1 − s = s̄`, so reflection gives `2 Re g(½+it) = Re χ'/χ(½+it) ≤ −log(t/2π) + 3/50`.
   - Peel the finitely many on-line zeros in a thin neighbourhood `U` of the segment: `ζ = P·h`
     with `P = ∏(s−ρ)^m` and `h` zero-free on `U`. Off-line zeros are at positive distance.
   - `Re h'/h = Re g − Σ Re m/(i(t−γ)) = Re g < 0` on the line (pole terms are imaginary there).
     By continuity it holds on the whole segment, and by compactness (tube lemma) on the
     thickening `|σ − ½| ≤ δ₀`.
   - The pole terms at `½ − δ + it` have real part `−mδ/(δ² + (t−γ)²) ≤ 0`. So `Re g < 0` on the
     right edge for `0 < δ < δ₀`.
4. **Winding.**
   - `G₁ = (s−1)²ζ'` and `G₀ = (s−1)²ζ` are entire, and `G₁/G₀ = g`. Both are nonzero on `∂R` by 1–3.
   - The argument principle in integral form (`exists_entire_argument_variation_rectangle`) for
     `G₁` and `G₀` gives `2π(N₁ − N₀) = Σ_edges ∫ (arg-derivative of g)`.
   - On each edge `−g` lies in the right half-plane, so the edge integral is the increment of
     `Im log(−g)`. The four increments telescope to 0. Hence `N₁(R) = N₀(R)`.
5. **Exhaustion.**
   - No zero of `ζ` or `ζ'` has `0 < Re s ≤ c` (zero-free regions).
   - Choosing `δ` below `min(½ − Re)` over the finitely many left zeros in the window makes `R`
     capture all of them.

## Proof of B

- The shadow set has measure `vol(S ∩ [0,V]) ≤ 2 Σ m(β−½)⁺ ≤ (42/100)(V+½)` (corpus:
  `volume_xiShadow_inter_Icc_le_offLineMoment`, `eventually_offLineMoment_le`).
- So every interval `[γ₀/2, γ₀)` and `(γ₀, 2γ₀]` with `γ₀` large contains unshadowed heights.
- A left zero of `ζ` at `γ₀` then forces, by A, a left zero of `ζ'` in the window.

## Lean status [L] (all clean, standard axioms, wired)

- `R:RectangleLeftHalfPlaneWinding`, the generic winding step.
  - `sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg`: entire `F₁, F₀` with `logDeriv F₁ = logDeriv g + logDeriv F₀` and `Re g < 0` on `∂R` have equal zero counts in `R`.
  - Edge primitives: `integral_re_logDeriv_vertical_eq_of_re_neg`, `integral_im_logDeriv_horizontal_eq_of_re_neg`.
- `R:SpeiserExactCount`.
  - Theorem A: `exists_speiser_count_eq`, stated with `SpeiserUnshadowed`, `speiserWindow` and `101 ≤ T₁`.
  - Right edge: `exists_right_edge_re_logDeriv_neg`.
  - Critical-line identity: `two_mul_re_logDeriv_riemannZeta_criticalLine`.
  - Entire pair: `zetaDerivResidueUnit = (s−1)²ζ'` and `zetaResidueUnitSq = (s−1)²ζ`, with their order lemmas.
  - Boundary step: `ratioLeftBoundary_zeta`.
- `R:SpeiserEventualEquivalence`.
  - `speiserUnshadowed_of_not_mem_xiShadow` and `exists_speiserUnshadowed_mem_Icc`.
  - Corollary B: `exists_riemannZeta_ne_zero_left_of_deriv_ne_zero`.
  - Equivalence: `eventually_re_eq_half_iff_eventually_deriv_ne_zero`.
- `R:SpeiserLocalDisk` now also carries `speiserDisk_strict_of_re_lt` (the left-edge input).

## Remarks

- The count is exact, with no `O(log T)` error. That needs both edges unshadowed. Levinson–Montgomery's `O(log T)` version for arbitrary heights would need Backlund-type horizontal bounds; it is not done.
- The eventual equivalence is ineffective in `T₀`. It comes from `eventually_offLineMoment_le`. Full Speiser (all heights) would need the low heights, i.e. zero verification.

## Addendum (cycle 69): clean horizontal lines [L]

`R:SpeiserCleanHeights`.
- `cleanLine_of_speiserUnshadowed`: at every unshadowed height `T ≥ 101`, the whole line
  `Im s = T` is clean:
  - `ζ, ζ' ≠ 0` and `Re ζ'/ζ < 0` on `0 < Re s < ½`;
  - `|ζ|` is strictly decreasing there;
  - `ξ ≠ 0` and `Re ξ'/ξ ≥ 0` on `Re s > ½`.
- `eventually_volume_speiserUnshadowed_ge`: unshadowed heights in `[0,V]` have measure
  `≥ (29/50)V − 21/100`.

Together with the corpus's Laguerre/vertical-monotonicity shadow law, at least 58% of heights carry
every horizontal RH-sign simultaneously, along the entire line. The proportion is governed only by
the off-line first moment. Its improvement (e.g. to 1 − 0.143 with the conditional 0.0714 moment)
waits on the mollified gates.

## Addendum (cycle 70): one exceptional set for all local RH signs [L]

- `speiserUnshadowed_iff_not_mem_xiShadow`: unshadowed ⟺ outside the corpus de Bruijn shadow set.
- `allRHSigns_of_speiserUnshadowed`: at every unshadowed `T ≥ 101` the following hold together:
  - the first Laguerre inequality and vertical monotonicity of `|Ξ|` at `T`;
  - `c_n(T) ≥ 0` for every slice coefficient;
  - Speiser and horizontal ζ-monotonicity on `0 < Re s < ½`;
  - the Hadamard sign on `Re s > ½`.
- All six local RH-equivalent signs therefore share the exceptional set
  `⋃_ρ [γ − |β−½|, γ + |β−½|]`, whose measure is at most twice the off-line first moment.

## Addendum (loop cycle 103): Speiser's deficit is at most `(1 − HD 1)/2 ≈ 16.4%` [L] — MUST-623

Module `R:SpeiserDeficitTwoThirds`.

- `eventually_speiser_deficit_le`: for every `ε > 0` and all large `T₂`, between unshadowed heights `101 ≤ T₁ < T₂` the zeros of `ζ'` with multiplicity in `0 < Re s < ½`, `T₁ < Im s < T₂` number at most `((1 − HD 1)/2 + ε)·N(T₂)`, where `HD 1 = 0.6725…`.
- `eventually_xiDeriv_right_le` and `eventually_levinsonG_right_le`: the same bound for the right zeros of `ξ'`, and for the right zeros of `ζ + λζ'` in Levinson's exact range.
- Tools:
  - `two_mul_xiLeftZeroCount_eq`: the left multiplicity is exactly half of the off-line multiplicity, via `z ↦ 1 − z̄` with `xi_orderAt_one_sub` and `xi_orderAt_conj`.
  - `eventually_xiLeftZeroCount_le`, `eventually_xiRightZeroCount_le`.

Proof: exact Speiser count (MUST-600) + Zeta23 Montgomery–Taylor (`lamzouri_montgomeryTaylor_simpleCritical_epsilon`) + `N_off ≤ N − N₀ˢ`.
