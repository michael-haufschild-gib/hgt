# Regular-deviation rigidity, analytic-continuation form: a Weil-positive completion never differs from Λ by a deviation that continues across the critical line

- **ID:** MC-WEIL-REGULAR-DEVIATION
- **Stage:** 3-formalized (MC loop cycle 165)
- **Type:** THEOREM (Lean, unconditional)
- **Statement.**
  - **Setting.** Let `w : ℕ → ℝ` with `w(0) = w(1) = 0` and `Σ|w(n)|n^{−5/4} < ∞`. Suppose there is `E`, holomorphic on a neighbourhood of the strip `½ ≤ Re s ≤ 5/4`, with:
    - `E(s) = Σ w(n) n^{−s}` on `Re s = 5/4`;
    - `E(½ − it) = conj E(½ + it)`;
    - `‖E(s)‖ ≤ C(1+|Im s|)` on the strip.
  - **Conclusion.** If `Λ + w` is Weil-positive on pole-free tests (the corpus `WeilPositive`), then `w = 0`.
  - **Full cone.** In particular a full-cone Weil-positive `Λ + w` of this kind is `Λ`, and RH holds.
- **Relation to the corpus (corrected 2026-09-30).** The core of this theorem was already in the corpus, via the regular-perturbation rigidity of the MUST-507 lineage:
  - `RHTower.vonMangoldt_add_eq_zero_of_symbol`: any deviation whose atoms pair with tests through a continuous symbol of linear growth vanishes, under `WeilPositive`. It has the same three-step mechanism: concentration gives `P ≤ 0`, small-support probes give `P ≡ 0`, resonators give `w = 0`.
  - `RHTower.vonMangoldt_add_oscillating_eq_zero`: the case of partial sums `O(n^θ)`, `θ < ½`. This already contains every periodic mean-zero deviation, including `1⋆p` with `P(1) = 0`.
  - **What cycle 165 adds.** It adds the critical-line representation lemma (`tsum_deviation_mul_pair_eq`). The lemma turns analytic-continuation data (holomorphy across the strip plus linear growth) into the corpus symbol. The regular class is therefore defined by continuation rather than by partial-sum bounds, which gives a formally larger class. It is a bridge, not a new exclusion.

## Why
- **The cycle-163 claim was wrong.** Cycle 163 listed "Dirichlet-polynomial multiples `ζP`" as unreached. That is incorrect: `vonMangoldt_add_oscillating_eq_zero` covers them, because the partial sums of `1⋆p` are bounded. This card records the correction.
- **Value of the continuation form.** Hypotheses on analytic continuation (`E` holomorphic across `Re s = ½` with growth) are the natural output of spectral or explicit-formula constructions. Partial-sum bounds need Perron/Tauberian work to extract. The representation lemma is reusable for any strip test with `(1+|x|)^{−3}` decay.

## Paper proof
- **Notation.**
  - `a(n) = w(n)/√n` is the normalized deviation.
  - `K = Φ⋆Φ` is Riemann's autocorrelation. `𝓕K = Ξ₂ := riemannXi²` with `riemannXi ξ = ξ(½+2πiξ)`, which is real, even and entire of decay type in horizontal strips.
  - `ψ(y) = Σ a(n)(K(y+log n)+K(y−log n))`. By the corpus (`positiveDefiniteOnReal_neg_deviationPotential`, `exists_spectralMeasure`), `−ψ` is positive definite and equals `charFun σ` for a finite positive measure `σ`. This uses Weil positivity only.
1. **Representation lemma R.** Let `G` be holomorphic on `|Im z| ≤ η = 1/π` with `|G(ξ+iη')| ≤ C(1+|ξ|)^{−N−2}`, and `g(u) = ∫G(ξ)e^{2πiξu}dξ`. Then for all `y`:
   `Σ_n a(n)(g(y−log n)+g(y+log n)) = ∫ G(ξ) e^{2πiξy} (E(½+2πiξ)+E(½−2πiξ)) dξ`.
   - Proof, first sum: shift `ξ ↦ ξ−iη` in each term, which gives the factor `n^{−2}`. Sum under the integral (absolute convergence, since `Σ|a(n)|n^{−2} < ∞`). The inner sum is `E(5/2+2πiξ)`. Shift back to `Im = 0`.
   - The second sum is symmetric, with `ξ ↦ ξ+iη`.
2. **Density of σ.** Take `G = Ξ₂` in R. Then `ψ(y) = ∫Ξ₂(ξ)e^{2πiξy}·2Re E(½+2πiξ)dξ`, so `charFun σ = charFun(f dx)` with `f(x) = −(1/π)Ξ₂(x/2π) Re E(½+ix)`.
   - Split `f = f⁺ − f⁻`. Then `σ + f⁻dx = f⁺dx` as finite measures (`Measure.ext_of_charFun`).
   - `f⁺` and `f⁻` have disjoint supports, so `f⁻ = 0` a.e. As `f` is continuous, `f ≥ 0`.
3. **Sign on the line.** `Ξ₂ > 0` off the discrete set of real zeros of `Ξ`. Hence `Re E(½+ix) ≤ 0` on a dense set, and by continuity for all `x`.
4. **Small-support annihilation.** Take `k = φ⋆φ` with `φ` real, even, smooth, supported in `(−¼log2, ¼log2)`, and `G = 𝓕k = (𝓕φ)² ≥ 0` in R, at `y = 0`.
   - The left side vanishes, because `k(±log n) = 0` for `n ≥ 2`.
   - So `∫(𝓕φ)²·Re E(½+2πiξ)dξ = 0`. The integrand is `≤ 0` and continuous, so it vanishes. `𝓕φ` is entire and nonzero, so `Re E(½+2πiξ) = 0` for all `ξ`.
5. **Vanishing.** With `Re E ≡ 0` on the line, R gives `Σ a(n)(k(y−log n)+k(y+log n)) = 0` for every compactly supported smooth `k` and every `y`.
   - Take `k` a narrow bump at `0` and `y = log m`. This gives `a(m)k(0) = 0`, so `w(m) = 0`.
6. **RH.** `lam = Λ` is Weil-positive, so RH holds (`riemannHypothesis_iff_weilPositiveFull_vonMangoldt`).
- **ζP instance.**
  - `E(s) = ζ_u(s)·dslope P 1 s − p(1)` is entire, since `P(1) = 0`.
  - `E = Σ(1⋆p)(n)n^{−s} − p(1)` on `Re s > 1` (`LSeries_convolution`, `LSeries_one_eq_riemannZeta`).
  - Real coefficients give `E(s̄) = conj E(s)`.
  - Polynomial growth comes from `exists_bound_norm_riemannZeta_strip` and continuity near `s = 1`.
  - Möbius inversion: if `1⋆p` vanishes on `n ≥ 2` and `p` is finitely supported, then `p = 0`.

## Novelty audit
- **Verdict: REDISCOVERED** (core statement and mechanism: MUST-507 lineage, `WeilPositivityRegularPerturbationRigidity`) **/ BRIDGE** (the continuation form via the line-representation lemma).
- **The audit failure.** The Phase-4 search checked HF's crystalline and ζ-mass cards (L150–L155) but not the regular-perturbation modules. The frontier-map row "Proved [L]: `Λ+w∈W` with `Σ w = κ₁(n−1)+κ₂(√n−1)+E(n)` … partial-sum `O(n^θ)` for `θ<½`" already covered the class.
- **Literature.** There is no literature notion of the Weil cone of completions.

## Lean
- **`RHTower/WeilDeviationLineRepresentation.lean`** (new tool): `RHTower.WeilRegular.tsum_deviation_mul_pair_eq`, the critical-line representation of deviation pairings by contour shift.
- **`RHTower/WeilRegularDeviationRigidity.lean`** (297 lines).
  - `structure RegularDeviation`.
  - `pairTransform`, with its decay and Fourier inversion for `weilTest f f`.
  - `regular_symbol_identity`, the corpus symbol hypothesis.
  - `eq_zero_of_weilPositive_add`, which uses pole-free positivity and applies `vonMangoldt_add_eq_zero_of_symbol`.
  - `eq_zero_of_weilPositiveFull_add` and `riemannHypothesis_of_weilPositiveFull_add`.
- **History.**
  - An independent 730-line proof went through the near-null Bochner measure `σ` and `Measure.ext_of_charFun`. It showed `Ξ²·Re E ≤ 0`, then used small-support annihilation and narrow-bump vanishing. It was built and verified, then replaced by the thin instance above, since it duplicated the corpus mechanism.
  - A separate `ζP` module was deleted as redundant with `vonMangoldt_add_oscillating_eq_zero`.
- **Audit.** Wired into `RHTower.lean`. `#print axioms`: `propext, Classical.choice, Quot.sound`. The ilean sweep found no collisions, and lint is clean.

## Log
- 2026-09-30 — card created (MC cycle 165). Paper proof above. Lean: starting.

- 2026-09-30 — formalized (MC cycle 165). Moved from 1-in-progress to 3-formalized.

- 2026-09-30 — corrected (MC cycle 165a). The core was already in the corpus (MUST-507 lineage). The module was refactored onto `vonMangoldt_add_eq_zero_of_symbol`, which strengthens it to pole-free positivity. The `ζP` module was deleted as redundant.
