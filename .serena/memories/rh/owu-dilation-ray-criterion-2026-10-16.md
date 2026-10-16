# OWU: the dilation-ray criterion (2026-10-16, Lean) — MUST-1554

Card: docs/drafts/pipeline/3-formalized/owu-dilation-ray-criterion-2026-10-16.md.
Lean: formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean (namespace RHTower.OddResolvent),
wired into RHTower.lean, axioms [propext, Classical.choice, Quot.sound].

Theorem: φ = reference bump (ContDiffBump (0:ℝ) with rIn 1, rOut 2; `refProfile`, `dilate T x = φ(x/T)`).
If WeilPositiveOdd lam and ∀ T ≥ 1, 0 ≤ Re W_lam(weilTest (dilate T) (dilate T)), then lam = Λ on n ≥ 2 and RH
(`eq_vonMangoldt_and_riemannHypothesis_of_dilationRay_nonneg`); RH ⟺ ∃ such lam
(`riemannHypothesis_iff_exists_weilPositiveOdd_dilationRay`).

Mechanism (odd Nevanlinna data (ν, c), D = ∫φ ∈ [2,4], E(Tr) = ∫φ e^{−Tru} ≥ 2 + T²r²/6, N₂ real-line decay):
- weights of dilates: critical ≤ T²(D² + 2N₂²) (`spectralWeight_dilate_le_uniform`), ≤ T²γD² − T²(D² − |φ̂(T√γ)|²)/γ,
  ≤ (1+γ²)N₂²/(T²γ³) − T²D²/γ; near centre (T√γ ≤ ½) ≤ T²γD² − T⁴D/6 (uses φ̂(0) − φ̂(v) ≥ v²/6 for |v| ≤ ½);
  centre Θ(−1) ≤ −T⁴D/6; cut ≤ 0, and ≤ 4T²(12 − T⁴r₀⁴/36) at distance ≥ r₀ once T⁴r₀⁴ ≥ 432.
- `mul_measureReal_le_of_weight_bounds`: Θ ≤ M₀ off A, ≤ −K on A, W ≥ 0 ⟹ Kν(A) ≤ M₀ν(S¹) − c|f̂(0)|².
  ⟹ ν(cutSet r₀) = 0 (then countable union), ν({−1}) = 0.
- `integral_farSet_inv_le_of_dilationRay`: ∫_{γ≥δ} dν/γ ≤ δν(S¹) − c (bound function
  1_{γ≥δ}(K_δ/T² − T²D²/γ) + 1_{γ<δ}T²δD², K_δ = N₂²(1/δ³+1/δ); let T → ∞).
- `le_re_integral_nevKernel`: Re ∫(γz−1)/(z+γ)dν ≥ c for real z > 0 (kernel ≥ −1/γ on far set, ≥ −1/z on near set,
  near sets shrink to the null set cut ∪ {−1} via tendsto_measure_iInter_atTop); `re_cutFreeExtension_nonneg`.
- then `eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension` (square-root transfer).

Reading: obstacles (1) cut removal and (2) central nonnegativity are the single family W_λ(φ_T) ≥ 0; the even
half of the primitive-hyperplane certificate (MUST-1519) collapses to a ray. Arithmetic content: scale-T excess
of Σλ(n)n^{−½} over the archimedean prediction (half-pole excess c log X, real-power excess x^{½+r}).

Obstacle 3 (source, PrimeBlindPositiveOddAt 1): ⟺ ∃ mean-one real Dirichlet series D with a(Ψ₀ − D)(½+a)
Nevanlinna off (−∞,¼], i.e. Re D(½+0+iτ) ≤ w(τ) (archimedean density) on the line with equality a.e. for Λ under RH.
Absolutely convergent series on the line cannot carry the pole; ζ−1, 2ΣΛ(n)n^{−2s}, Euler perturbations fail the
line condition. Unconditional provability = RH ∨ odd fakes. Corpus window programme (weilArchRe_nonneg_of_support_*:
nonneg tests to 4/9, signed to ~1/36 via half_window_signed_short_support_le_weilArchRe) covers tiny supports only.

Lean notes: `Measure.integral_comp_div` for dilation; `Integrable.ofReal`; `integral_complex_ofReal`; state
`integral_add` with explicit Complex coercions (RCLike vs Complex.ofReal mismatch blocks rw); `ContDiffBump.neg/le_one/
one_of_mem_closedBall/zero_of_le_dist`; `Real.cos_bound`; `tendsto_measure_iInter_atTop` + `ENNReal.tendsto_toReal`;
avoid `if` with Classical in statements (instance mismatch at call sites) — use implication pairs; `simp only
[RCLike.re_to_complex]` after `Integrable.re`; `positivity` cannot see local `set` variables' positivity.
