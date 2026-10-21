import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTenOneBlocks
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropEightOne
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

set_option autoImplicit false

/-!
# Guth–Maynard Proposition 10.1: the refined `S₃` bound

**Proposition 10.1** (arXiv 2405.20552): for a `T^ε`-separated `W` in an interval of length `T`,
`S₃ ⪅ T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`.

Its proof starts from Proposition 7.2, `S₃ ⪅ (N²/M) Σ_m Ĩ_m + O(T^{-100})` with
`Ĩ_m = ∫_{1/2}^{2} |R(v)| R̃(α_m v) R̃(β_m v) dv`, `α_m v = (m₁v + m₃)/(m₂v)`,
`β_m v = (m₁v + m₃)/m₂`, the sum over the box `M₁ ≤ |m₁| < 2M₁`, `M ≤ |m₂| < 2M`, `M ≤ |m₃| < 9M`.

* Cauchy–Schwarz in `v` and then in `m` (`sum_smoothedCubicTerm_sq_le`):
  `(Σ_m Ĩ_m)² ≤ (∫_{1/2}^{2} |R|²) ∫_{1/2}^{2} P Q`, `P = Σ_m R̃(α_m v)²`, `Q = Σ_m R̃(β_m v)²`.
* For `v ∈ [1/2, 2]` both arguments satisfy `|α_m v|, |β_m v| ≤ 20`, so any `f` with
  `R̃² ≤ f` on `[−20, 20]` (the paper's `f = ψ₁ |R̃|²`) majorises them; `PQ ≤ (P̃² + Q̃²)/2`
  and the block comparisons of `GuthMaynardPropTenOneBlocks` give `∫ PQ ≤ 130 J_{16M}(f)`.
* Proposition 9.1 (`affineSup_le_of_fourier_decay`) bounds `J_{16M}(f) ⪅ M⁶ (∫ f)² + M⁴ ∫ f²`.

The theorems here are **assembly lemmas**: the Proposition 7.2 inequality enters as a hypothesis on
an arbitrary real `S₃` (`propTenOne_of_expansion`), and the function `f` is arbitrary data with the
Fourier decay of Lemma 8.4 (`ξ² |f̂(ξ)| ≤ A T³ sup f`) and arbitrary bounds `∫ f ≤ L₁`,
`∫ f² ≤ L₄` (Lemmas 8.2, 8.3 give `L₁ ≪ |W|`, `L₄ ⪅ E(W)` for the paper's `f`). Lemma 8.2 for
`R` (`∫_{1/2}^{2} |R|² ≪ |W|`) is used directly. The box hypothesis `InPropSevenTwoBox M₁ M` is
exactly membership in `dyadicFrequencyBlock M₁ M` (`mem_dyadicFrequencyBlock`).
-/

open MeasureTheory Finset Set
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The window of the arguments -/

/-- `|(m₁v + m₃)/m₂| ≤ 13` on `[1/2, 2]` for `m` in the box. -/
theorem abs_affine_arg_le {M₁ M : ℕ} (hM : 1 ≤ M) (hM₁M : M₁ ≤ M) {m : ℤ × ℤ × ℤ}
    (hm : InPropSevenTwoBox M₁ M m) {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 2) :
    |((m.1 : ℝ) * v + m.2.2) / m.2.1| ≤ 20 := by
  obtain ⟨-, h2, h3, -, -, h6⟩ := hm
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h2' : |(m.1 : ℝ)| ≤ 2 * M := by
    have hMM : (M₁ : ℤ) ≤ M := by exact_mod_cast hM₁M
    have : |m.1| ≤ 2 * (M : ℤ) := by linarith
    exact_mod_cast this
  have h3' : (M : ℝ) ≤ |(m.2.1 : ℝ)| := by exact_mod_cast h3
  have h6' : |(m.2.2 : ℝ)| ≤ 9 * M := by
    have : |m.2.2| ≤ 9 * (M : ℤ) := h6.le
    exact_mod_cast this
  have hv0 : 0 ≤ v := by linarith [hv.1]
  rw [abs_div, div_le_iff₀ (by linarith)]
  calc |(m.1 : ℝ) * v + m.2.2| ≤ |(m.1 : ℝ)| * v + |(m.2.2 : ℝ)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hv0]
    _ ≤ 2 * M * 2 + 9 * M := by
        have := hv.2
        nlinarith [abs_nonneg (m.1 : ℝ)]
    _ ≤ 20 * |(m.2.1 : ℝ)| := by nlinarith

/-- `|(m₁v + m₃)/(m₂v)| ≤ 20` on `[1/2, 2]` for `m` in the box. -/
theorem abs_mobius_arg_le {M₁ M : ℕ} (hM : 1 ≤ M) (hM₁M : M₁ ≤ M) {m : ℤ × ℤ × ℤ}
    (hm : InPropSevenTwoBox M₁ M m) {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 2) :
    |((m.1 : ℝ) * v + m.2.2) / (m.2.1 * v)| ≤ 20 := by
  obtain ⟨-, h2, h3, -, -, h6⟩ := hm
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h2' : |(m.1 : ℝ)| ≤ 2 * M := by
    have hMM : (M₁ : ℤ) ≤ M := by exact_mod_cast hM₁M
    have : |m.1| ≤ 2 * (M : ℤ) := by linarith
    exact_mod_cast this
  have h3' : (M : ℝ) ≤ |(m.2.1 : ℝ)| := by exact_mod_cast h3
  have h6' : |(m.2.2 : ℝ)| ≤ 9 * M := by
    have : |m.2.2| ≤ 9 * (M : ℤ) := h6.le
    exact_mod_cast this
  have hv0 : 0 < v := by linarith [hv.1]
  rw [abs_div, abs_mul, abs_of_pos hv0, div_le_iff₀ (mul_pos (by linarith) hv0)]
  calc |(m.1 : ℝ) * v + m.2.2| ≤ |(m.1 : ℝ)| * v + |(m.2.2 : ℝ)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hv0]
    _ ≤ 2 * M * v + 9 * M := by nlinarith [abs_nonneg (m.1 : ℝ)]
    _ ≤ 20 * (|(m.2.1 : ℝ)| * v) := by nlinarith [hv.1]

/-! ### Cauchy–Schwarz over the box -/

/-- **The `S_{3,0}` bound.** For a smoothing pair, `NM > 0`, `1 ≤ M₁ ≤ M`, a finite set `𝓜` in the
box, and any continuous compactly supported `f ≥ 0` with `R̃² ≤ f` on `[−20, 20]`:
`(Σ_m Ĩ_m)² ≤ (∫_{1/2}^{2} |R|²) · 130 J_{16M}(f)`. -/
theorem sum_smoothedCubicTerm_sq_le {ψ₁ ψ₂ : ℝ → ℝ} (hψ : IsSmoothingPair ψ₁ ψ₂) {N : ℝ}
    {M₁ M : ℕ} (hNM : 0 < N * M) (hM₁ : 1 ≤ M₁) (hM₁M : M₁ ≤ M) (W : Finset ℝ)
    (𝓜 : Finset (ℤ × ℤ × ℤ)) (h𝓜 : ∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x)
    (hmaj : ∀ u, |u| ≤ 20 → smoothedLagSum ψ₁ ψ₂ N M W u ^ 2 ≤ f u) :
    (∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2) ^ 2 ≤
      (∫ v in Icc (1 / 2 : ℝ) 2, ‖lagSum W v‖ ^ 2) * (130 * affineSup f (16 * M)) := by
  have hM : 1 ≤ M := hM₁.trans hM₁M
  set S := Icc (1 / 2 : ℝ) 2 with hS
  set Rt := smoothedLagSum ψ₁ ψ₂ N M W with hRt
  set G : ℝ → ℝ := fun v => ∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / (m.2.1 * v)) *
    Rt ((m.1 * v + m.2.2) / m.2.1) with hG
  set P : ℝ → ℝ := fun v => ∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / (m.2.1 * v)) with hP
  set Q : ℝ → ℝ := fun v => ∑ m ∈ 𝓜, f ((m.1 * v + m.2.2) / m.2.1) with hQ
  have hRtm := measurable_smoothedLagSum hψ N M W
  have hRt0 : ∀ u, 0 ≤ Rt u := smoothedLagSum_nonneg ψ₁ ψ₂ N M W
  have hGm : Measurable G := Finset.measurable_sum _ fun m _ =>
    (hRtm.comp (by fun_prop)).mul (hRtm.comp (by fun_prop))
  -- `Σ_m Ĩ_m = ∫_S |R| G`
  have hsum : ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 =
      ∫ v in S, ‖lagSum W v‖ * G v := by
    simp only [smoothedCubicTerm, hG, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      refine setIntegral_congr_fun measurableSet_Icc fun v _ => ?_
      ring
    · intro m _
      exact (integrableOn_norm_lagSum_mul_smoothedLagSum hψ hNM W
        (a := fun v => ((m.1 : ℝ) * v + m.2.2) / (m.2.1 * v))
        (b := fun v => ((m.1 : ℝ) * v + m.2.2) / m.2.1) (by fun_prop) (by fun_prop)).congr_fun
        (fun v _ => by ring) measurableSet_Icc
  -- `G² ≤ (P² + Q²)/2` on `S`
  have hGPQ : ∀ v ∈ S, G v ^ 2 ≤ (P v ^ 2 + Q v ^ 2) / 2 := fun v hv => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq 𝓜 (fun m => Rt ((m.1 * v + m.2.2) / (m.2.1 * v)))
      (fun m => Rt ((m.1 * v + m.2.2) / m.2.1))
    have hPle : ∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / (m.2.1 * v)) ^ 2 ≤ P v :=
      Finset.sum_le_sum fun m hm => hmaj _ (abs_mobius_arg_le hM hM₁M (h𝓜 m hm) hv)
    have hQle : ∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / m.2.1) ^ 2 ≤ Q v :=
      Finset.sum_le_sum fun m hm => hmaj _ (abs_affine_arg_le hM hM₁M (h𝓜 m hm) hv)
    have hP0 : 0 ≤ ∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / (m.2.1 * v)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hQ0 : 0 ≤ ∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / m.2.1) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc G v ^ 2 ≤ (∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / (m.2.1 * v)) ^ 2) *
          ∑ m ∈ 𝓜, Rt ((m.1 * v + m.2.2) / m.2.1) ^ 2 := hcs
      _ ≤ P v * Q v := mul_le_mul hPle hQle hQ0 (hP0.trans hPle)
      _ ≤ (P v ^ 2 + Q v ^ 2) / 2 := by nlinarith [sq_nonneg (P v - Q v)]
  -- integrability on `S`
  have hPc : ContinuousOn P S := by
    refine continuousOn_finsetSum _ fun m hm => hf.comp_continuousOn ?_
    have h₂ := cast_ne_zero_of_box hM (h𝓜 m hm).2.2.1
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv =>
      mul_ne_zero h₂ (by linarith [hv.1] : v ≠ 0)
  have hQc : Continuous Q := continuous_finsetSum _ fun m _ => hf.comp (by fun_prop)
  have hPQi : IntegrableOn (fun v => (P v ^ 2 + Q v ^ 2) / 2) S :=
    ((hPc.pow 2).add ((hQc.pow 2).continuousOn)).div_const 2 |>.integrableOn_compact isCompact_Icc
  have hG2i : IntegrableOn (fun v => G v ^ 2) S :=
    Integrable.mono' hPQi (hGm.pow_const 2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hGPQ v hv))
  have hr2i : IntegrableOn (fun v => ‖lagSum W v‖ ^ 2) S := integrableOn_Icc_norm_lagSum_sq W _ _
  -- Cauchy–Schwarz in `v`
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := volume.restrict S)
    (f := fun v => ‖lagSum W v‖) (g := G)
    (measurable_lagSum W).norm.aestronglyMeasurable hGm.aestronglyMeasurable hr2i hG2i
  -- the two square functions
  obtain ⟨hJ1, hJ2⟩ := affineEnergy_box_le_affineSup hf hfc hM₁ hM₁M
  have hQint := setIntegral_sq_sum_box_le hf hfc hf0 𝓜 h𝓜
  have hPint := setIntegral_sq_sum_box_mobius_le hf hfc hf0 hM 𝓜 h𝓜
  have hJ0 : 0 ≤ affineSup f (16 * M) := affineSup_nonneg f _
  have hsumJ : ∑ k ∈ range 4, affineEnergy f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
      ((2 * M₁ : ℕ) : ℝ) ≤ 4 * affineSup f (16 * M) := by
    calc ∑ k ∈ range 4, affineEnergy f (((2 ^ k * M : ℕ) : ℝ) - 1 / 2) ((M : ℝ) - 1 / 2)
          ((2 * M₁ : ℕ) : ℝ) ≤ ∑ _k ∈ range 4, affineSup f (16 * M) := Finset.sum_le_sum hJ2
      _ = 4 * affineSup f (16 * M) := by rw [Finset.sum_const, Finset.card_range]; norm_num
  have hG2 : ∫ v in S, G v ^ 2 ≤ 130 * affineSup f (16 * M) := by
    calc ∫ v in S, G v ^ 2 ≤ ∫ v in S, (P v ^ 2 + Q v ^ 2) / 2 :=
          setIntegral_mono_on hG2i hPQi measurableSet_Icc hGPQ
      _ = ((∫ v in S, P v ^ 2) + ∫ v in S, Q v ^ 2) / 2 := by
          rw [integral_div, integral_add (f := fun v => P v ^ 2) (g := fun v => Q v ^ 2)
            ((hPc.pow 2).integrableOn_compact isCompact_Icc)
            ((hQc.pow 2).continuousOn.integrableOn_compact isCompact_Icc)]
      _ ≤ (64 * (4 * affineSup f (16 * M)) + 4 * affineSup f (16 * M)) / 2 := by
          have h1 : ∫ v in S, P v ^ 2 ≤ 64 * (4 * affineSup f (16 * M)) :=
            hPint.trans (mul_le_mul_of_nonneg_left hsumJ (by norm_num))
          have h2 : ∫ v in S, Q v ^ 2 ≤ 4 * affineSup f (16 * M) :=
            hQint.trans (mul_le_mul_of_nonneg_left hJ1 (by norm_num))
          linarith
      _ = 130 * affineSup f (16 * M) := by ring
  rw [hsum]
  refine hCS.trans ?_
  exact mul_le_mul_of_nonneg_left hG2 (setIntegral_nonneg measurableSet_Icc fun v _ => by positivity)

/-! ### Proposition 10.1 -/

/-- **`Σ Ĩ_m` through Proposition 9.1.** For `δ > 0`, `A ≥ 0` there is `K` such that, for a
smoothing pair, `1`-separated `W`, `1 ≤ M₁ ≤ M`, a finite `𝓜` in the box, and any continuous
compactly supported `f ≥ 0` with `R̃² ≤ f` on `[−20, 20]`, `ξ² |f̂(ξ)| ≤ A T³ sup f`,
`∫ f ≤ L₁`, `∫ f² ≤ L₄`:
`Σ_m Ĩ_m ≤ K T^δ |W|^{1/2} (M³ L₁ + M² L₄^{1/2})`. -/
theorem sum_smoothedCubicTerm_le_of_decay {δ : ℝ} (hδ : 0 < δ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T N : ℝ) (M₁ M : ℕ) (ψ₁ ψ₂ f : ℝ → ℝ) (W : Finset ℝ)
      (𝓜 : Finset (ℤ × ℤ × ℤ)) (L₁ L₄ : ℝ), 1 ≤ T → 0 < N → 1 ≤ M₁ → M₁ ≤ M →
      IsSmoothingPair ψ₁ ψ₂ → IsSeparated 1 W → (∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) →
      Continuous f → HasCompactSupport f → (∀ u, 0 ≤ f u) →
      (∀ u, |u| ≤ 20 → smoothedLagSum ψ₁ ψ₂ N M W u ^ 2 ≤ f u) →
      (∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * T ^ 3 * ⨆ x, f x) →
      ∫ u, f u ≤ L₁ → ∫ u, f u ^ 2 ≤ L₄ →
      ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 ≤
        K * T ^ δ * √(W.card : ℝ) * ((M : ℝ) ^ 3 * L₁ + (M : ℝ) ^ 2 * √L₄) := by
  obtain ⟨c, hc, h91⟩ := affineSup_le_of_fourier_decay hδ hA
  have hmc := momentConstant_nonneg (A := 2) (by norm_num)
  refine ⟨√(momentConstant 2 * (130 * 16 ^ 6 * c)), Real.sqrt_nonneg _,
    fun T N M₁ M ψ₁ ψ₂ f W 𝓜 L₁ L₄ hT hN hM₁ hM₁M hψ hW h𝓜 hf hfc hf0 hmaj hdec hL₁ hL₄ => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast hM₁.trans hM₁M
  have hNM : 0 < N * M := by positivity
  have hTδ : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ.le
  have hF0 : 0 ≤ ∫ u, f u := integral_nonneg hf0
  have hF20 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hL₁0 : 0 ≤ L₁ := hF0.trans hL₁
  have hL₄0 : 0 ≤ L₄ := hF20.trans hL₄
  -- Lemma 8.2 for `R` on `[1/2, 2]`
  have hR2 : ∫ v in Icc (1 / 2 : ℝ) 2, ‖lagSum W v‖ ^ 2 ≤ momentConstant 2 * W.card := by
    rw [one_div]
    exact setIntegral_Icc_inv_normSq_lagSum_le (by norm_num) hW
  -- Proposition 9.1 at scale `16M`
  have hJ := h91 f T (16 * M) hT (by positivity) hf hfc hf0 hdec
  have hJ' : affineSup f (16 * M) ≤ 16 ^ 6 * c * T ^ δ * ((M : ℝ) ^ 6 * L₁ ^ 2 + (M : ℝ) ^ 4 * L₄) := by
    refine hJ.trans ?_
    have h1 : (∫ x, f x) ^ 2 ≤ L₁ ^ 2 := pow_le_pow_left₀ hF0 hL₁ 2
    have hM4 : 0 ≤ (M : ℝ) ^ 4 := by positivity
    have hM6 : 0 ≤ (M : ℝ) ^ 6 := by positivity
    have hcT : 0 ≤ c * T ^ δ := by positivity
    calc c * T ^ δ * ((16 * M) ^ 6 * (∫ x, f x) ^ 2 + (16 * M) ^ 4 * ∫ x, f x ^ 2)
        ≤ c * T ^ δ * (16 ^ 6 * M ^ 6 * L₁ ^ 2 + 16 ^ 6 * M ^ 4 * L₄) := by
          gcongr
          · nlinarith
          · nlinarith
      _ = 16 ^ 6 * c * T ^ δ * ((M : ℝ) ^ 6 * L₁ ^ 2 + (M : ℝ) ^ 4 * L₄) := by ring
  have hsq := sum_smoothedCubicTerm_sq_le hψ hNM hM₁ hM₁M W 𝓜 h𝓜 hf hfc hf0 hmaj
  have hsum0 : 0 ≤ ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 :=
    Finset.sum_nonneg fun _ _ => smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _
  have hJ0 : 0 ≤ affineSup f (16 * M) := affineSup_nonneg f _
  have hbig : (∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2) ^ 2 ≤
      momentConstant 2 * (130 * 16 ^ 6 * c) * (W.card : ℝ) * T ^ δ *
        ((M : ℝ) ^ 6 * L₁ ^ 2 + (M : ℝ) ^ 4 * L₄) := by
    refine hsq.trans ?_
    calc (∫ v in Icc (1 / 2 : ℝ) 2, ‖lagSum W v‖ ^ 2) * (130 * affineSup f (16 * M))
        ≤ (momentConstant 2 * W.card) *
            (130 * (16 ^ 6 * c * T ^ δ * ((M : ℝ) ^ 6 * L₁ ^ 2 + (M : ℝ) ^ 4 * L₄))) := by
          gcongr
      _ = _ := by ring
  -- take square roots
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (M : ℝ) ^ 6 * L₁ ^ 2 + (M : ℝ) ^ 4 * L₄ := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  rw [← hZ] at hbig
  have hsqZ : √Z ≤ (M : ℝ) ^ 3 * L₁ + (M : ℝ) ^ 2 * √L₄ := by
    rw [hZ]
    refine (GaloisForLFunctions.HTGeometry.sqrt_add_le_sqrt_add_sqrt' (by positivity)
      (by positivity)).trans (le_of_eq ?_)
    rw [show (M : ℝ) ^ 6 * L₁ ^ 2 = ((M : ℝ) ^ 3 * L₁) ^ 2 by ring,
      Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity),
      show (M : ℝ) ^ 4 = ((M : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hroot := (le_abs_self _).trans (Real.abs_le_sqrt hbig)
  have hTδ' : √(T ^ δ) ≤ T ^ δ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  calc ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2
      ≤ √(momentConstant 2 * (130 * 16 ^ 6 * c) * (W.card : ℝ) * T ^ δ * Z) := hroot
    _ = √(momentConstant 2 * (130 * 16 ^ 6 * c)) * √(W.card : ℝ) * √(T ^ δ) * √Z := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity)]
    _ ≤ √(momentConstant 2 * (130 * 16 ^ 6 * c)) * √(W.card : ℝ) * T ^ δ *
          ((M : ℝ) ^ 3 * L₁ + (M : ℝ) ^ 2 * √L₄) := by
        gcongr
    _ = _ := by ring

/-- **Guth–Maynard Proposition 10.1, assembly from Proposition 7.2 (explicit form).**

Assembly lemma: the hypothesis `hS₃` is the conclusion of Proposition 7.2 for an arbitrary real
`S₃` and an arbitrary finite set `𝓜` in the box; `f` is arbitrary data with `R̃² ≤ f` on
`[−20, 20]`, the Lemma 8.4 decay `ξ² |f̂(ξ)| ≤ A T³ sup f`, and `∫ f ≤ L₁`, `∫ f² ≤ L₄`.
For `δ > 0` there is `K` (depending on `δ`, `A`) with
`S₃ ≤ X K T^δ |W|^{1/2} ((NM)² L₁ + N (NM) L₄^{1/2}) + Y`.
With `NM ⪅ T`, `L₁ ≪ |W|`, `L₄ ⪅ E(W)` this is `S₃ ⪅ T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`. -/
theorem propTenOne_of_expansion {δ : ℝ} (hδ : 0 < δ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T N : ℝ) (M₁ M : ℕ) (ψ₁ ψ₂ f : ℝ → ℝ) (W : Finset ℝ)
      (𝓜 : Finset (ℤ × ℤ × ℤ)) (L₁ L₄ S₃ X Y : ℝ), 1 ≤ T → 0 < N → 1 ≤ M₁ → M₁ ≤ M →
      IsSmoothingPair ψ₁ ψ₂ → IsSeparated 1 W → (∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) →
      Continuous f → HasCompactSupport f → (∀ u, 0 ≤ f u) →
      (∀ u, |u| ≤ 20 → smoothedLagSum ψ₁ ψ₂ N M W u ^ 2 ≤ f u) →
      (∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * T ^ 3 * ⨆ x, f x) →
      ∫ u, f u ≤ L₁ → ∫ u, f u ^ 2 ≤ L₄ → 0 ≤ X →
      S₃ ≤ X * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 + Y →
      S₃ ≤ X * K * T ^ δ * √(W.card : ℝ) * ((N * M) ^ 2 * L₁ + N * (N * M) * √L₄) + Y := by
  obtain ⟨K, hK, hmain⟩ := sum_smoothedCubicTerm_le_of_decay hδ hA
  refine ⟨K, hK, fun T N M₁ M ψ₁ ψ₂ f W 𝓜 L₁ L₄ S₃ X Y hT hN hM₁ hM₁M hψ hW h𝓜 hf hfc hf0
    hmaj hdec hL₁ hL₄ hX hS₃ => ?_⟩
  have hM : (0 : ℝ) < M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM₁.trans hM₁M
    linarith
  have hb := hmain T N M₁ M ψ₁ ψ₂ f W 𝓜 L₁ L₄ hT hN hM₁ hM₁M hψ hW h𝓜 hf hfc hf0 hmaj hdec hL₁ hL₄
  have hc : 0 ≤ X * (N ^ 2 / M) := by positivity
  have := mul_le_mul_of_nonneg_left hb hc
  have e : X * (N ^ 2 / M) * (K * T ^ δ * √(W.card : ℝ) * ((M : ℝ) ^ 3 * L₁ + (M : ℝ) ^ 2 * √L₄)) =
      X * K * T ^ δ * √(W.card : ℝ) * ((N * M) ^ 2 * L₁ + N * (N * M) * √L₄) := by
    field_simp
  rw [e] at this
  linarith

/-- **Guth–Maynard Proposition 10.1** (`S₃ ⪅ T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`), assembled
from Proposition 7.2 in the paper's `T^{o(1)}` form.

Assembly lemma: the hypothesis is the Proposition 7.2 inequality
`S₃ ≤ C₇ T^ε (N²/M) Σ_{m ∈ 𝓜} Ĩ_m + C₇ T^{-100}` with `NM ≤ C₇ T^{1+ε}`, and `f` is data with
`R̃² ≤ f` on `[−20, 20]`, `ξ² |f̂(ξ)| ≤ A T³ sup f` (Lemma 8.4), `∫ f ≤ C₁ |W|` (Lemma 8.2) and
`∫ f² ≤ C₄ E(W)` (Lemma 8.3). For every `δ > 0` there is `K` with
`S₃ ≤ C₇ K (C₇² C₁ + C₇ C₄^{1/2}) T^δ (T^ε)³ (T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2})
  + C₇ T^{-100}`. -/
theorem guthMaynard_prop101 {δ : ℝ} (hδ : 0 < δ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε T N C₇ C₁ C₄ : ℝ) (M₁ M : ℕ) (ψ₁ ψ₂ f : ℝ → ℝ) (W : Finset ℝ)
      (𝓜 : Finset (ℤ × ℤ × ℤ)) (S₃ : ℝ), 0 ≤ ε → 1 ≤ T → 0 < N → 0 ≤ C₇ → 0 ≤ C₁ → 0 ≤ C₄ →
      1 ≤ M₁ → M₁ ≤ M → N * M ≤ C₇ * T ^ (1 + ε) →
      IsSmoothingPair ψ₁ ψ₂ → IsSeparated 1 W → (∀ m ∈ 𝓜, InPropSevenTwoBox M₁ M m) →
      Continuous f → HasCompactSupport f → (∀ u, 0 ≤ f u) →
      (∀ u, |u| ≤ 20 → smoothedLagSum ψ₁ ψ₂ N M W u ^ 2 ≤ f u) →
      (∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * T ^ 3 * ⨆ x, f x) →
      ∫ u, f u ≤ C₁ * W.card → ∫ u, f u ^ 2 ≤ C₄ * additiveEnergy W →
      S₃ ≤ C₇ * T ^ ε * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 +
        C₇ * T ^ (-100 : ℝ) →
      S₃ ≤ C₇ * K * (C₇ ^ 2 * C₁ + C₇ * √C₄) * T ^ δ * (T ^ ε) ^ 3 *
          (T ^ 2 * W.card * √(W.card : ℝ) + T * N * √(W.card : ℝ) * √(additiveEnergy W : ℝ)) +
        C₇ * T ^ (-100 : ℝ) := by
  obtain ⟨K, hK, hmain⟩ := propTenOne_of_expansion hδ hA
  refine ⟨K, hK, fun ε T N C₇ C₁ C₄ M₁ M ψ₁ ψ₂ f W 𝓜 S₃ hε hT hN hC₇ hC₁ hC₄ hM₁ hM₁M hNM hψ hW
    h𝓜 hf hfc hf0 hmaj hdec hL₁ hL₄ hS₃ => ?_⟩
  have hT0 : 0 < T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT hε
  have hX : 0 ≤ C₇ * T ^ ε := by positivity
  have h := hmain T N M₁ M ψ₁ ψ₂ f W 𝓜 _ _ S₃ (C₇ * T ^ ε) (C₇ * T ^ (-100 : ℝ)) hT hN hM₁ hM₁M
    hψ hW h𝓜 hf hfc hf0 hmaj hdec hL₁ hL₄ hX hS₃
  have hNM0 : 0 ≤ N * M := by positivity
  have hpow1 : T ^ (1 + ε) = T * T ^ ε := by rw [Real.rpow_add hT0, Real.rpow_one]
  rw [hpow1] at hNM
  -- opaque abbreviations keep the final algebra linear
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ ε := ⟨_, rfl⟩
  obtain ⟨Td, hTd⟩ : ∃ Td, Td = T ^ δ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = (W.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨sw, hsw⟩ : ∃ sw, sw = √(W.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨se, hse⟩ : ∃ se, se = √(additiveEnergy W : ℝ) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ s4, s4 = √C₄ := ⟨_, rfl⟩
  have hsqrt4 : √(C₄ * additiveEnergy W) = s4 * se := by rw [hs4, hse]; exact Real.sqrt_mul hC₄ _
  rw [← hP, ← hTd, ← hsw, ← hw, hsqrt4] at h
  rw [← hP] at hNM
  rw [← hP, ← hTd, ← hsw, ← hw, ← hse, ← hs4]
  have hP1 : 1 ≤ P := hP ▸ hTε
  have hw0 : 0 ≤ w := hw ▸ Nat.cast_nonneg _
  have hsw0 : 0 ≤ sw := hsw ▸ Real.sqrt_nonneg _
  have hse0 : 0 ≤ se := hse ▸ Real.sqrt_nonneg _
  have hs40 : 0 ≤ s4 := hs4 ▸ Real.sqrt_nonneg _
  have hTd0 : 0 ≤ Td := hTd ▸ Real.rpow_nonneg hT0.le _
  -- the two terms
  have t1 : (N * M) ^ 2 * (C₁ * w) ≤ C₇ ^ 2 * C₁ * P ^ 2 * (T ^ 2 * w) := by
    have hNMsq : (N * M) ^ 2 ≤ (C₇ * (T * P)) ^ 2 := pow_le_pow_left₀ hNM0 hNM 2
    calc (N * M) ^ 2 * (C₁ * w) ≤ (C₇ * (T * P)) ^ 2 * (C₁ * w) := by gcongr
      _ = C₇ ^ 2 * C₁ * P ^ 2 * (T ^ 2 * w) := by ring
  have t2 : N * (N * M) * (s4 * se) ≤ C₇ * s4 * P ^ 2 * (T * N * se) := by
    have hPP : P ≤ P ^ 2 := by nlinarith
    calc N * (N * M) * (s4 * se) ≤ N * (C₇ * (T * P)) * (s4 * se) := by gcongr
      _ = C₇ * s4 * P * (T * N * se) := by ring
      _ ≤ C₇ * s4 * P ^ 2 * (T * N * se) := by gcongr
  have hab : (N * M) ^ 2 * (C₁ * w) + N * (N * M) * (s4 * se) ≤
      C₇ ^ 2 * C₁ * P ^ 2 * (T ^ 2 * w) + C₇ * s4 * P ^ 2 * (T * N * se) := add_le_add t1 t2
  have hpre : 0 ≤ C₇ * P * K * Td * sw := by positivity
  have hmul := mul_le_mul_of_nonneg_left hab hpre
  have hextra : 0 ≤ C₇ * K * Td * P ^ 3 * sw * (C₇ ^ 2 * C₁ * (T * N * se) + C₇ * s4 * (T ^ 2 * w)) := by
    positivity
  have e : C₇ * K * (C₇ ^ 2 * C₁ + C₇ * s4) * Td * P ^ 3 * (T ^ 2 * w * sw + T * N * sw * se) =
      C₇ * P * K * Td * sw * (C₇ ^ 2 * C₁ * P ^ 2 * (T ^ 2 * w) + C₇ * s4 * P ^ 2 * (T * N * se)) +
        C₇ * K * Td * P ^ 3 * sw * (C₇ ^ 2 * C₁ * (T * N * se) + C₇ * s4 * (T ^ 2 * w)) := by ring
  rw [e]
  linarith

end

end RHTower.GuthMaynard
