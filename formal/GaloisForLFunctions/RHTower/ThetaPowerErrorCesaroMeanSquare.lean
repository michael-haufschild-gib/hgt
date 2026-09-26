import GaloisForLFunctions.RHTower.ThetaPowerMeanSquare
import GaloisForLFunctions.RHTower.ThetaPowerSmoothDirichletBounds

/-!
# Mean square of the Dirichlet error over `[0, T]`

For `σ₁ ≤ Re z ≤ 1`, `|Im z| ≤ 1` and `T ≥ 1`,

  `∫₀ᵀ |E^δ(z + it)|² dt ≤ C₀(δ) + 4 C δ^{2η} T`.

`C` is the dyadic constant of `exists_lintegral_thetaPowerDirichletError_le`, independent of `δ`.  The height
range `[Im z, Im z + T]` is covered by `[-1, 1]` and the dyadic blocks `[2^k, 2^{k+1}]`, `k ≤ log₂(T+1)`.
On `[-1, 1]`, `E^δ = D - D^δ` is bounded because `D` is continuous and `|D^δ| ≤ α^{-2} Σ |b_n| e^{-λ_n δ}`.
-/

open Complex Real MeasureTheory Set Filter Topology Metric

namespace RHTower

noncomputable section

variable {a : ℝ}

/-- `E^δ` is bounded on the rectangle `σ₁ ≤ Re w ≤ 1`, `|Im w| ≤ 1`, for `σ₁ > 0`. -/
theorem exists_norm_thetaPowerDirichletError_le_rect (ha0 : 0 < a) (ha4 : a ≤ 4) {δ σ₁ : ℝ}
    (hδ : 0 < δ) (hσ₁ : 0 < σ₁) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 1 → |w.im| ≤ 1 →
      ‖thetaPowerDirichletError a δ w‖ ≤ B := by
  obtain ⟨BD, hBD⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
    (differentiable_thetaPowerDirichlet ha0).continuous.continuousOn
  set S := (∑' n, ‖thetaPowerCoeff a n‖ * thetaPowerSmoothWeight a δ n) * (a / 4) ^ (-2 : ℝ) with hS
  have hS0 : 0 ≤ S := mul_nonneg (tsum_nonneg fun n =>
    mul_nonneg (norm_nonneg _) (thetaPowerSmoothWeight_pos a δ n).le) (by positivity)
  refine ⟨max BD 0 + S, by positivity, fun w h1 h2 h3 => ?_⟩
  have hw0 : 0 < w.re := by linarith
  have hE : thetaPowerDirichletError a δ w =
      thetaPowerDirichlet a w - thetaPowerSmoothDirichlet a δ w := by
    rw [thetaPowerDirichlet_split ha0 hδ hw0]; ring
  have hwball : w ∈ closedBall (0 : ℂ) 2 := by
    rw [mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 2 := by rw [abs_of_pos hw0]; linarith
  have hD := (hBD w hwball).trans (le_max_left BD 0)
  have hDδ := norm_thetaPowerSmoothDirichlet_le ha0 ha4 hδ hw0.le (by linarith) (z := w)
  rw [hE]
  calc ‖thetaPowerDirichlet a w - thetaPowerSmoothDirichlet a δ w‖
      ≤ ‖thetaPowerDirichlet a w‖ + ‖thetaPowerSmoothDirichlet a δ w‖ := norm_sub_le _ _
    _ ≤ max BD 0 + S := add_le_add hD hDδ

/-- Accumulation over dyadic blocks: `∫_1^{2^K} g ≤ c (2^K - 1)` from `∫_T^{2T} g ≤ c T`. -/
theorem lintegral_Icc_one_two_pow_le {g : ℝ → ENNReal} {c : ℝ} (hc : 0 ≤ c)
    (hdy : ∀ T : ℝ, 1 ≤ T → ∫⁻ t in Icc T (2 * T), g t ≤ ENNReal.ofReal (c * T)) (K : ℕ) :
    ∫⁻ t in Icc 1 ((2 : ℝ) ^ K), g t ≤ ENNReal.ofReal (c * ((2 : ℝ) ^ K - 1)) := by
  induction K with
  | zero =>
    simp only [pow_zero, Icc_self, sub_self, mul_zero, ENNReal.ofReal_zero]
    exact (setLIntegral_measure_zero _ _ Real.volume_singleton).le
  | succ K ih =>
    have hK : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    calc ∫⁻ t in Icc 1 ((2 : ℝ) ^ (K + 1)), g t
        ≤ ∫⁻ t in Icc 1 ((2 : ℝ) ^ K) ∪ Icc ((2 : ℝ) ^ K) (2 * 2 ^ K), g t := by
          apply lintegral_mono_set
          intro s hs
          rcases le_total s (2 ^ K) with h | h
          · exact Or.inl ⟨hs.1, h⟩
          · refine Or.inr ⟨h, ?_⟩
            have := hs.2
            rw [pow_succ] at this
            linarith
      _ ≤ (∫⁻ t in Icc 1 ((2 : ℝ) ^ K), g t) + ∫⁻ t in Icc ((2 : ℝ) ^ K) (2 * 2 ^ K), g t :=
          lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (c * (2 ^ K - 1)) + ENNReal.ofReal (c * 2 ^ K) := add_le_add ih (hdy _ hK)
      _ = ENNReal.ofReal (c * (2 ^ (K + 1) - 1)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hc (by linarith)) (by positivity)]
          congr 1
          rw [pow_succ]
          ring

/-- **Mean square over `[0, T]`.** -/
theorem exists_lintegral_thetaPowerDirichletError_Icc_zero_le (ha0 : 0 < a) (ha1 : a < 1 / 2)
    {η σ₁ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hσ₁ : 1 / 4 + η < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (z : ℂ) (T : ℝ), σ₁ ≤ z.re → z.re ≤ 1 →
      |z.im| ≤ 1 → 1 ≤ T →
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (‖thetaPowerDirichletError a δ (z + t * I)‖ ^ 2) ≤
        ENNReal.ofReal (C₀ + 4 * C * δ ^ (2 * η) * T) := by
  obtain ⟨C, hC, hdy⟩ := exists_lintegral_thetaPowerDirichletError_le ha0 ha1 hη0 hη1 hσ₁
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨B, hB, hbd⟩ :=
    exists_norm_thetaPowerDirichletError_le_rect ha0 (by linarith) hδ (show 0 < σ₁ by linarith)
  refine ⟨2 * B ^ 2, by positivity, fun z T h1 h2 h3 hT => ?_⟩
  set g : ℝ → ENNReal :=
    fun s => ENNReal.ofReal (‖thetaPowerDirichletError a δ ((z.re : ℂ) + s * I)‖ ^ 2) with hg
  have hshift : ∀ t : ℝ, z + t * I = (z.re : ℂ) + ((z.im + t : ℝ) : ℂ) * I := by
    intro t; apply Complex.ext <;> simp
  have hcov : ∫⁻ t in Icc 0 T, ENNReal.ofReal (‖thetaPowerDirichletError a δ (z + t * I)‖ ^ 2) =
      ∫⁻ s in Icc z.im (z.im + T), g s := by
    have := (measurePreserving_add_left volume z.im).setLIntegral_comp_emb
      (measurableEmbedding_addLeft z.im) g (Icc 0 T)
    rw [Set.image_const_add_Icc, add_zero] at this
    rw [← this]
    congr 1
    funext t
    simp only [hg]
    rw [hshift]
  rw [hcov]
  obtain ⟨n, hn1, hn⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ T + 1 by linarith) (show (1 : ℝ) < 2 by norm_num)
  have him := abs_le.mp h3
  have hcover : Icc z.im (z.im + T) ⊆ Icc (-1) 1 ∪ Icc 1 ((2 : ℝ) ^ (n + 1)) := by
    intro s hs
    rcases le_total s 1 with h | h
    · exact Or.inl ⟨by linarith [hs.1], h⟩
    · exact Or.inr ⟨h, by linarith [hs.2]⟩
  have hlow : ∫⁻ s in Icc (-1 : ℝ) 1, g s ≤ ENNReal.ofReal (2 * B ^ 2) := by
    calc ∫⁻ s in Icc (-1 : ℝ) 1, g s ≤ ∫⁻ _ in Icc (-1 : ℝ) 1, ENNReal.ofReal (B ^ 2) := by
          refine setLIntegral_mono measurable_const fun s hs => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hw := hbd ((z.re : ℂ) + s * I) (by simpa using h1) (by simpa using h2)
            (by simpa [abs_le] using hs)
          exact pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ = ENNReal.ofReal (2 * B ^ 2) := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hc0 : 0 ≤ C * δ ^ (2 * η) := by positivity
  have hhigh := lintegral_Icc_one_two_pow_le (g := g) hc0
    (fun T₀ hT₀ => hdy δ z.re T₀ hδ h1 h2 hT₀) (n + 1)
  have hpow : (2 : ℝ) ^ (n + 1) - 1 ≤ 4 * T := by
    have : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    linarith
  calc ∫⁻ s in Icc z.im (z.im + T), g s
      ≤ ∫⁻ s in Icc (-1 : ℝ) 1 ∪ Icc 1 ((2 : ℝ) ^ (n + 1)), g s := lintegral_mono_set hcover
    _ ≤ (∫⁻ s in Icc (-1 : ℝ) 1, g s) + ∫⁻ s in Icc 1 ((2 : ℝ) ^ (n + 1)), g s :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (2 * B ^ 2) + ENNReal.ofReal (C * δ ^ (2 * η) * ((2 : ℝ) ^ (n + 1) - 1)) :=
        add_le_add hlow hhigh
    _ = ENNReal.ofReal (2 * B ^ 2 + C * δ ^ (2 * η) * ((2 : ℝ) ^ (n + 1) - 1)) := by
        rw [ENNReal.ofReal_add (by positivity)
          (mul_nonneg hc0 (by linarith [one_le_pow₀ (M₀ := ℝ) (show (1 : ℝ) ≤ 2 by norm_num) (n := n + 1)]))]
    _ ≤ ENNReal.ofReal (2 * B ^ 2 + 4 * C * δ ^ (2 * η) * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

end

end RHTower
