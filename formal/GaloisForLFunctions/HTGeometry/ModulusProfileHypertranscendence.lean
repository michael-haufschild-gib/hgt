import GaloisForLFunctions.HTGeometry.ModulusPhaseSequence
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily

/-!
# Every admissible modulus profile has a hypertranscendental realization

Given a modulus profile of infinite support and infinite radius of convergence, the phases chosen in
`ModulusPhaseSequence` make the resulting entire function hypertranscendental, while its Taylor
coefficient magnitudes are exactly the prescribed profile.

Coefficient magnitudes — hence the maximum-term function, the logarithmic Newton envelope, the
active indices and the plateau widths — carry no differential-algebraic information.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The entire realization of a modulus profile with independent phases. -/
def modulusProfileFunction (ρ : ℕ → ℝ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (phaseSeq ρ)

theorem radius_eq_top_of_bounded {ρ : ℕ → ℝ}
    (h : ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |ρ n| * r ^ n ≤ C) :
    (FormalMultilinearSeries.ofScalars ℂ (phaseSeq ρ)).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr0)
  obtain ⟨C, hC⟩ := h r hrpos
  refine FormalMultilinearSeries.le_radius_of_bound _ (max C 1) fun n => ?_
  have hnorm : ‖FormalMultilinearSeries.ofScalars ℂ (phaseSeq ρ) n‖ = ‖phaseSeq ρ n‖ := by
    simp
  rw [hnorm, norm_phaseSeq]
  exact le_trans (hC n) (le_max_left _ _)

theorem contDiff_modulusProfileFunction {ρ : ℕ → ℝ}
    (h : ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |ρ n| * r ^ n ≤ C) :
    ContDiff ℂ (⊤ : ℕ∞) (modulusProfileFunction ρ) := by
  set p := FormalMultilinearSeries.ofScalars ℂ (phaseSeq ρ) with hp
  have hr : p.radius = ⊤ := radius_eq_top_of_bounded h
  have hball : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hball.analyticOnNhd
  exact ha.contDiff

theorem taylorPS_modulusProfileFunction {ρ : ℕ → ℝ}
    (h : ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |ρ n| * r ^ n ≤ C) (n : ℕ) :
    PowerSeries.coeff n (GaloisForLFunctions.taylorPS (modulusProfileFunction ρ))
      = phaseSeq ρ n :=
  GaloisForLFunctions.taylorPS_ofScalarsSum_of_radius_eq_top (phaseSeq ρ)
    (radius_eq_top_of_bounded h) n

/-- **The prescribed magnitudes are attained.** -/
theorem norm_taylorPS_modulusProfileFunction {ρ : ℕ → ℝ}
    (h : ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |ρ n| * r ^ n ≤ C) (n : ℕ) :
    ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS (modulusProfileFunction ρ))‖ = |ρ n| := by
  rw [taylorPS_modulusProfileFunction h, norm_phaseSeq]

/-- **Every admissible modulus profile has a hypertranscendental realization.** -/
theorem hypertranscendental_modulusProfileFunction {ρ : ℕ → ℝ}
    (h : ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |ρ n| * r ^ n ≤ C)
    (hS : {n : ℕ | ρ n ≠ 0}.Infinite) :
    GaloisForLFunctions.Hypertranscendental (modulusProfileFunction ρ) := by
  refine GaloisForLFunctions.hypertranscendental_of_aeval_survives
    (contDiff_modulusProfileFunction h) ?_
  intro m Q hQ0
  have htaylor : GaloisForLFunctions.taylorPS (modulusProfileFunction ρ)
      = PowerSeries.mk (phaseSeq ρ) := by
    ext n
    rw [taylorPS_modulusProfileFunction h, PowerSeries.coeff_mk]
  rw [htaylor]
  refine aeval_formalJets_ne_zero_of_infinite_independent hS ?_ hQ0
  intro T hTS
  exact algebraicIndepOn_phaseSeq T fun i hi => hTS hi

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The root test.**  A modulus profile whose `n`-th roots tend to zero has infinite radius of
convergence, in the bounded form used above. -/
theorem bounded_of_root_tendsto {ρ : ℕ → ℝ}
    (h : Filter.Tendsto (fun n : ℕ => |ρ n| ^ ((n : ℝ)⁻¹)) Filter.atTop (nhds 0)) :
    ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |ρ n| * r ^ n ≤ C := by
  intro r hr
  have hpos : 0 < (2 * r)⁻¹ := by positivity
  have hev : ∀ᶠ n : ℕ in Filter.atTop, |ρ n| ^ ((n : ℝ)⁻¹) < (2 * r)⁻¹ := by
    have := h (Metric.ball_mem_nhds (0 : ℝ) hpos)
    filter_upwards [this] with n hn
    have : |(|ρ n| ^ ((n : ℝ)⁻¹)) - 0| < (2 * r)⁻¹ := by
      simpa [Real.dist_eq] using hn
    have h2 : |ρ n| ^ ((n : ℝ)⁻¹) ≤ |(|ρ n| ^ ((n : ℝ)⁻¹))| := le_abs_self _
    calc |ρ n| ^ ((n : ℝ)⁻¹) ≤ |(|ρ n| ^ ((n : ℝ)⁻¹))| := h2
      _ < (2 * r)⁻¹ := by simpa using this
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n ∈ Finset.range (N + 1), |ρ n| * r ^ n ≤ M := by
    obtain ⟨n₀, -, hn₀⟩ := Finset.exists_max_image (Finset.range (N + 1))
      (fun n => |ρ n| * r ^ n) ⟨0, Finset.mem_range.mpr (by omega)⟩
    exact ⟨_, fun n hn => hn₀ n hn⟩
  refine ⟨max M 1, fun n => ?_⟩
  by_cases hn : n ≤ N
  · exact le_trans (hM n (Finset.mem_range.mpr (by omega))) (le_max_left _ _)
  · push Not at hn
    have hn1 : 1 ≤ n := by omega
    have hroot := hN n (by omega)
    have hbase : (0 : ℝ) ≤ |ρ n| ^ ((n : ℝ)⁻¹) := Real.rpow_nonneg (abs_nonneg _) _
    have hpow : |ρ n| < ((2 * r)⁻¹) ^ n := by
      have hid : (|ρ n| ^ ((n : ℝ)⁻¹)) ^ n = |ρ n| :=
        Real.rpow_inv_natCast_pow (abs_nonneg _) (by omega)
      calc |ρ n| = (|ρ n| ^ ((n : ℝ)⁻¹)) ^ n := hid.symm
        _ < ((2 * r)⁻¹) ^ n := by
            refine pow_lt_pow_left₀ hroot hbase (by omega)
    have hrn : (0 : ℝ) < r ^ n := by positivity
    have hfinal : |ρ n| * r ^ n < ((2 * r)⁻¹) ^ n * r ^ n := by
      exact mul_lt_mul_of_pos_right hpow hrn
    have hsimp : ((2 * r)⁻¹) ^ n * r ^ n = (2 : ℝ)⁻¹ ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hsimp] at hfinal
    have hle1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := by
      refine pow_le_one₀ (by norm_num) (by norm_num)
    exact le_trans (le_of_lt (lt_of_lt_of_le hfinal hle1)) (le_max_right _ _)

end

end GaloisForLFunctions.HTGeometry
