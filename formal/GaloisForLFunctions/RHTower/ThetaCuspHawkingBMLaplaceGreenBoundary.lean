import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceEndpointGreen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Physical endpoint conditions of the actual retained-source inverse. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Both full-endpoint moments extend continuously over the entire radial interval. -/
theorem greenMoments_continuousOn {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ContinuousOn (horizonMoment w chi s a J K T) (Icc 0 1) ∧
    ContinuousOn (outerMoment w chi s a J K T) (Icc 0 1) := by
  have hi := greenIntegrands_intervalIntegrable h s a J K T
  constructor
  · simpa only [horizonMoment,uIcc_of_le (show (0:ℝ)≤1 by norm_num)] using!
      intervalIntegral.continuousOn_primitive_interval' hi.1 (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 1)
  · have hi' : IntegrableOn (fun t => normalizable w chi t*sourceProfile s w a J K T t/(-connection w chi))
        (uIcc (0:ℝ) 1) := by
      rw [uIcc_of_le (show (0:ℝ)≤1 by norm_num)]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hi.2
    simpa only [outerMoment,uIcc_of_le (show (0:ℝ)≤1 by norm_num)] using!
      intervalIntegral.continuousOn_primitive_interval_left hi'

/-- The actual Green response satisfies the zero AdS boundary condition. -/
theorem response_boundary {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Tendsto (response w chi s a J K T) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have hc := greenMoments_continuousOn h s a J K T
  have hA := (hc.1 1 (by norm_num)).mono Ioo_subset_Icc_self
  have hB := (hc.2 1 (by norm_num)).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsLT (show (0:ℝ)<1 by norm_num)] at hA hB
  have hB0 : outerMoment w chi s a J K T 1=0 := by simp [outerMoment]
  rw [hB0] at hB
  unfold response
  simpa only [zero_mul,mul_zero,add_zero] using!
    (((normalizable_boundary h).mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)).mul hA).add
      ((horizon_boundary h).mul hB)

private theorem horizonMoment_bound {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, z ∈ Ioo 0 1 → ‖horizonMoment w chi s a J K T z‖ ≤ C*z^(w.re+1) := by
  obtain ⟨D,hD,hb⟩ := horizon_source_bound h s a J K T
  let E : ℝ := D/‖connection w chi‖
  have hE : 0 ≤ E := div_nonneg hD (norm_nonneg _)
  refine ⟨E/(w.re+1),div_nonneg hE (by linarith [chamber_re_pos h]),fun z hz => ?_⟩
  have hb' : ∀ᵐ t : ℝ, t ∈ Ioc 0 z →
      ‖horizon w chi t*sourceProfile s w a J K T t/(-connection w chi)‖ ≤ E*t^w.re := by
    apply Eventually.of_forall
    intro t ht
    rw [norm_div,norm_neg]
    simpa only [E,div_mul_eq_mul_div] using
      div_le_div_of_nonneg_right (hb t ⟨ht.1,lt_of_le_of_lt ht.2 hz.2⟩) (norm_nonneg (connection w chi))
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := z)
    (show -1<w.re by linarith [chamber_re_pos h])).const_mul E
  have hb'' := intervalIntegral.norm_integral_le_of_norm_le hz.1.le hb' hi
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (show -1<w.re by linarith [chamber_re_pos h])),
    Real.zero_rpow (show w.re+1≠0 by linarith [chamber_re_pos h]),sub_zero] at hb''
  simpa only [horizonMoment,div_mul_eq_mul_div,mul_div_assoc] using hb''

private theorem outerFactor_horizonMoment_zero {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Tendsto (fun z => outerFactor w chi z*horizonMoment w chi s a J K T z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let N := Nat.ceil w.re
  have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr (chamber_re_pos h)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hN))
  have hkle : w.re-1 ≤ (k:ℝ) := by
    have hn := Nat.le_ceil w.re
    change w.re ≤ (N:ℝ) at hn
    rw [hk] at hn
    push_cast at hn
    linarith
  have he : 0 < w.re+1-((k+1:ℕ):ℝ) := by
    have hn := Nat.ceil_lt_add_one (chamber_re_pos h).le
    change (N:ℝ) < w.re+1 at hn
    rw [hk] at hn
    linarith
  obtain ⟨D,hD,hF⟩ := outerFactor_bound h k hkle
  obtain ⟨C,hC,hA⟩ := horizonMoment_bound h s a J K T
  have ht : Tendsto (fun z : ℝ => (D*C)*z^(w.re+1-((k+1:ℕ):ℝ))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const he.le).tendsto (0:ℝ)
    have hx : Tendsto (fun z : ℝ => z^(w.re+1-((k+1:ℕ):ℝ))) (𝓝 (0:ℝ)) (𝓝 0) := by
      simpa only [Real.zero_rpow (ne_of_gt he)] using hc
    simpa only [mul_zero] using (hx.const_mul (D*C)).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from inf_le_left)
  apply squeeze_zero_norm' ?_ ht
  have hlt : ∀ᶠ z : ℝ in 𝓝[>] (0:ℝ), z < 1 :=
    (show ∀ᶠ z : ℝ in 𝓝 0, z < 1 from Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin,hlt] with z hz0 hz1
  have hz : z ∈ Ioo 0 1 := ⟨hz0,hz1⟩
  have hs : ‖power (1/2) (1-z)‖ ≤ 1 := by
    rw [power_half_eq_sqrt (sub_nonneg.mpr hz1.le),Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by linarith [hz.1])
  have hV : ‖outerFactor w chi z‖ ≤ D/z^(k+1) := by
    unfold outerFactor
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul hs (hF z hz) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  rw [norm_mul]
  calc
    _ ≤ (D/z^(k+1))*(C*z^(w.re+1)) := mul_le_mul hV (hA z hz) (norm_nonneg _) (div_nonneg hD (pow_nonneg hz.1.le _))
    _ = (D*C)*z^(w.re+1-((k+1:ℕ):ℝ)) := by rw [Real.rpow_sub hz0,Real.rpow_natCast]; ring

/-- Finite ingoing amplitude at the true horizon: the full source response,
divided by its original horizon factor z^(w/2), tends to its endpoint moment. -/
theorem response_ingoing {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Tendsto (fun z => response w chi s a J K T z/power (w/2) z) (𝓝[>] (0:ℝ))
      (𝓝 (outerMoment w chi s a J K T 0)) := by
  have hc := (greenMoments_continuousOn h s a J K T).2 0 (by norm_num)
  have hB := hc.mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT (show (0:ℝ)<1 by norm_num)] at hB
  have hF := (gaussFactor_derivatives (z := 0) h false (by simp)).1.comp_ofReal.continuousAt.tendsto
  simp only [Complex.ofReal_zero,gaussFactor_zero] at hF
  have ht := (outerFactor_horizonMoment_zero h s a J K T).add
    ((hF.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from inf_le_left)).mul hB)
  simp only [one_mul,zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp [response,normalizable,horizon,dress]
  field_simp [power_ne_zero (w/2) hz]

/-- The actual source response has zero horizon value in the causal chamber,
with the stronger finite ingoing amplitude proved separately. -/
theorem response_horizon {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Tendsto (response w chi s a J K T) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : 0 < (w/2).re := by simpa using half_pos (chamber_re_pos h)
  have ht := ((power_tendsto_zero hp).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from inf_le_left)).mul
    (response_ingoing h s a J K T)
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  field_simp [power_ne_zero (w/2) hz]

end
end RHTower.D4BMLaplaceRadial
