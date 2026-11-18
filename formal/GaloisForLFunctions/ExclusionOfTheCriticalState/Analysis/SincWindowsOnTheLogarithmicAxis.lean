import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity
import GaloisForLFunctions.HTGeometry.LaplaceMomentPositivity

/-!
# Positive bounded-width windows on the logarithmic axis

A fourth power of sinc is a characteristic function of four bounded independent
frequencies. Multiplying it by a gamma density normalized at its mode preserves
a positive mass near the centre and gives a uniformly bounded second moment.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry

/-- The fourth convolution power of uniform frequencies in the symmetric interval of radius δ. -/
def sincFourthFrequency (δ : ℝ) : Measure ℝ :=
  convPow (centeredUniformClockProbabilityMeasure δ : Measure ℝ) 4

instance (δ : ℝ) : IsProbabilityMeasure (sincFourthFrequency δ) :=
  isProbabilityMeasure_convPow _ _

theorem charFun_sincFourthFrequency (δ u : ℝ) :
    charFun (sincFourthFrequency δ) u = (Real.sinc (δ*u):ℂ)^4 := by
  rw [sincFourthFrequency,charFun_convPow_probability,charFun_centeredUniformClockProbabilityMeasure]

private theorem ae_abs_le_convPow (Q : Measure ℝ) [IsProbabilityMeasure Q] {δ : ℝ}
    (hq : ∀ᵐ ξ ∂Q, |ξ| ≤ δ) (n : ℕ) : ∀ᵐ ξ ∂convPow Q n, |ξ| ≤ (n:ℝ)*δ := by
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    haveI := isProbabilityMeasure_convPow Q n
    rw [convPow,Measure.conv,ae_map_iff (by fun_prop) (by measurability)]
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hq] with x hx
    filter_upwards [ih] with y hy
    exact (abs_add_le x y).trans ((add_le_add hx hy).trans_eq (by push_cast; ring))

theorem sincFourthFrequency_support {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ξ ∂sincFourthFrequency δ, |ξ| ≤ 4*δ := by
  have hq : ∀ᵐ ξ ∂(centeredUniformClockProbabilityMeasure δ : Measure ℝ), |ξ| ≤ δ := by
    rw [centeredUniformClockProbabilityMeasure,ProbabilityMeasure.toMeasure_map,
      ae_map_iff (by fun_prop) (by measurability)]
    change ∀ᵐ u ∂volume.restrict (Ioc (0:ℝ) 1), |δ*(2*u-1)| ≤ δ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [abs_mul,abs_of_pos hδ]
    apply mul_le_of_le_one_right hδ.le
    exact abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
  exact_mod_cast ae_abs_le_convPow _ hq 4

/-- Gamma weight with height one at its mode, localized by a positive sinc fourth power. -/
def localizedPrimeWindow (δ : ℝ) (n : ℕ) (T t : ℝ) : ℝ :=
  laplacePeak n t ^ n * Real.sinc (δ*(t-T))^4

theorem localizedPrimeWindow_eq {δ : ℝ} {n : ℕ} (hn : 0 < n) (T t : ℝ) :
    localizedPrimeWindow δ n T t = (t/(n:ℝ))^n * Real.exp ((n:ℝ)-t) * Real.sinc (δ*(t-T))^4 := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [localizedPrimeWindow,laplacePeak,mul_pow,← Real.exp_nat_mul]
  rw [show (n:ℝ)*(1-t/(n:ℝ)) = n-t by field_simp]

private theorem window_nonneg_le {δ : ℝ} {n : ℕ} (hn : 0 < n) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ localizedPrimeWindow δ n T t ∧ localizedPrimeWindow δ n T t ≤ Real.sinc (δ*(t-T))^4 := by
  have hp := laplacePeak_nonneg (t₀ := (n:ℝ)) (by exact_mod_cast hn) ht
  unfold localizedPrimeWindow
  exact ⟨mul_nonneg (pow_nonneg hp _) (by positivity),
    mul_le_of_le_one_left (by positivity) (pow_le_one₀ hp (laplacePeak_le_one _ _))⟩

private theorem integrable_sinc_sq_scaled {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ => Real.sinc (δ*u)^2) := by
  have h := BandLimitedPositiveDensity.integrable_sincSq.comp_mul_left'
    (div_ne_zero hδ.ne' Real.pi_ne_zero)
  apply h.congr (Eventually.of_forall fun u => ?_)
  change Real.sinc (Real.pi * (δ / Real.pi * u))^2 = _
  rw [show Real.pi * (δ / Real.pi * u) = δ*u by field_simp]

private theorem integrable_sinc_window_moment {δ : ℝ} (hδ : 0 < δ) :
    Integrable fun u : ℝ => (1+u^2)*Real.sinc (δ*u)^4 := by
  have hbase := (integrable_sinc_sq_scaled hδ).const_mul (1+(δ^2)⁻¹)
  apply hbase.mono' (by fun_prop) (Eventually.of_forall fun u => ?_)
  have hs : Real.sinc (δ*u)^2 ≤ 1 := by
    have h := Real.abs_sinc_le_one (δ*u)
    rw [← sq_abs (Real.sinc (δ*u))]
    exact pow_le_one₀ (abs_nonneg _) h
  have hsinc (x : ℝ) : x*Real.sinc x = Real.sin x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]; field_simp
  have hsin : δ^2*u^2*Real.sinc (δ*u)^2 ≤ 1 := by
    rw [← mul_pow,← mul_pow,hsinc]
    exact Real.sin_sq_le_one _
  have hm : u^2*Real.sinc (δ*u)^2 ≤ (δ^2)⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ (sq_pos_of_pos hδ)]
    linarith only [hsin]
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1+u^2)*Real.sinc (δ*u)^4 =
        (Real.sinc (δ*u)^2 + u^2*Real.sinc (δ*u)^2)*Real.sinc (δ*u)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add hs hm) (sq_nonneg _)

/-- Uniform positive mass and bounded second moment for every centre between adjacent modes. -/
theorem localizedPrimeWindow_mass_and_width {δ : ℝ} (hδ : 0 < δ) :
    ∃ m M : ℝ, 0 < m ∧ ∀ n : ℕ, 0 < n → ∀ T : ℝ, (n:ℝ) ≤ T → T ≤ n+1 →
      m ≤ ∫ t in Ioi (0:ℝ), localizedPrimeWindow δ n T t ∧
      (∫ t in Ioi (0:ℝ), (t-T)^2 * localizedPrimeWindow δ n T t) ≤ M := by
  let K := fun u : ℝ => (1+u^2)*Real.sinc (δ*u)^4
  have hK := integrable_sinc_window_moment hδ
  have hnear : ∀ᶠ u in 𝓝 (0:ℝ), 1/2 < Real.sinc (δ*u)^4 := by
    have hc : Continuous (fun u : ℝ => Real.sinc (δ*u)^4) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by norm_num : 1/2 < Real.sinc (δ*0)^4))
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let d := min (ε/2) 1
  have hd : 0 < d := lt_min (half_pos hε) zero_lt_one
  let m := d * (Real.exp (-2)/2)
  refine ⟨m,∫ u : ℝ, K u,mul_pos hd (half_pos (Real.exp_pos _)),?_⟩
  intro n hn T hT hT'
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hcont : Continuous (localizedPrimeWindow δ n T) := by unfold localizedPrimeWindow laplacePeak; fun_prop
  have htK : Integrable (fun t : ℝ => K (t-T)) := hK.comp_sub_right T
  have hmajor (t : ℝ) (ht : t ∈ Ioi 0) : localizedPrimeWindow δ n T t ≤ K (t-T) :=
    (window_nonneg_le hn T ht.le).2.trans (le_mul_of_one_le_left (by positivity) (by nlinarith [sq_nonneg (t-T)]))
  have hi : IntegrableOn (localizedPrimeWindow δ n T) (Ioi 0) :=
    htK.integrableOn.mono' hcont.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      rw [Real.norm_of_nonneg (window_nonneg_le hn T ht.le).1]; exact hmajor t ht)
  constructor
  · let S := Ioc T (T+d)
    have hsub : S ⊆ Ioi 0 := fun t ht => lt_trans (hn'.trans_le hT) ht.1
    have hlo (t : ℝ) (ht : t ∈ S) : Real.exp (-2)/2 ≤ localizedPrimeWindow δ n T t := by
      have hu : 0 < t-T := sub_pos.mpr ht.1
      have hε' : dist (t-T) 0 < ε := by
        rw [Real.dist_eq,sub_zero,abs_of_pos hu]
        have h := ht.2
        linarith only [h,min_le_left (ε/2) 1,hε]
      have hs := (hnear hε').le
      have hp : 1 ≤ (t/(n:ℝ))^n := one_le_pow₀ ((one_le_div hn').mpr (hT.trans ht.1.le))
      have he : Real.exp (-2) ≤ Real.exp ((n:ℝ)-t) := Real.exp_le_exp.mpr (by
        linarith only [ht.2,hT',min_le_right (ε/2) 1])
      rw [localizedPrimeWindow_eq hn]
      calc Real.exp (-2)/2 = (1*Real.exp (-2))*(1/2) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul hp he (Real.exp_pos _).le (le_trans zero_le_one hp)) hs
          (by norm_num) (by positivity)
    have hc : (∫ t in S, Real.exp (-2)/2) = m := by
      simp [S,m,Real.volume_Ioc,hd.le,Measure.real]
    rw [← hc]
    exact (setIntegral_mono_on (by simp [S]) (hi.mono_set hsub) measurableSet_Ioc hlo).trans
      (setIntegral_mono_set hi (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (window_nonneg_le hn T ht.le).1)
        hsub.eventuallyLE)
  · have hb (t : ℝ) (ht : t ∈ Ioi 0) : (t-T)^2*localizedPrimeWindow δ n T t ≤ K (t-T) :=
      (mul_le_mul_of_nonneg_left (window_nonneg_le hn T ht.le).2 (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (by linarith : (t-T)^2 ≤ 1+(t-T)^2) (by positivity))
    have hi₂ : IntegrableOn (fun t => (t-T)^2*localizedPrimeWindow δ n T t) (Ioi 0) :=
      htK.integrableOn.mono' (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (window_nonneg_le hn T ht.le).1)]; exact hb t ht)
    calc _ ≤ ∫ t in Ioi (0:ℝ), K (t-T) := setIntegral_mono_on hi₂ htK.integrableOn measurableSet_Ioi hb
      _ ≤ ∫ t : ℝ, K (t-T) := setIntegral_le_integral htK (Eventually.of_forall fun t => by dsimp [K]; positivity)
      _ = _ := integral_sub_right_eq_self K T

#print axioms localizedPrimeWindow_mass_and_width

end GaloisForLFunctions.ExclusionOfTheCriticalState
