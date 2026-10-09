import GaloisForLFunctions.RHTower.MobiusRieszNormalizedEscape
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Exact mass and quantitative escape for normalized threshold packets

The threshold primitive is a convolution of the causal exponential density with
one interval indicator per shift. Its integral is the product of the shifts.
After this normalization, total mass is one and the lower-tail mass below T is
at most exp((2/c)*T) * 2^(-length A) whenever every shift is at least c>0.
-/

noncomputable section

namespace RHTower.MobiusRieszSmoothing

open MeasureTheory Set Filter Topology

/-- The unnormalized density of one positive interval. -/
def intervalDensity (a : ℝ) : ℝ → ℝ := (Ioc 0 a).indicator (fun _ => 1)

/-- The causal exponential probability density. -/
def exponentialDensity : ℝ → ℝ := (Ioi 0).indicator (fun t => Real.exp (-t))

theorem integrable_intervalDensity (a : ℝ) : Integrable (intervalDensity a) := by
  rw [intervalDensity, integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by simp)

theorem integral_intervalDensity {a : ℝ} (ha : 0 ≤ a) :
    (∫ t, intervalDensity a t) = a := by
  rw [intervalDensity, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le ha, intervalIntegral.integral_const]
  simp

theorem integrable_exponentialDensity : Integrable exponentialDensity := by
  rw [exponentialDensity, integrable_indicator_iff measurableSet_Ioi]
  simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) (0:ℝ)

theorem integral_exponentialDensity : (∫ t, exponentialDensity t) = 1 := by
  rw [exponentialDensity, integral_indicator measurableSet_Ioi]
  simpa using integral_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) (0:ℝ)

/-- Box convolution is exactly the moving interval integral from the causal calculus. -/
theorem intervalDensity_convolution {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) (t : ℝ) :
    convolution (intervalDensity a) f (ContinuousLinearMap.lsmul ℝ ℝ) volume t =
      ∫ u in (t-a)..t, f u := by
  rw [convolution_def]
  change (∫ u, intervalDensity a u * f (t-u)) = _
  have he : (fun u => intervalDensity a u * f (t-u)) =
      (Ioc 0 a).indicator (fun u => f (t-u)) := by
    funext u
    by_cases hu : u ∈ Ioc 0 a <;> simp [intervalDensity, hu]
  rw [he, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_comp_sub_left]
  simp

private theorem hasDerivAt_hinge_off_zero {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt hinge (exponentialDensity t) t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have he : exponentialDensity t = 0 := by
      simp [exponentialDensity, not_lt.mpr ht.le]
    rw [he]
    apply (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact causal_hinge u hu.le
  · have he : exponentialDensity t = Real.exp (-t) := by
      simp [exponentialDensity, ht]
    rw [he]
    have hd : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-t)) t := by
      simpa using (((hasDerivAt_id t).neg).exp).const_sub 1
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact hinge_of_nonneg hu.le

theorem integral_exponentialDensity_eq_hinge_sub (a b : ℝ) :
    (∫ u in a..b, exponentialDensity u) = hinge b - hinge a := by
  apply integral_eq_of_hasDerivAt_off_countable hinge exponentialDensity
    (s := {0}) (Set.countable_singleton 0) continuous_hinge.continuousOn
  · intro t ht
    exact hasDerivAt_hinge_off_zero (by simpa using ht.2)
  · exact integrable_exponentialDensity.intervalIntegrable

/-- The first positive packet is an interval density convolved with a causal exponential. -/
theorem threshold_single_convolution {a : ℝ} (ha : 0 < a) :
    smoothed [a] 0 =
      convolution (intervalDensity a) exponentialDensity
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext t
  rw [intervalDensity_convolution ha.le, integral_exponentialDensity_eq_hinge_sub]
  rfl

/-- Exact convolution structure gives integrability and the product-of-shifts mass. -/
theorem threshold_integrable_mass {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) :
    Integrable (smoothed A (A.length-1)) ∧
      (∫ t, smoothed A (A.length-1) t) = shiftMass A := by
  induction A with
  | nil => exact (hne rfl).elim
  | cons a A ih =>
      have ha : 0 < a := hA a (by simp)
      have hA' : ∀ b ∈ A, 0 < b := fun b hb => hA b (by simp [hb])
      rcases eq_or_ne A [] with rfl | hne'
      · have he : smoothed [a] ([a].length-1) =
            convolution (intervalDensity a) exponentialDensity
              (ContinuousLinearMap.lsmul ℝ ℝ) volume := threshold_single_convolution ha
        rw [he]
        constructor
        · exact (integrable_intervalDensity a).integrable_convolution
            (ContinuousLinearMap.lsmul ℝ ℝ) integrable_exponentialDensity
        · rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
            (integrable_intervalDensity a) integrable_exponentialDensity,
            integral_intervalDensity ha.le, integral_exponentialDensity]
          simp [shiftMass]
      · have ih' := ih hA' hne'
        have hlen : (a::A).length-1 = (A.length-1)+1 := by
          have := List.length_pos_iff_ne_nil.mpr hne'
          simp only [List.length_cons]
          omega
        have he : smoothed (a::A) ((a::A).length-1) =
            convolution (intervalDensity a) (smoothed A (A.length-1))
              (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
          funext t
          rw [hlen, smoothed_cons_succ (fun b hb => (hA' b hb).le) ha.le,
            intervalDensity_convolution ha.le]
        rw [he]
        constructor
        · exact (integrable_intervalDensity a).integrable_convolution
            (ContinuousLinearMap.lsmul ℝ ℝ) ih'.1
        · rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
            (integrable_intervalDensity a) ih'.1, integral_intervalDensity ha.le, ih'.2]
          rfl

theorem integrable_normalizedThreshold {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) : Integrable (normalizedThreshold A) :=
  (threshold_integrable_mass hA hne).1.div_const (shiftMass A)

/-- The normalized threshold packet is a probability density. -/
theorem integral_normalizedThreshold {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) : (∫ t, normalizedThreshold A t) = 1 := by
  simp only [normalizedThreshold, integral_div, (threshold_integrable_mass hA hne).2]
  exact div_self (shiftMass_pos hA).ne'

/-- Quantitative lower-tail mass bound, with no loss from integrating the exponential envelope. -/
theorem normalizedThreshold_lower_mass_bound {A : List ℝ} {c : ℝ}
    (hc : 0 < c) (hA : ∀ a ∈ A, c ≤ a) (hne : A ≠ []) (T : ℝ) :
    (∫ t in Iic T, normalizedThreshold A t) ≤
      (1/2:ℝ)^A.length * Real.exp ((2/c)*T) := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => hc.trans_le (hA a ha)
  have hrate : 0 < 2/c := by positivity
  have hE := integrableOn_exp_mul_Iic hrate T
  calc
    _ ≤ ∫ t in Iic T, ((2/c) * (1/2:ℝ)^A.length) * Real.exp ((2/c)*t) :=
      integral_mono (integrable_normalizedThreshold hpos hne).integrableOn
        (hE.const_mul _) (normalizedThreshold_geometric_bound hc hA hne)
    _ = ((2/c) * (1/2:ℝ)^A.length) * (Real.exp ((2/c)*T) / (2/c)) := by
      rw [integral_const_mul, integral_exp_mul_Iic hrate]
    _ = _ := by field_simp

theorem normalizedThreshold_upper_mass_eq {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) (T : ℝ) :
    (∫ t in Ioi T, normalizedThreshold A t) =
      1 - ∫ t in Iic T, normalizedThreshold A t := by
  have h := integral_add_compl (s := Iic T) measurableSet_Iic
    (integrable_normalizedThreshold hA hne)
  rw [compl_Iic, integral_normalizedThreshold hA hne] at h
  linarith

/-- Almost all probability mass lies above every fixed logarithmic cutoff for large packets. -/
theorem normalizedThreshold_upper_mass_bound {A : List ℝ} {c : ℝ}
    (hc : 0 < c) (hA : ∀ a ∈ A, c ≤ a) (hne : A ≠ []) (T : ℝ) :
    1 - (1/2:ℝ)^A.length * Real.exp ((2/c)*T) ≤
      (∫ t in Ioi T, normalizedThreshold A t) ∧
      (∫ t in Ioi T, normalizedThreshold A t) ≤ 1 := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => hc.trans_le (hA a ha)
  rw [normalizedThreshold_upper_mass_eq hpos hne T]
  have hlo : 0 ≤ ∫ t in Iic T, normalizedThreshold A t :=
    integral_nonneg (normalizedThreshold_nonneg hpos hne)
  have hhi := normalizedThreshold_lower_mass_bound hc hA hne T
  constructor <;> linarith

/-- The normalized probability mass escapes every fixed upper scale. -/
theorem tendsto_normalizedThreshold_upper_mass {ι : Type*} {l : Filter ι}
    {A : ι → List ℝ} {c : ℝ} (hc : 0 < c)
    (hA : ∀ i, ∀ a ∈ A i, c ≤ a)
    (hlen : Tendsto (fun i => (A i).length) l atTop) (T : ℝ) :
    Tendsto (fun i => ∫ t in Ioi T, normalizedThreshold (A i) t) l (𝓝 1) := by
  have he : ∀ᶠ i in l, A i ≠ [] := by
    filter_upwards [hlen.eventually (eventually_ge_atTop 1)] with i hi
    intro h
    simp [h] at hi
  have hb : Tendsto (fun i => (1/2:ℝ)^(A i).length * Real.exp ((2/c)*T)) l (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).comp hlen
    simpa using hh.mul_const (Real.exp ((2/c)*T))
  have hlo : ∀ᶠ i in l, 0 ≤ ∫ t in Iic T, normalizedThreshold (A i) t := by
    filter_upwards [he] with i hi
    exact integral_nonneg
      (normalizedThreshold_nonneg (fun a ha => hc.trans_le (hA i a ha)) hi)
  have hhi : ∀ᶠ i in l, (∫ t in Iic T, normalizedThreshold (A i) t) ≤
      (1/2:ℝ)^(A i).length * Real.exp ((2/c)*T) := by
    filter_upwards [he] with i hi
    exact normalizedThreshold_lower_mass_bound hc (hA i) hi T
  have hz := squeeze_zero' hlo hhi hb
  have heq : (fun i => ∫ t in Ioi T, normalizedThreshold (A i) t) =ᶠ[l]
      (fun i => 1 - ∫ t in Iic T, normalizedThreshold (A i) t) := by
    filter_upwards [he] with i hi
    exact normalizedThreshold_upper_mass_eq (fun a ha => hc.trans_le (hA i a ha)) hi T
  apply (tendsto_congr' heq).2
  simpa using tendsto_const_nhds.sub hz

end RHTower.MobiusRieszSmoothing
