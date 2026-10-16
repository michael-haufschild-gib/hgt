import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationMellin
import GaloisForLFunctions.RHTower.CompactCarrierPolynomialDetection
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Literal complete source on a compact clock interval

The continuous profile keeps every cutoff in a fixed logarithmic interval.
Its Banach-valued Laplace transform factors exactly into the complete Abel
source transform and the compact exponential test. Complexification of a
real functional preserves the literal pairing. Its Fourier--Borel transform
is entire of finite exponential type and detects every nonzero functional.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped NNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower

abbrev CriticalClockWindow (a : ℝ≥0) := Icc (0 : ℝ) (a : ℝ)

def criticalClockProfile (a : ℝ≥0) (t : ℝ) : C(CriticalClockWindow a, ℝ) :=
  ⟨fun u => criticalAbelLogProfile (t - u),
    continuous_criticalAbelLogProfile.comp (continuous_const.sub continuous_subtype_val)⟩

def criticalClockProfileC (a : ℝ≥0) (t : ℝ) : C(CriticalClockWindow a, ℂ) :=
  Complex.ofRealCLM.compLeftContinuous ℝ _ (criticalClockProfile a t)

def criticalClockCoordinate (a : ℝ≥0) : C(CriticalClockWindow a, ℂ) :=
  ⟨fun u => (u : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

def criticalClockDualComplex (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) : C(CriticalClockWindow a, ℂ) →L[ℂ] ℂ :=
  StrongDual.extendRCLike (L.comp (Complex.reCLM.compLeftContinuous ℝ _))

lemma criticalClockDualComplex_ofReal (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (f : C(CriticalClockWindow a, ℝ)) :
    criticalClockDualComplex a L (Complex.ofRealCLM.compLeftContinuous ℝ _ f) = (L f : ℂ) := by
  rw [criticalClockDualComplex, StrongDual.extendRCLike_apply]
  have hreal : (Complex.reCLM.compLeftContinuous ℝ (CriticalClockWindow a))
      (Complex.ofRealCLM.compLeftContinuous ℝ _ f) = f := by ext u; rfl
  have him : (Complex.reCLM.compLeftContinuous ℝ (CriticalClockWindow a))
      (Complex.I • (Complex.ofRealCLM.compLeftContinuous ℝ _ f)) = 0 := by
    ext u
    simp [ContinuousLinearMap.compLeftContinuous, Complex.mul_re]
  simp only [ContinuousLinearMap.comp_apply, RCLike.I_to_complex, hreal, him,
    map_zero, mul_zero, sub_zero]
  rfl

lemma continuous_criticalClockProfile (a : ℝ≥0) : Continuous (criticalClockProfile a) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_criticalAbelLogProfile.comp
    (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))

lemma continuous_criticalClockProfileC (a : ℝ≥0) : Continuous (criticalClockProfileC a) :=
  (Complex.ofRealCLM.compLeftContinuous ℝ (CriticalClockWindow a)).continuous.comp
    (continuous_criticalClockProfile a)

lemma norm_criticalClockProfileC_le (a : ℝ≥0) (t : ℝ) :
    ‖criticalClockProfileC a t‖ ≤ ∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u| := by
  apply (ContinuousMap.norm_le _ (integral_nonneg (fun _ => abs_nonneg _))).mpr
  intro u
  change ‖(criticalAbelLogProfile (t - u) : ℂ)‖ ≤ _
  simpa only [Complex.norm_real, Real.norm_eq_abs]
    using criticalAbelLogProfile_uniform_bound (t - u)

lemma integrable_criticalClockProfileC_ray (a : ℝ≥0) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => expRay s t • criticalClockProfileC a t) (Ioi 0) := by
  let B : ℝ := ∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u|
  have hB : 0 ≤ B := integral_nonneg (fun _ => abs_nonneg _)
  have hi := (integrableOn_exp_mul_Ioi (a := -s.re) (by linarith) 0).mul_const B
  apply hi.mono' ((show Continuous (fun t : ℝ => expRay s t • criticalClockProfileC a t) from
    (by have hc := continuous_criticalClockProfileC a; unfold expRay; fun_prop)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, norm_expRay]
  simpa only [B, neg_mul] using
    mul_le_mul_of_nonneg_left (norm_criticalClockProfileC_le a t) (Real.exp_pos (-(s.re * t))).le

lemma criticalClockProfileC_zero_of_nonpos (a : ℝ≥0) {t : ℝ} (ht : t ≤ 0) :
    criticalClockProfileC a t = 0 := by
  ext u
  change (criticalAbelLogProfile (t - u) : ℂ) = 0
  rw [criticalAbelLogProfile_zero_of_nonpos (by linarith [u.property.1])]
  rfl
lemma criticalAbelProfile_delay_laplace (u : ℝ) (hu : 0 ≤ u) (s : ℂ) :
    (∫ t in Ioi (0 : ℝ), expRay s t * (criticalAbelLogProfile (t - u) : ℂ)) =
      expRay s u * criticalAbelProfileLaplace s := by
  have hwhole (v : ℝ) (hv : 0 ≤ v) :
      (∫ t in Ioi (0 : ℝ), expRay s t * (criticalAbelLogProfile (t - v) : ℂ)) =
        ∫ t : ℝ, expRay s t * (criticalAbelLogProfile (t - v) : ℂ) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases ht : 0 < t
    · simp [ht]
    · have hz := criticalAbelLogProfile_zero_of_nonpos (t := t - v) (by linarith)
      simp [ht, hz]
  have hbase : criticalAbelProfileLaplace s =
      ∫ t : ℝ, expRay s t * (criticalAbelLogProfile t : ℂ) := by
    simpa only [criticalAbelProfileLaplace, bochnerLaplaceRay, smul_eq_mul, sub_zero]
      using hwhole 0 le_rfl
  rw [hwhole u hu, hbase, ← integral_const_mul]
  rw [← integral_add_right_eq_self
    (fun t : ℝ => expRay s t * (criticalAbelLogProfile (t - u) : ℂ)) u]
  apply integral_congr_ae
  filter_upwards with t
  rw [add_sub_cancel_right]
  have he : expRay s (t + u) = expRay s u * expRay s t := by
    unfold expRay
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, mul_assoc]

lemma integral_criticalClockProfileC (a : ℝ≥0) {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0 : ℝ), expRay s t • criticalClockProfileC a t) =
      criticalAbelProfileLaplace s • compactExponentialTest (criticalClockCoordinate a) s := by
  ext u
  rw [ContinuousMap.integral_apply (integrable_criticalClockProfileC_ray a hs)]
  change (∫ t in Ioi (0 : ℝ), expRay s t * (criticalAbelLogProfile (t - u) : ℂ)) = _
  rw [criticalAbelProfile_delay_laplace u u.property.1]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, compactExponentialTest_apply,
    criticalClockCoordinate, ContinuousMap.coe_mk, expRay]
  ring

lemma integral_criticalClockDual (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0 : ℝ), expRay s t * (L (criticalClockProfile a t) : ℂ)) =
      criticalAbelProfileLaplace s *
        compactFourierBorel (criticalClockDualComplex a L) (criticalClockCoordinate a) s := by
  have hp (t : ℝ) : expRay s t * (L (criticalClockProfile a t) : ℂ) =
      criticalClockDualComplex a L (expRay s t • criticalClockProfileC a t) := by
    rw [map_smul]
    change _ = expRay s t * criticalClockDualComplex a L
      (Complex.ofRealCLM.compLeftContinuous ℝ _ (criticalClockProfile a t))
    rw [criticalClockDualComplex_ofReal]
  simp_rw [hp]
  rw [(criticalClockDualComplex a L).integral_comp_comm
    (integrable_criticalClockProfileC_ray a hs), integral_criticalClockProfileC a hs, map_smul]
  rfl

def criticalClockFourierBorel (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) : ℂ → ℂ :=
  compactFourierBorel (criticalClockDualComplex a L) (criticalClockCoordinate a)

lemma differentiable_criticalClockFourierBorel (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) :
    Differentiable ℂ (criticalClockFourierBorel a L) := by
  intro z
  exact (compactFourierBorel_analyticOnNhd _ _ z (mem_univ z)).differentiableAt

lemma norm_criticalClockFourierBorel_le (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (s : ℂ) :
    ‖criticalClockFourierBorel a L s‖ ≤
      ‖criticalClockDualComplex a L‖ * Real.exp ((a : ℝ) * ‖s‖) := by
  have hb (u : CriticalClockWindow a) : -(a : ℝ) * ‖s‖ ≤
      (s * criticalClockCoordinate a u).re := by
    change -(a : ℝ) * ‖s‖ ≤ (s * ((u : ℝ) : ℂ)).re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hr := (neg_le_abs s.re).trans (Complex.abs_re_le_norm s)
    have hn := norm_nonneg s
    nlinarith [u.property.1, u.property.2,
      mul_nonneg u.property.1 (show 0 ≤ s.re + ‖s‖ by linarith)]
  have h := norm_compactFourierBorel_le (criticalClockDualComplex a L)
    (criticalClockCoordinate a) s (-(a : ℝ)) hb
  simpa only [criticalClockFourierBorel, neg_mul, neg_neg] using h

lemma criticalClockDual_eq_zero_of_fourierBorel_zero (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ)
    (hF : criticalClockFourierBorel a L = 0) : L = 0 := by
  let r : C(CriticalClockWindow a, ℝ) := ⟨fun u => u, continuous_subtype_val⟩
  have hpow (n : ℕ) : L (r ^ n) = 0 := by
    have h := map_coordinate_pow_eq_zero_of_fourierBorel_zero
      (criticalClockDualComplex a L) (criticalClockCoordinate a)
      (fun z => congrFun hF z) n
    have he : criticalClockCoordinate a ^ n =
        Complex.ofRealCLM.compLeftContinuous ℝ _ (r ^ n) := by
      ext u
      simp [criticalClockCoordinate, r, ContinuousLinearMap.compLeftContinuous,
        Complex.ofReal_pow]
    rw [he, criticalClockDualComplex_ofReal] at h
    exact Complex.ofReal_eq_zero.mp h
  have hpoly (p : Polynomial ℝ) : L (p.toContinuousMapOn (CriticalClockWindow a)) = 0 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have he : (p + q).toContinuousMapOn (CriticalClockWindow a) =
          p.toContinuousMapOn (CriticalClockWindow a) +
            q.toContinuousMapOn (CriticalClockWindow a) := by ext u; simp
      rw [he, map_add, hp, hq, add_zero]
    | monomial n c =>
      have he : (Polynomial.monomial n c).toContinuousMapOn (CriticalClockWindow a) =
          c • r ^ n := by ext u; simp [r]
      rw [he, map_smul, hpow, smul_zero]
  have hsub : (polynomialFunctions (CriticalClockWindow a) :
      Set C(CriticalClockWindow a, ℝ)) ⊆ (L.toLinearMap.ker : Set C(CriticalClockWindow a, ℝ)) := by
    rw [polynomialFunctions_coe]
    rintro f ⟨p, rfl⟩
    exact hpoly p
  have hd : closure (polynomialFunctions (CriticalClockWindow a) :
      Set C(CriticalClockWindow a, ℝ)) = univ := by
    rw [← Subalgebra.topologicalClosure_coe, polynomialFunctions.topologicalClosure]
    rfl
  have hall := closure_minimal hsub L.isClosed_ker
  rw [hd] at hall
  ext f
  exact hall (mem_univ f)

lemma criticalClockFourierBorel_ne_zero (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    criticalClockFourierBorel a L ≠ 0 :=
  fun h => hL (criticalClockDual_eq_zero_of_fourierBorel_zero a L h)

lemma criticalClockFourierBorel_criticalLine_nonzero (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    (fun z : ℂ => criticalClockFourierBorel a L (-1 / 2 + z * I)) ≠ 0 := by
  intro h
  apply criticalClockFourierBorel_ne_zero a L hL
  ext s
  have he : (-1 / 2 : ℂ) + (-(s + 1 / 2) * I) * I = s := by
    rw [mul_assoc, I_mul_I]
    ring
  simpa only [he, Pi.zero_apply] using congrFun h (-(s + 1 / 2) * I)

lemma criticalClockFourierBorel_criticalLine_exponentialType (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ,
      ‖criticalClockFourierBorel a L (-1 / 2 + z * I)‖ ≤ C * Real.exp ((a : ℝ) * ‖z‖) := by
  let C : ℝ := max 1 (‖criticalClockDualComplex a L‖ * Real.exp a)
  refine ⟨C, le_max_left _ _, fun z => ?_⟩
  have hn : ‖(-1 / 2 : ℂ) + z * I‖ ≤ 1 + ‖z‖ := by
    calc
      _ ≤ ‖(-1 / 2 : ℂ)‖ + ‖z * I‖ := norm_add_le _ _
      _ ≤ 1 + ‖z‖ := by rw [norm_mul, norm_I, mul_one]; norm_num
  calc
    _ ≤ ‖criticalClockDualComplex a L‖ *
        Real.exp ((a : ℝ) * ‖(-1 / 2 : ℂ) + z * I‖) := norm_criticalClockFourierBorel_le _ _ _
    _ ≤ ‖criticalClockDualComplex a L‖ * Real.exp ((a : ℝ) * (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hn a.property))
        (norm_nonneg (criticalClockDualComplex a L))
    _ = (‖criticalClockDualComplex a L‖ * Real.exp a) * Real.exp ((a : ℝ) * ‖z‖) := by
      rw [mul_add, mul_one, Real.exp_add, mul_assoc]
    _ ≤ C * Real.exp ((a : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end RHTower
