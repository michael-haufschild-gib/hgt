import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceKernel
import Mathlib.NumberTheory.LSeries.Injectivity

/-! Complete original and reflected nonlocal currents on the same arithmetic source,
with their exact signed forcing and nonzero leading coefficient. -/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaMobiusSameSourceAtom_measurable (z : ℂ) (n : ℕ) :
    Measurable (pwGammaMobiusSameSourceAtom z n) := by
  unfold pwGammaMobiusSameSourceAtom pwGammaWeightedTranslation pwGammaMobiusReflectedAtom
    pwGammaRayInverseReflection pwGammaMobiusGlobalAtom pwGammaRaySource GaloisForLFunctions.expShift
  fun_prop

private theorem pwGammaSameSource_reciprocal_summable :
    Summable (fun n : ℕ => 1/((n : ℝ)+1)^2) := by
  have ht := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
  change Summable (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)^2) at ht
  simpa only [Nat.cast_add, Nat.cast_one] using ht

theorem pwGammaMobiusSameSourceAtom_integrable (z : ℂ) (n : ℕ) :
    Integrable (pwGammaMobiusSameSourceAtom z n)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  rcases n with _ | n
  · rw [pwGammaMobiusSameSourceAtom_zero]; exact integrable_zero _ _ _
  rcases n with _ | n
  · apply (integrable_zero _ _ _).congr
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact (pwGammaMobiusSameSourceAtom_one z hp.1.le hp.2).symm
  have hg := (pwGammaSameSourceMajorant_integrable (N+3)).const_mul
    ((2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(1/((n : ℝ)+1)^2))
  apply Integrable.mono' hg (pwGammaMobiusSameSourceAtom_measurable z (n+2)).aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact pwGammaMobiusSameSourceAtom_norm_le hN n hp.1 hp.2

theorem pwGammaMobiusSameSourceAtom_integrable_section (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun h : ℝ => pwGammaMobiusSameSourceAtom z n (h,x)) (Ioi 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  rcases n with _ | n
  · simp only [pwGammaMobiusSameSourceAtom_zero, Pi.zero_apply]
    exact integrable_zero _ _ _
  rcases n with _ | n
  · apply IntegrableOn.congr_fun (integrable_zero _ _ _) _ measurableSet_Ioi
    intro h hh
    exact (pwGammaMobiusSameSourceAtom_one z hh.le hx).symm
  have hg := (pwGammaSameSourceMajorant_integrable_section (N+3) x).const_mul
    ((2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(1/((n : ℝ)+1)^2))
  have hm : Measurable (fun h : ℝ => pwGammaMobiusSameSourceAtom z (n+2) (h,x)) :=
    (pwGammaMobiusSameSourceAtom_measurable z (n+2)).comp (measurable_id.prodMk measurable_const)
  apply Integrable.mono' hg hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact pwGammaMobiusSameSourceAtom_norm_le hN n hh hx

theorem pwGammaMobiusSameSourceAtom_norm_integrals_summable (z : ℂ) :
    Summable (fun n : ℕ => ∫ p, ‖pwGammaMobiusSameSourceAtom z n p‖
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  have hs := pwGammaSameSource_reciprocal_summable.mul_left
    ((2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(∫ p, pwGammaSameSourceMajorant (N+3) p
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))))
  apply (summable_nat_add_iff 2).mp
  refine hs.of_nonneg_of_le (fun n => integral_nonneg (fun p => norm_nonneg _)) ?_
  intro n
  calc
    _ ≤ ∫ p, (2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(1/((n : ℝ)+1)^2)*
        pwGammaSameSourceMajorant (N+3) p
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      apply integral_mono_ae (pwGammaMobiusSameSourceAtom_integrable z (n+2)).norm
        ((pwGammaSameSourceMajorant_integrable (N+3)).const_mul _)
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
      exact pwGammaMobiusSameSourceAtom_norm_le hN n hp.1 hp.2
    _ = _ := by rw [integral_const_mul]; ring

theorem pwGammaMobiusSameSourceAtom_section_norm_integrals_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ h in Ioi (0 : ℝ), ‖pwGammaMobiusSameSourceAtom z n (h,x)‖) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  have hs := pwGammaSameSource_reciprocal_summable.mul_left
    ((2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(∫ h in Ioi (0 : ℝ), pwGammaSameSourceMajorant (N+3) (h,x)))
  apply (summable_nat_add_iff 2).mp
  refine hs.of_nonneg_of_le (fun n => integral_nonneg (fun h => norm_nonneg _)) ?_
  intro n
  calc
    _ ≤ ∫ h in Ioi (0 : ℝ), (2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(1/((n : ℝ)+1)^2)*
        pwGammaSameSourceMajorant (N+3) (h,x) := by
      apply integral_mono_ae (pwGammaMobiusSameSourceAtom_integrable_section z (n+2) hx).norm
        ((pwGammaSameSourceMajorant_integrable_section (N+3) x).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact pwGammaMobiusSameSourceAtom_norm_le hN n hh hx
    _ = _ := by rw [integral_const_mul]; ring

/-- The original operator evaluated on the complete reflected arithmetic source. -/
def pwGammaMobiusSameSourceResponse (z : ℂ) (x h : ℝ) : ℂ :=
  (pwGammaWeightedTranslation h (pwGammaRayInverseReflection (pwGammaMobiusTilt z)) x-
    (Real.exp (-h) : ℂ)*pwGammaRayInverseReflection (pwGammaMobiusTilt z) x)/(h : ℂ)

private theorem pwGammaMobiusSameSourceTranslated_summable (z : ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    Summable (fun n => pwGammaWeightedTranslation h (pwGammaMobiusReflectedAtom z n) x) :=
  (pwGammaMobiusReflectedAtom_summable z (add_pos_of_pos_of_nonneg hx hh)).mul_left _

theorem pwGammaMobiusSameSourceAtom_summable (z : ℂ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    Summable (fun n => pwGammaMobiusSameSourceAtom z n (h,x)) := by
  have h0 := (pwGammaMobiusReflectedAtom_summable z hx).mul_left (Real.exp (-h) : ℂ)
  exact ((pwGammaMobiusSameSourceTranslated_summable z hh hx).sub h0).div_const (h : ℂ)

theorem pwGammaMobiusSameSourceResponse_eq_tsum (z : ℂ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaMobiusSameSourceResponse z x h = ∑' n, pwGammaMobiusSameSourceAtom z n (h,x) := by
  have h1 := pwGammaMobiusSameSourceTranslated_summable z hh hx
  have h0 := (pwGammaMobiusReflectedAtom_summable z hx).mul_left (Real.exp (-h) : ℂ)
  calc
    _ = ((∑' n, pwGammaWeightedTranslation h (pwGammaMobiusReflectedAtom z n) x)-
        (∑' n, (Real.exp (-h) : ℂ)*pwGammaMobiusReflectedAtom z n x))/(h : ℂ) := by
      simp only [pwGammaMobiusSameSourceResponse, pwGammaWeightedTranslation,
        pwGammaMobiusTilt_reflection_eq_tsum, tsum_mul_left]
    _ = _ := by
      rw [← h1.tsum_sub h0]
      simp only [pwGammaMobiusSameSourceAtom, div_eq_mul_inv, tsum_mul_right]

theorem pwGammaMobiusSameSourceResponse_integrable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (pwGammaMobiusSameSourceResponse z x) (Ioi 0) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun n => pwGammaMobiusSameSourceAtom_integrable_section z n hx)
    (pwGammaMobiusSameSourceAtom_section_norm_integrals_summable z hx)
  exact IntegrableOn.congr_fun hs (fun h hh => (pwGammaMobiusSameSourceResponse_eq_tsum z hh.le hx).symm)
    measurableSet_Ioi

theorem pwGammaMobiusSameSourceResponse_joint_integrable (z : ℂ) :
    Integrable (fun p : ℝ × ℝ => pwGammaMobiusSameSourceResponse z p.2 p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusSameSourceAtom_integrable z) (pwGammaMobiusSameSourceAtom_norm_integrals_summable z)
  apply Integrable.congr hs
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact (pwGammaMobiusSameSourceResponse_eq_tsum z hp.1.le hp.2).symm

theorem pwGammaMobiusSameSourceResponse_integral_interchange (z : ℂ) :
    (∫ h in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), pwGammaMobiusSameSourceResponse z x h) =
      ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceResponse z x h :=
  integral_integral_swap (pwGammaMobiusSameSourceResponse_joint_integrable z)

/-- Admitted original Frullani current of the reflected arithmetic source. -/
def pwGammaMobiusSameSourceCurrent (z : ℂ) (x : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceResponse z x h

theorem pwGammaMobiusSameSourceCurrent_integrable (z : ℂ) :
    IntegrableOn (pwGammaMobiusSameSourceCurrent z) (Ioi 0) :=
  (pwGammaMobiusSameSourceResponse_joint_integrable z).integral_prod_right

theorem pwGammaMobiusSameSourceCurrent_eq_tsum (z : ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusSameSourceCurrent z x =
      ∑' n : ℕ, ∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceAtom z n (h,x) := by
  rw [pwGammaMobiusSameSourceCurrent,
    setIntegral_congr_fun measurableSet_Ioi (fun h hh => pwGammaMobiusSameSourceResponse_eq_tsum z hh.le hx)]
  exact (integral_tsum_of_summable_integral_norm
    (fun n => pwGammaMobiusSameSourceAtom_integrable_section z n hx)
    (pwGammaMobiusSameSourceAtom_section_norm_integrals_summable z hx)).symm

/-- Full forcing difference; both operators act on the same reflected arithmetic input. -/
def pwGammaMobiusSameSourceDefect (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusSameSourceCurrent z x-pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x

theorem pwGammaMobiusSameSourceDefect_integrable (z : ℂ) :
    IntegrableOn (pwGammaMobiusSameSourceDefect z) (Ioi 0) :=
  (pwGammaMobiusSameSourceCurrent_integrable z).sub (pwGammaMobiusTiltCurrent_reflection_integrable z)

theorem pwGammaMobiusSameSourceDefect_response_joint_integrable (z : ℂ) :
    Integrable (fun p : ℝ × ℝ => pwGammaMobiusSameSourceResponse z p.2 p.1-
      pwGammaMobiusReflectedFrullaniResponse z p.2 p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
  (pwGammaMobiusSameSourceResponse_joint_integrable z).sub (pwGammaMobiusReflectedFrullaniResponse_joint_integrable z)

theorem pwGammaMobiusSameSourceDefect_response_integral (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceResponse z x h-
      pwGammaMobiusReflectedFrullaniResponse z x h) = pwGammaMobiusSameSourceDefect z x := by
  rw [integral_sub (pwGammaMobiusSameSourceResponse_integrable z hx)
    (pwGammaMobiusReflectedFrullaniResponse_integrable z hx), pwGammaMobiusReflectedFrullaniResponse_integral z hx]
  rfl

theorem pwGammaMobiusSameSourceAtom_defect_eq (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusSameSourceAtom z n (h,x))-
      pwGammaMobiusReflectedCurrentAtom z n x =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusSameSourceAtom_zero, pwGammaMobiusReflectedCurrentAtom,
      pwGammaMobiusReflectedAtom_zero, pwGammaSameSourceDefectWeight_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh => pwGammaMobiusSameSourceAtom_eq z hn hh.le hx)]
  simp only [integral_const_mul, integral_complex_ofReal]
  rw [pwGammaMobiusReflectedCurrentAtom, pwGammaMobiusReflectedAtom_eq z hn hx,
    pwGammaSameSourceDefectWeight, if_neg (Nat.ne_of_gt hn)]
  push_cast
  ring

private theorem pwGammaMobiusReflectedCurrentAtom_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n => pwGammaMobiusReflectedCurrentAtom z n x) := by
  have hs := (pwGammaMobiusTiltCurrent_summable z (inv_pos.mpr hx)).mul_left
    (pwGammaRaySource x/pwGammaRaySource x⁻¹)
  exact hs.congr (fun n => by
    dsimp [pwGammaMobiusReflectedCurrentAtom, pwGammaMobiusReflectedAtom,
      pwGammaRayInverseReflection, pwGammaMobiusGlobalCurrentAtom, pwGammaMobiusGlobalAtom]
    ring)

theorem pwGammaMobiusSameSourceDefect_weighted_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ =>
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ)) := by
  have hi := (hasSum_integral_of_summable_integral_norm
    (fun n => pwGammaMobiusSameSourceAtom_integrable_section z n hx)
    (pwGammaMobiusSameSourceAtom_section_norm_integrals_summable z hx)).summable
  exact (hi.sub (pwGammaMobiusReflectedCurrentAtom_summable z hx)).congr
    (fun n => pwGammaMobiusSameSourceAtom_defect_eq z n hx)

/-- Complete signed forcing, with no scalar-positive-to-arithmetic-positive inference. -/
theorem pwGammaMobiusSameSourceDefect_eq_tsum (z : ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusSameSourceDefect z x =
      ∑' n : ℕ, (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ) := by
  have hi := (hasSum_integral_of_summable_integral_norm
    (fun n => pwGammaMobiusSameSourceAtom_integrable_section z n hx)
    (pwGammaMobiusSameSourceAtom_section_norm_integrals_summable z hx)).summable
  rw [pwGammaMobiusSameSourceDefect, pwGammaMobiusSameSourceCurrent_eq_tsum z hx,
    pwGammaMobiusTiltCurrent_reflection_eq_tsum, ← hi.tsum_sub (pwGammaMobiusReflectedCurrentAtom_summable z hx)]
  exact tsum_congr (fun n => pwGammaMobiusSameSourceAtom_defect_eq z n hx)

/-- Closed domain and forcing classification for the same actual reflected arithmetic source. -/
theorem pwGammaMobiusSameSourceCurrent_closed :
    (∀ z : ℂ, IntegrableOn (pwGammaMobiusSameSourceCurrent z) (Ioi 0) ∧
      IntegrableOn (pwGammaMobiusSameSourceDefect z) (Ioi 0) ∧
      Integrable (fun p : ℝ × ℝ => pwGammaMobiusSameSourceResponse z p.2 p.1)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
      (∀ x : ℝ, 0 < x → IntegrableOn (pwGammaMobiusSameSourceResponse z x) (Ioi 0) ∧
        pwGammaMobiusSameSourceDefect z x =
          ∑' n : ℕ, (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
            pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ))) ∧
    (∀ n : ℕ, 1 < n → ∀ x : ℝ, 0 < x → 0 < pwGammaSameSourceDefectWeight n x) :=
  ⟨fun z => ⟨pwGammaMobiusSameSourceCurrent_integrable z, pwGammaMobiusSameSourceDefect_integrable z,
    pwGammaMobiusSameSourceResponse_joint_integrable z, fun _x hx =>
      ⟨pwGammaMobiusSameSourceResponse_integrable z hx, pwGammaMobiusSameSourceDefect_eq_tsum z hx⟩⟩,
    fun _n hn _x hx => pwGammaSameSourceDefectWeight_pos hn hx⟩

/-- The complete coefficient sequence of the same-source forcing. -/
def pwGammaSameSourceDefectCoefficient (x : ℝ) (n : ℕ) : ℂ :=
  (((moebius n : ℤ) : ℂ)*pwGammaRaySource x)*(pwGammaSameSourceDefectWeight n x : ℂ)

private theorem pwGammaSameSourceDefectCoefficient_zero (x : ℝ) :
    pwGammaSameSourceDefectCoefficient x 0 = 0 := by
  simp [pwGammaSameSourceDefectCoefficient, pwGammaSameSourceDefectWeight_zero]

private theorem pwGammaSameSourceDefectCoefficient_one (x : ℝ) :
    pwGammaSameSourceDefectCoefficient x 1 = 0 := by
  simp [pwGammaSameSourceDefectCoefficient, pwGammaSameSourceDefectWeight_one]

private theorem pwGammaSameSourceDefectCoefficient_term (z : ℂ) (x : ℝ) (n : ℕ) :
    LSeries.term (pwGammaSameSourceDefectCoefficient x) z n =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        pwGammaRaySource x*(pwGammaSameSourceDefectWeight n x : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaSameSourceDefectWeight_zero]
  rw [LSeries.term_def₀ (pwGammaSameSourceDefectCoefficient_zero x),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne' : (n : ℂ) ≠ 0),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ n)]
  rw [mul_comm (Real.log (n : ℝ) : ℂ) (-z)]
  dsimp [pwGammaSameSourceDefectCoefficient]
  ring

theorem pwGammaMobiusSameSourceDefect_eq_LSeries (z : ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusSameSourceDefect z x = LSeries (pwGammaSameSourceDefectCoefficient x) z := by
  rw [pwGammaMobiusSameSourceDefect_eq_tsum z hx, LSeries]
  exact tsum_congr (fun n => (pwGammaSameSourceDefectCoefficient_term z x n).symm)

theorem pwGammaSameSourceDefectCoefficient_LSeriesSummable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    LSeriesSummable (pwGammaSameSourceDefectCoefficient x) z := by
  change Summable (fun n => LSeries.term (pwGammaSameSourceDefectCoefficient x) z n)
  simp_rw [pwGammaSameSourceDefectCoefficient_term]
  exact pwGammaMobiusSameSourceDefect_weighted_summable z hx

/-- A nonzero actual leading coefficient survives in the complete forcing family. -/
theorem pwGammaMobiusSameSourceDefect_leading_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun r : ℝ => (2 : ℂ)^(r : ℂ)*pwGammaMobiusSameSourceDefect r x) atTop
      (𝓝 (-pwGammaRaySource x*(pwGammaSameSourceDefectWeight 2 x : ℂ))) := by
  have ha : LSeries.abscissaOfAbsConv (pwGammaSameSourceDefectCoefficient x) < ⊤ :=
    (pwGammaSameSourceDefectCoefficient_LSeriesSummable 0 hx).abscissaOfAbsConv_le.trans_lt
      (by simp)
  have hhead : ∀ m : ℕ, m ≤ 1 → pwGammaSameSourceDefectCoefficient x m = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact pwGammaSameSourceDefectCoefficient_zero x
    · have hm1 : m = 1 := by omega
      rw [hm1]
      exact pwGammaSameSourceDefectCoefficient_one x
  have ht := LSeries.tendsto_cpow_mul_atTop hhead ha
  simpa only [pwGammaMobiusSameSourceDefect_eq_LSeries _ hx, Nat.cast_one, one_add_one_eq_two,
    pwGammaSameSourceDefectCoefficient, moebius_apply_prime Nat.prime_two,
    Int.cast_neg, Int.cast_one, neg_one_mul] using ht

theorem pwGammaMobiusSameSourceDefect_eventually_ne_zero {x : ℝ} (hx : 0 < x) :
    ∀ᶠ r : ℝ in atTop, pwGammaMobiusSameSourceDefect r x ≠ 0 := by
  have hc : -pwGammaRaySource x*(pwGammaSameSourceDefectWeight 2 x : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (pwGammaRaySource_ne_zero x))
      (Complex.ofReal_ne_zero.mpr (pwGammaSameSourceDefectWeight_pos one_lt_two hx).ne')
  filter_upwards [(pwGammaMobiusSameSourceDefect_leading_limit hx).eventually_ne hc] with r hr
  exact fun hh => hr (by rw [hh, mul_zero])

theorem pwGammaMobiusSameSourceDefect_not_identically_zero {x : ℝ} (hx : 0 < x) :
    ¬ ∀ z : ℂ, pwGammaMobiusSameSourceDefect z x = 0 := by
  intro hz
  obtain ⟨r, hr⟩ := (pwGammaMobiusSameSourceDefect_eventually_ne_zero hx).exists
  exact hr (hz r)

end
end RHTower
