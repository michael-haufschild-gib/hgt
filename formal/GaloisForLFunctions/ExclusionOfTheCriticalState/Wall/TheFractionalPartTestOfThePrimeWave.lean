import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.TheFractionalPartAverageOfTheMangoldtMeasure
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.TheLogarithmicFloorKernelOnTheCriticalStrip
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LogarithmicTranslationsAgainstACausalKernel
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.MoebiusInversionOfTheIntegerQuadrature

/-!
# The fractional-part test of the polar-subtracted Mangoldt wave

Truncating at a common physical time converts each translated test to a
finite sum of fractional parts. The cutoff in the arithmetic sum depends
on the integration variable, while the cutoff in the time integral is fixed.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Positive fractional-part test on the logarithmic axis. -/
def fractionalPrimeTest (v : ℝ) : ℝ := Real.exp (-v/2)*Int.fract (Real.exp v)

private theorem measurable_fractionalPrimeTest : Measurable fractionalPrimeTest :=
  (by fun_prop : Measurable fun v : ℝ => Real.exp (-v/2)).mul
    (measurable_fract.comp Real.measurable_exp)

private theorem abs_fractionalPrimeTest_le_one (v : ℝ) : |fractionalPrimeTest v| ≤ 1 := by
  have h := abs_weightedFloorDiscrepancy_le_one (σ := 1/2) (by norm_num) (by norm_num) v
  simpa only [fractionalPrimeTest,weightedFloorDiscrepancy,
    show -(1/2:ℝ)*v = -v/2 by ring, neg_mul, abs_neg] using h

private def truncatedTest (h v : ℝ) : ℂ := if 0 ≤ v then (fractionalPrimeTest (h+v):ℂ) else 0

private theorem mangoldt_summable_at_cut :
    Summable fun n : ℕ => |vonMangoldt n/Real.sqrt n|/(n:ℝ)^2 := by
  apply Summable.of_nonneg_of_le (fun _ => div_nonneg (abs_nonneg _) (sq_nonneg _)) _
    GaloisForLFunctions.summable_log_nat_div_sq
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hroot : 1 ≤ Real.sqrt n := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  rw [abs_div,abs_of_nonneg vonMangoldt_nonneg,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right ((div_le_self vonMangoldt_nonneg hroot).trans vonMangoldt_le_log)
    (sq_nonneg _)

private theorem fractional_prime_prefix (q h : ℝ) :
    (∑' n : ℕ, ((vonMangoldt n/Real.sqrt n:ℝ):ℂ)*truncatedTest h (q-Real.log n)) =
      ((Real.exp (-(h+q)/2)*(∑ n ∈ Finset.Icc 0 ⌊Real.exp q⌋₊,
        vonMangoldt n*Int.fract (Real.exp (h+q)/n)):ℝ):ℂ) := by
  let S := Finset.Icc 0 ⌊Real.exp q⌋₊
  rw [tsum_eq_sum (s := S) (fun n hn => ?_)]
  · rw [Finset.mul_sum,Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp
    have hp0 : (0:ℝ) < n := by exact_mod_cast hp
    have hle : (n:ℝ) ≤ Real.exp q := (Nat.le_floor_iff (Real.exp_pos q).le).mp (Finset.mem_Icc.mp hn).2
    have hlog := (Real.log_le_iff_le_exp hp0).2 hle
    rw [truncatedTest,if_pos (sub_nonneg.2 hlog),← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    have hs : Real.sqrt n = Real.exp (Real.log n/2) := by rw [Real.exp_half,Real.exp_log hp0]
    rw [fractionalPrimeTest,show h+(q-Real.log n)=h+q-Real.log n by ring,
      Real.exp_sub,Real.exp_log hp0,hs,
      show -(h+q-Real.log n)/2 = -(h+q)/2+Real.log n/2 by ring,Real.exp_add]
    field_simp [(Real.exp_pos (Real.log n/2)).ne']
    <;> ring
  · have hfar : ⌊Real.exp q⌋₊ < n := lt_of_not_ge fun hle =>
      hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hle⟩)
    have hp : 0 < n := (Nat.zero_le _).trans_lt hfar
    have hx : Real.exp q < (n:ℝ) := (Nat.floor_lt (Real.exp_pos q).le).mp hfar
    rw [truncatedTest,if_neg (not_le_of_gt (sub_neg.mpr
      ((Real.lt_log_iff_exp_lt (by exact_mod_cast hp)).mpr hx))),mul_zero]

/-- The cutoff on physical time moves to the arithmetic cutoff
`exp (M-u)` after interchanging the integer row with the profile. -/
theorem integral_mangoldt_fractional_cut {Φ : ℝ → ℝ} (hm : Measurable Φ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (M T : ℝ) :
    (∫ t in Set.Iic M, (logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ t : ℂ)*
      (fractionalPrimeTest (T-t):ℂ)) =
      ∫ u, (Φ u : ℂ)*((Real.exp ((u-T)/2)*(∑ n ∈ Finset.Icc 0 ⌊Real.exp (M-u)⌋₊,
        vonMangoldt n*Int.fract (Real.exp (T-u)/n)):ℝ):ℂ) := by
  let K := truncatedTest (T-M)
  have hmK : Measurable K := Measurable.ite (measurableSet_le measurable_const measurable_id)
    (Complex.continuous_ofReal.measurable.comp (measurable_fractionalPrimeTest.comp (by fun_prop))) measurable_const
  have hpre := integral_logShiftWave_mul_causal (b := fun n : ℕ => vonMangoldt n/Real.sqrt n)
    (by simp) mangoldt_summable_at_cut hm hC hc hmK (fun v hv => if_neg (not_le_of_gt hv))
    (B := 1) (fun v => by
      by_cases hv : 0 ≤ v
      · simpa only [K,truncatedTest,if_pos hv,Complex.norm_real,Real.norm_eq_abs] using abs_fractionalPrimeTest_le_one (T-M+v)
      · simp [K,truncatedTest,hv]) M
  rw [← integral_indicator measurableSet_Iic]
  calc _ = ∫ t, (logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ t : ℂ)*K (M-t) := by
           apply integral_congr_ae (Eventually.of_forall fun t => ?_)
           by_cases ht : t ≤ M
           · rw [Set.indicator_of_mem ht,K,truncatedTest,if_pos (sub_nonneg.mpr ht)]
             rw [show T-M+(M-t)=T-t by ring]
           · rw [Set.indicator_of_notMem ht,K,truncatedTest,if_neg (not_le.mpr (sub_neg.mpr (lt_of_not_ge ht))),mul_zero]
    _ = _ := hpre.2.2.trans (integral_congr_ae (Eventually.of_forall fun u => by
      rw [show (∑' n : ℕ, ((vonMangoldt n/Real.sqrt n:ℝ):ℂ)*K (M-u-Real.log n)) = _ from
        fractional_prime_prefix (M-u) (T-M),show T-M+(M-u)=T-u by ring,show -(T-u)/2=(u-T)/2 by ring]))

private theorem density_tail_at_nonpos {a : ℝ} (ha : a ≤ 0) :
    (∫ v in Set.Ici a, Real.exp (-v)*Int.fract (Real.exp v)) = -a+(1-Real.eulerMascheroniConstant) := by
  let f := fun v : ℝ => Real.exp (-v)*Int.fract (Real.exp v)
  have hneg : Set.EqOn f (fun _ => 1) (Set.Ico a 0) := fun v hv => by
    dsimp only [f]
    rw [Int.fract_eq_self.mpr ⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr hv.2⟩,
      ← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc a 0) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
  have hi₀ := (hc.mono_set Set.Ico_subset_Icc_self).congr_fun hneg.symm measurableSet_Ico
  have hm : Measurable f := (by fun_prop : Measurable fun v : ℝ => Real.exp (-v)).mul
    (measurable_fract.comp Real.measurable_exp)
  have hi₁ : IntegrableOn f (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h := integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) 0
    simp only [neg_one_mul] at h
    apply h.mono' hm.aestronglyMeasurable.restrict (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs,f,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le
  have hd : Disjoint (Set.Ico a 0) (Set.Ici 0) := Set.disjoint_left.2 fun _ h h' => (not_lt_of_ge h') h.2
  change (∫ v in Set.Ici a, f v) = _
  rw [← Set.Ico_union_Ici_eq_Ici ha,setIntegral_union hd measurableSet_Ici hi₀ hi₁,
    setIntegral_congr_fun measurableSet_Ico hneg,integral_Ici_eq_integral_Ioi]
  change (∫ _ in Set.Ico a 0, (1:ℝ)) + _ = _
  rw [fractional_density_integral,setIntegral_const,Real.volume_real_Ico_of_le ha,smul_eq_mul,mul_one,zero_sub]

/-- With a common physical cutoff the integral of the polar density is
affine in the cutoff. Its constant term is supplied by the harmonic sum. -/
theorem integral_polar_fractional_cut {M T : ℝ} (h : T ≤ M) :
    (∫ t in Set.Iic M, Real.exp (t/2)*fractionalPrimeTest (T-t)) =
      Real.exp (T/2)*(M-T+1-Real.eulerMascheroniConstant) := by
  let a := T-M
  let f := fun v : ℝ => Real.exp (-v)*Int.fract (Real.exp v)
  let w := (Set.Ici a).indicator f
  have he : (∫ t in Set.Iic M, Real.exp (t/2)*fractionalPrimeTest (T-t)) =
      Real.exp (T/2)*∫ v in Set.Ici a, f v := by
    rw [← integral_indicator measurableSet_Iic,← integral_indicator measurableSet_Ici,
      ← integral_sub_left_eq_self w volume T,← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ≤ M
    · have hv : T-t ∈ Set.Ici a := sub_le_sub_left ht T
      rw [Set.indicator_of_mem ht,w,Set.indicator_of_mem hv]
      dsimp only [fractionalPrimeTest,f]
      rw [← mul_assoc,← mul_assoc,← Real.exp_add,← Real.exp_add]
      congr 2 <;> ring
    · have hv : T-t ∉ Set.Ici a := not_le.mpr (sub_lt_sub_left (lt_of_not_ge ht) T)
      rw [Set.indicator_of_notMem ht,w,Set.indicator_of_notMem hv,mul_zero]
  rw [he,show (∫ v in Set.Ici a, f v) = _ from density_tail_at_nonpos (sub_nonpos.mpr h)]
  dsimp only [a]; ring

open ArithmeticOfSquareRootPrecision

/-- The limiting arithmetic term after removal of the continuum density. -/
def stirlingTestResponse (Φ : ℝ → ℝ) (T : ℝ) :=
  ∫ u in Set.Iic (0:ℝ), Φ u*Real.exp ((u-T)/2)*
    (stirlingMain (Real.exp (T-u))-Real.log ((⌊Real.exp (T-u)⌋₊).factorial : ℕ))

/-- The factorial remainder contributes exponentially little at every
positive center, even when the confined profile changes sign. -/
theorem abs_stirlingTestResponse_le {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {T : ℝ} (hT : 0 ≤ T) :
    |stirlingTestResponse Φ T| ≤ C*(1+T)*Real.exp (-T/2) := by
  let D := C*(1+T)*Real.exp (-T/2)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC (by linarith only [hT])) (Real.exp_pos _).le
  have hi := (integrableOn_exp_Iic (0:ℝ)).const_mul D
  simp only [stirlingTestResponse,← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hi ?_).trans_eq (by rw [integral_const_mul,integral_exp_Iic_zero,mul_one])
  rw [ae_restrict_iff' measurableSet_Iic]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : u ≤ 0 := hu
  have hx : 1 ≤ Real.exp (T-u) := Real.one_le_exp ((sub_nonneg.mpr (hu0.trans hT)))
  have hsmall := (tendsto_fractionalMangoldtError hx).2
  rw [Real.log_exp] at hsmall
  have hfactor : 1+(T-u) ≤ (1+T)*Real.exp (-u) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-u)) (by linarith only [hT] : 0 ≤ 1+T)
    nlinarith only [h,mul_nonpos_of_nonneg_of_nonpos hT hu0]
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc _ ≤ (C*Real.exp (2*u))*Real.exp ((u-T)/2)*((1+T)*Real.exp (-u)) :=
           mul_le_mul (mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le)
             (hsmall.trans hfactor) (abs_nonneg _) (by positivity)
    _ = D*Real.exp (3*u/2) := by
           dsimp only [D]
           rw [show (C*Real.exp (2*u))*Real.exp ((u-T)/2)*((1+T)*Real.exp (-u)) =
             C*(1+T)*(Real.exp (2*u)*Real.exp ((u-T)/2)*Real.exp (-u)) by ring,
             show C*(1+T)*Real.exp (-T/2)*Real.exp (3*u/2) =
               C*(1+T)*(Real.exp (-T/2)*Real.exp (3*u/2)) by ring,
             ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
           congr 2 <;> ring
    _ ≤ D*Real.exp u := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hu0])) hD

#print axioms abs_stirlingTestResponse_le
#print axioms integral_mangoldt_fractional_cut
end GaloisForLFunctions.ExclusionOfTheCriticalState
