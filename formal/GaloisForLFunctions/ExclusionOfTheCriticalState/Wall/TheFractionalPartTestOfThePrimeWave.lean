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
    continuous_const.integrableOn_Icc
  have hi₀ : IntegrableOn f (Set.Ico a 0) :=
    (hc.mono_set Set.Ico_subset_Icc_self).congr_fun hneg.symm measurableSet_Ico
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

private def stirlingTestTerm (Φ : ℝ → ℝ) (T u : ℝ) :=
  Φ u*Real.exp ((u-T)/2)*(stirlingMain (Real.exp (T-u))-Real.log ((⌊Real.exp (T-u)⌋₊).factorial : ℕ))

/-- The limiting arithmetic term after removal of the continuum density. -/
def stirlingTestResponse (Φ : ℝ → ℝ) (T : ℝ) :=
  ∫ u in Set.Iic (0:ℝ), stirlingTestTerm Φ T u

private theorem stirling_term_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {T u : ℝ} (hT : 0 ≤ T) (hu0 : u ≤ 0) :
    ‖stirlingTestTerm Φ T u‖ ≤ (C*(1+T)*Real.exp (-T/2))*Real.exp u := by
  let D := C*(1+T)*Real.exp (-T/2)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC (by linarith only [hT])) (Real.exp_pos _).le
  dsimp only [stirlingTestTerm]
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

private theorem measurable_stirling_term {Φ : ℝ → ℝ} (hΦ : Measurable Φ) (T : ℝ) :
    Measurable (stirlingTestTerm Φ T) := by
  have hfac : Measurable (fun n : ℕ => Real.log (n.factorial : ℕ)) := measurable_of_countable _
  have hf := hfac.comp (Nat.measurable_floor.comp (by fun_prop : Measurable fun u : ℝ => Real.exp (T-u)))
  exact (hΦ.mul (by fun_prop)).mul ((by unfold stirlingMain; fun_prop :
    Measurable fun u : ℝ => stirlingMain (Real.exp (T-u))).sub hf)

/-- The factorial remainder contributes exponentially little at every
positive center, even when the confined profile changes sign. -/
theorem abs_stirlingTestResponse_le {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {T : ℝ} (hT : 0 ≤ T) :
    |stirlingTestResponse Φ T| ≤ C*(1+T)*Real.exp (-T/2) := by
  rw [stirlingTestResponse,← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrableOn_exp_Iic 0).const_mul _) ?_).trans_eq
    (by rw [integral_const_mul,integral_exp_Iic_zero,mul_one])
  exact (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun _ hu => stirling_term_bound hC hb hT hu)

private def reciprocalRemainder (Y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, vonMangoldt n/(n:ℝ))-Real.log Y+Real.eulerMascheroniConstant

/-- On the negative half-line all cutoffs exceed exp M. The reciprocal
Mangoldt remainder therefore disappears uniformly inside any L¹ test. -/
private theorem reciprocal_cut_tends_to_zero {f : ℝ → ℝ} (hi : IntegrableOn f (Set.Iic 0)) :
    Tendsto (fun M : ℝ => ∫ u in Set.Iic 0, f u*reciprocalRemainder (Real.exp (M-u)))
      atTop (𝓝 0) := by
  have h := _root_.RHTower.tendsto_real_sum_vonMangoldt_div_sub_log.add_const Real.eulerMascheroniConstant
  rw [neg_add_cancel] at h
  have hr : Tendsto reciprocalRemainder atTop (𝓝 0) := h
  let A := ∫ u in Set.Iic 0, |f u|
  have ha : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(A+1)
  have hδ : 0 < δ := div_pos hε (by linarith only [ha])
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hr δ hδ)
  filter_upwards [Real.tendsto_exp_atTop (eventually_ge_atTop Y)] with M hM
  rw [Real.dist_eq,sub_zero,← Real.norm_eq_abs]
  have hbound : ∀ᵐ u ∂volume.restrict (Set.Iic (0:ℝ)),
      ‖f u*reciprocalRemainder (Real.exp (M-u))‖ ≤ δ*|f u| := by
    rw [ae_restrict_iff' measurableSet_Iic]
    refine Eventually.of_forall fun u hu => ?_
    have hy : Y ≤ Real.exp (M-u) := hM.trans (Real.exp_le_exp.2 (le_sub_self _ hu))
    have hh := hY _ hy
    rw [Real.dist_eq,sub_zero] at hh
    rw [Real.norm_eq_abs,abs_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right hh.le (abs_nonneg _)
  calc _ ≤ ∫ u in Set.Iic 0, δ*|f u| := norm_integral_le_of_norm_le (hi.abs.const_mul δ) hbound
    _ = δ*A := integral_const_mul _ _
    _ < ε := by
      have he : δ*(A+1)=ε := div_mul_cancel₀ _ (by linarith only [ha])
      linarith only [he,hδ]

private theorem measurable_reciprocalRemainder : Measurable reciprocalRemainder := by
  let H := fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, vonMangoldt n/(n:ℝ)
  exact (((measurable_of_countable H).comp Nat.measurable_floor).sub Real.measurable_log).add measurable_const

private theorem cut_arithmetic_term (Φ : ℝ → ℝ) {M T : ℝ} (hM : T ≤ M) (u : ℝ) :
    Φ u*(Real.exp ((u-T)/2)*(∑ n ∈ Finset.Icc 0 ⌊Real.exp (M-u)⌋₊,
      vonMangoldt n*Int.fract (Real.exp (T-u)/n))) =
      stirlingTestTerm Φ T u + Real.exp (T/2)*
      (Φ u*Real.exp (-u/2)*reciprocalRemainder (Real.exp (M-u))) +
      (Real.exp (T/2)*(M-T+1-Real.eulerMascheroniConstant))*(Φ u*Real.exp (-u/2)) := by
  let x := Real.exp (T-u)
  let Y := Real.exp (M-u)
  have he := fractionalMangoldtError_eq (Real.exp_pos (T-u)).le
    (Real.exp_le_exp.2 (sub_le_sub_right hM u))
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, vonMangoldt n*Int.fract (x/n)) =
      (stirlingMain x-Real.log ((⌊x⌋₊).factorial : ℕ))+
        x*(reciprocalRemainder Y+(M-T+1-Real.eulerMascheroniConstant)) := by
    unfold fractionalMangoldtError at he
    rw [Real.log_exp,Real.log_exp] at he
    dsimp only [x,Y,reciprocalRemainder]
    rw [Real.log_exp]
    linear_combination he
  have hscale : Real.exp ((u-T)/2)*x=Real.exp (T/2)*Real.exp (-u/2) := by
    dsimp only [x]; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  change Φ u*(Real.exp ((u-T)/2)*(∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, vonMangoldt n*Int.fract (x/n))) = _
  rw [hsum]
  change _ = Φ u*Real.exp ((u-T)/2)*(stirlingMain x-Real.log ((⌊x⌋₊).factorial : ℕ))+
    Real.exp (T/2)*(Φ u*Real.exp (-u/2)*reciprocalRemainder Y)+
    (Real.exp (T/2)*(M-T+1-Real.eulerMascheroniConstant))*(Φ u*Real.exp (-u/2))
  linear_combination Φ u*(reciprocalRemainder Y+(M-T+1-Real.eulerMascheroniConstant))*hscale

/-- At every nonnegative observation time the common-cutoff integral of
the polar-subtracted Mangoldt wave has a signed limit given by Stirling's
remainder. The cutoff tends to infinity in physical time. -/
theorem tendsto_mangoldt_fractional_response {Φ : ℝ → ℝ} (hm : Measurable Φ)
    (hs : ∀ u, 0 ≤ u → Φ u = 0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {T : ℝ} (hT : 0 ≤ T) :
    let A := ∫ u in Set.Iic (0:ℝ), Φ u*Real.exp (-u/2)
    Tendsto (fun M : ℝ =>
      (∫ t in Set.Iic M, logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ t*fractionalPrimeTest (T-t)) -
      A*(∫ t in Set.Iic M, Real.exp (t/2)*fractionalPrimeTest (T-t))) atTop
      (𝓝 (stirlingTestResponse Φ T)) := by
  let f := fun u : ℝ => Φ u*Real.exp (-u/2)
  let A := ∫ u in Set.Iic (0:ℝ), f u
  let P := logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ
  have hf : IntegrableOn f (Set.Iic 0) := by
    apply ((integrableOn_exp_Iic 0).const_mul C).mono' ((hm.mul (by fun_prop)).aestronglyMeasurable.restrict)
    rw [ae_restrict_iff' measurableSet_Iic]
    refine Eventually.of_forall fun u hu => ?_
    rw [Real.norm_eq_abs, f, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ C*Real.exp (2*u)*Real.exp (-u/2) := mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
      _ ≤ C*Real.exp u := by
        rw [mul_assoc,← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by change u ≤ 0 at hu; linarith only [hu])) hC
  have hS : IntegrableOn (stirlingTestTerm Φ T) (Set.Iic 0) :=
    ((integrableOn_exp_Iic 0).const_mul _).mono' (measurable_stirling_term hm T).aestronglyMeasurable.restrict
      ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun _ hu => stirling_term_bound hC hb hT hu))
  have hR := _root_.RHTower.tendsto_real_sum_vonMangoldt_div_sub_log.add_const Real.eulerMascheroniConstant
  rw [neg_add_cancel] at hR
  have hr : Tendsto reciprocalRemainder atTop (𝓝 0) := hR
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hr 1 zero_lt_one)
  have hlim := ((reciprocal_cut_tends_to_zero hf).const_mul (Real.exp (T/2))).const_add (stirlingTestResponse Φ T)
  rw [mul_zero,add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop T,Real.tendsto_exp_atTop (eventually_ge_atTop Y)] with M hM hMY
  let c := Real.exp (T/2)*(M-T+1-Real.eulerMascheroniConstant)
  let r := fun u : ℝ => f u*reciprocalRemainder (Real.exp (M-u))
  have hir : IntegrableOn r (Set.Iic 0) := by
    apply hf.norm.mono' (((hm.mul (by fun_prop)).mul (measurable_reciprocalRemainder.comp
      (by fun_prop : Measurable fun u : ℝ => Real.exp (M-u)))).aestronglyMeasurable.restrict)
    rw [ae_restrict_iff' measurableSet_Iic]
    refine Eventually.of_forall fun u hu => ?_
    have hh := hY (Real.exp (M-u)) (hMY.trans (Real.exp_le_exp.mpr (le_sub_self M hu)))
    rw [Real.dist_eq,sub_zero] at hh
    rw [r,norm_mul,Real.norm_eq_abs (reciprocalRemainder _)]
    exact mul_le_of_le_one_right (norm_nonneg _) hh.le
  let g := fun u : ℝ => Φ u*(Real.exp ((u-T)/2)*(∑ n ∈ Finset.Icc 0 ⌊Real.exp (M-u)⌋₊,
    vonMangoldt n*Int.fract (Real.exp (T-u)/n)))
  have hphys : (∫ t in Set.Iic M, P t*fractionalPrimeTest (T-t))=∫ u in Set.Iic (0:ℝ), g u := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Iic (0:ℝ)) (f := g) (fun u hu => by
      change Φ u*_ = 0; rw [hs u (lt_of_not_ge hu).le,zero_mul])]
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal,← integral_complex_ofReal]
    simpa only [P,g,Complex.ofReal_mul] using integral_mangoldt_fractional_cut hm hC hb M T
  have heq : (∫ u in Set.Iic (0:ℝ), g u) =
      stirlingTestResponse Φ T+Real.exp (T/2)*(∫ u in Set.Iic (0:ℝ), r u)+c*A := by
    rw [show g=(fun u => stirlingTestTerm Φ T u+Real.exp (T/2)*r u+c*f u) from funext (cut_arithmetic_term Φ hM),
      integral_add (hS.add (hir.const_mul _)) (hf.const_mul _),integral_add hS (hir.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  change stirlingTestResponse Φ T+Real.exp (T/2)*(∫ u in Set.Iic (0:ℝ), r u)=
    (∫ t in Set.Iic M, P t*fractionalPrimeTest (T-t)) - A*(∫ t in Set.Iic M, Real.exp (t/2)*fractionalPrimeTest (T-t))
  rw [hphys,heq,integral_polar_fractional_cut hM]
  dsimp only [c]; ring

#print axioms tendsto_mangoldt_fractional_response
#print axioms abs_stirlingTestResponse_le
#print axioms integral_mangoldt_fractional_cut
end GaloisForLFunctions.ExclusionOfTheCriticalState
