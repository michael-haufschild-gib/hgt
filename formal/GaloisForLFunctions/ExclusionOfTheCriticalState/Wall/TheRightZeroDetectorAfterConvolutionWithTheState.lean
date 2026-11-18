import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.LogarithmicPrimeRowFactorization
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PositiveComparisonForThePrimeZeroDetector
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheCriticalStateSeesALeftZero

/-!
# The right-zero detector after convolution with the state

The profile multiplies the leading exponential by its Laplace value at the
reflected zero. The remaining part stays bounded uniformly in the cutoff.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ExceptionalLayerTheory ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry

/-- A cutoff kernel vanishing at one with logarithmically bounded increments
has a continuous normalized logarithmic representative. -/
theorem continuous_logDilationKernel_of_increments (a : ArithmeticFunction ℝ) (w : ℝ → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (h0 : arithmeticKernel a w 1 = 0)
    (hinc : ∀ x y : ℝ, 1 ≤ x → x ≤ y →
      ‖arithmeticKernel a w y-arithmeticKernel a w x‖ ≤ C*(Real.log y-Real.log x)) :
    Continuous (logDilationKernel a w) := by
  let G := fun v : ℝ => arithmeticKernel a w (Real.exp v)
  have hzero (v : ℝ) (hv : v ≤ 0) : G v=0 := by
    rcases hv.lt_or_eq with h | rfl
    · simp [G,arithmeticKernel,Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.2 h)]
    · simpa only [G,Real.exp_zero] using h0
  have hpos (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) : ‖G v-G u‖ ≤ C*(v-u) := by
    simpa only [G,Real.log_exp] using hinc (Real.exp u) (Real.exp v) (Real.one_le_exp_iff.2 hu) (Real.exp_le_exp.2 huv)
  have hle (u v : ℝ) (huv : u ≤ v) : ‖G v-G u‖ ≤ C*(v-u) := by
    by_cases hu : 0 ≤ u
    · exact hpos u v hu huv
    have hu' := le_of_not_ge hu
    by_cases hv : v ≤ 0
    · rw [hzero u hu',hzero v hv,sub_zero,norm_zero]; exact mul_nonneg hC (sub_nonneg.2 huv)
    have h := hpos 0 v le_rfl (le_of_not_ge hv)
    rw [hzero 0 le_rfl,sub_zero,sub_zero] at h
    rw [hzero u hu',sub_zero]
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith only [hu']) hC)
  have hLip : LipschitzWith ⟨C,hC⟩ G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rcases le_total x y with h | h
    · rw [dist_comm (G x),dist_eq_norm,Real.dist_eq,abs_of_nonpos (sub_nonpos.2 h),neg_sub]
      exact hle x y h
    · rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg (sub_nonneg.2 h)]
      exact hle y x h
  exact (by fun_prop : Continuous (fun v : ℝ => ((Real.exp (-v/2):ℝ):ℂ))).mul hLip.continuous

/-- Real-valued arithmetic tests retain their values under complexification. -/
theorem logDilationKernel_ofReal (a : ArithmeticFunction ℝ) (w : ℝ → ℝ) (v : ℝ) :
    logDilationKernel a (fun u => (w u:ℂ)) v =
      ((Real.exp (-v/2)*arithmeticKernel a w (Real.exp v):ℝ):ℂ) := by
  simp only [logDilationKernel,arithmeticKernel,Complex.ofReal_mul,Complex.ofReal_sum,smul_eq_mul,Complex.real_smul]
  push_cast
  rfl

private theorem normalized_detector_error {a : ArithmeticFunction ℝ} {w : ℝ → ℂ} {ρ d : ℂ} {C : ℝ}
    (hb : ∀ x : ℝ, 1 ≤ x → ‖arithmeticKernel a w x - (x:ℂ)^ρ*d‖ ≤ C*Real.sqrt x)
    {v : ℝ} (hv : 0 ≤ v) :
    ‖logDilationKernel a w v-cexp ((ρ-1/2)*v)*d‖ ≤ C := by
  have hx := hb (Real.exp v) (Real.one_le_exp_iff.mpr hv)
  have hrt : Real.sqrt (Real.exp v) = Real.exp (v/2) := (Real.exp_half v).symm
  have hp : ((Real.exp v:ℝ):ℂ)^ρ = cexp ((v:ℂ)*ρ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
  have he : ((Real.exp (-v/2):ℝ):ℂ)*cexp ((v:ℂ)*ρ) = cexp ((ρ-1/2)*v) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]; push_cast; congr 1; ring
  rw [logDilationKernel,← he,mul_assoc,← mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hp,hrt] at hx
  apply (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans_eq
  rw [mul_left_comm,← Real.exp_add,show -v/2+v/2=0 by ring,Real.exp_zero,mul_one]

/-- Convolution with a negative-supported profile preserves a bounded
exponential remainder at every positive time, including its complex phase. -/
theorem confined_profile_preserves_detector_main_term {Φ : ℝ → ℝ} (hΦ : Integrable Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {z d : ℂ}
    (hz : Integrable fun u : ℝ => cexp (-z*u)*(Φ u:ℂ)) {K : ℝ → ℂ} {C T : ℝ}
    (hT : 0 ≤ T) (hK : Integrable fun u : ℝ => (Φ u:ℂ)*K (T-u))
    (hbound : ∀ v : ℝ, 0 ≤ v → ‖K v-cexp (z*v)*d‖ ≤ C) :
    ‖(∫ u, (Φ u:ℂ)*K (T-u)) - cexp (z*T)*d*negativeHalfLineLaplace (cx Φ) (-z)‖ ≤
      C*(∫ u, |Φ u|) := by
  let A := cexp (z*T)*d
  change ‖(∫ u, (Φ u:ℂ)*K (T-u)) - A*(∫ u : ℝ, cexp (-z*u)*(Φ u:ℂ))‖ ≤ _
  rw [← integral_const_mul,← integral_sub hK (hz.const_mul A),← integral_const_mul]
  apply norm_integral_le_integral_norm.trans
  apply integral_mono (hK.sub (hz.const_mul A)).norm (hΦ.abs.const_mul C)
  intro u
  by_cases hu : 0 ≤ u
  · simp [hs _ hu]
  have hmain : A*(cexp (-z*u)*(Φ u:ℂ)) = (Φ u:ℂ)*(cexp (z*((T-u:ℝ):ℂ))*d) := by
    dsimp only [A]
    rw [Complex.ofReal_sub,mul_sub,Complex.exp_sub]
    rw [neg_mul,Complex.exp_neg]
    ring
  rw [hmain,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbound _ (sub_nonneg.2 ((le_of_not_ge hu).trans hT))) (abs_nonneg _)

#print axioms confined_profile_preserves_detector_main_term

/-- The positive alternating weight on the logarithmic axis. -/
def positivePrimeDetector (v : ℝ) : ℝ := Real.exp (-v/2)*primeMeanKernel (Real.exp v)

theorem positivePrimeDetector_nonneg (v : ℝ) : 0 ≤ positivePrimeDetector v := by
  have h : 0 ≤ primeMeanKernel (Real.exp v) := by
    by_cases hv : 0 ≤ v
    · have h := (primeMeanKernel_increment_bounds (x := 1) le_rfl (Real.one_le_exp_iff.2 hv)).1
      rw [primeMeanKernel_eq_zero le_rfl,Real.log_one,Real.log_exp,sub_zero,sub_zero] at h
      linarith only [h,hv]
    · rw [primeMeanKernel_eq_zero (Real.exp_le_one_iff.2 (le_of_not_ge hv))]
  exact mul_nonneg (Real.exp_pos _).le h

theorem positivePrimeDetector_upper (v : ℝ) :
    positivePrimeDetector v ≤ Real.exp (-v/2)*max v 0 := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rcases le_total 0 v with hv | hv
  · have h := (primeMeanKernel_increment_bounds (x := 1) le_rfl (Real.one_le_exp_iff.2 hv)).2
    rw [primeMeanKernel_eq_zero le_rfl,Real.log_one,Real.log_exp,sub_zero,sub_zero] at h
    rw [max_eq_left hv]; linarith only [h,hv]
  · rw [primeMeanKernel_eq_zero (Real.exp_le_one_iff.2 hv),max_eq_right hv]

theorem positivePrimeDetector_le_two (v : ℝ) : positivePrimeDetector v ≤ 2 := by
  apply (positivePrimeDetector_upper v).trans
  rcases le_total 0 v with hv | hv
  · rw [max_eq_left hv,neg_div,Real.exp_neg,inv_mul_eq_div,div_le_iff₀ (Real.exp_pos _)]
    linarith only [Real.add_one_le_exp (v/2)]
  · rw [max_eq_right hv,mul_zero]; norm_num

/-- A visible zero gives an exponential term with bounded remainder in the
actual centred Mangoldt wave tested by a causal kernel. Its modulus is
pointwise dominated by the same positive weight for every zero. -/
theorem visible_zero_detector_for_centred_wave {F Φ : ℝ → ℝ}
    (hd : CriticalHalfLineEnergyDomain F) (hΦ : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ u, |Φ u| ≤ K*Real.exp (2*u))
    {ρ : ℂ} (hρ : 1/2 < ρ.re) (h1 : ρ.re < 1) (hz : riemannZeta ρ=0)
    (hseen : negativeHalfLineLaplace (cx F) (1/2-ρ)≠0) :
    let V := logShiftWave (fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n) Φ
    ∃ (H : ℝ → ℂ) (d : ℂ) (B D : ℝ), d≠0 ∧ 0 ≤ B ∧ 0 ≤ D ∧ Continuous H ∧
      (∀ v, ‖H v‖ ≤ D*positivePrimeDetector v) ∧ ∀ T : ℝ, 0 ≤ T →
        Integrable (fun t : ℝ => (V t:ℂ)*H (T-t)) ∧
        ‖(∫ t, (V t:ℂ)*H (T-t))-cexp ((ρ-1/2)*T)*d‖ ≤ B := by
  obtain ⟨k,d,C,hne,hC,hinc,hbounds⟩ := exists_dominated_prime_zero_detector hρ h1 hz
  let w := centeredDirichletTest k ρ
  let H := logDilationKernel alternatingDivisorCoeff w
  let z := ρ-1/2
  have hc : Continuous H := continuous_logDilationKernel_of_increments _ _ hC
    (by simp [w,arithmeticKernel,centeredDirichletTest]) hinc
  have hD : 0 ≤ 6*C := by positivity
  have hdom (v : ℝ) : ‖H v‖ ≤ (6*C)*positivePrimeDetector v := by
    by_cases hv : 0 ≤ v
    · change ‖((Real.exp (-v/2):ℝ):ℂ)*_‖ ≤ _
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_left (hbounds _ (Real.one_le_exp_iff.2 hv)).1 (Real.exp_pos _).le).trans_eq
        (by unfold positivePrimeDetector; ring)
    · rw [show H v=0 from logDilationKernel_of_neg _ _ (lt_of_not_ge hv),norm_zero]
      exact mul_nonneg hD (positivePrimeDetector_nonneg v)
  have hi : Integrable Φ := by
    apply Integrable.congr _ he
    simpa only [zero_mul,Real.exp_zero,mul_one] using
      integrable_mul_exp_of_domain hd (by norm_num : (-4:ℝ)<0)
  have hζ : -4 < (-z).re := by dsimp only [z]; simp; linarith only [h1]
  have hiζ : Integrable fun u : ℝ => cexp (-z*u)*(Φ u:ℂ) := by
    apply (integrable_abs_mul_exp_of_domain hd hζ).mono' (by fun_prop)
    filter_upwards [he] with u hu
    simp [hu,norm_mul,Complex.norm_exp,Complex.mul_re,Real.norm_eq_abs,mul_comm]
  have hL : negativeHalfLineLaplace (cx Φ) (-z)=negativeHalfLineLaplace (cx F) (1/2-ρ) := by
    rw [show -z=1/2-ρ by dsimp only [z]; ring]
    apply integral_congr_ae
    filter_upwards [he] with u hu
    rw [show cx F u=cx Φ u from congrArg Complex.ofReal hu]
  refine ⟨H,d*negativeHalfLineLaplace (cx Φ) (-z),C*(∫ u, |Φ u|),6*C,
    mul_ne_zero hne (by rwa [hL]),mul_nonneg hC (integral_nonneg fun _ => abs_nonneg _),hD,hc,hdom,?_⟩
  intro T hT
  obtain ⟨hiV,hq,heq⟩ := integral_centredMangoldtWave_mul_alternating hΦ.measurable hK hb w hc.measurable
    (fun v => (hdom v).trans (mul_le_mul_of_nonneg_left (positivePrimeDetector_le_two v) hD)) T
  refine ⟨hiV,?_⟩
  rw [heq,← mul_assoc]
  exact confined_profile_preserves_detector_main_term hi hs hiζ hT hq
    (fun v hv => normalized_detector_error (fun x hx => (hbounds x hx).2.1) hv)

#print axioms visible_zero_detector_for_centred_wave

/-- The positive comparison sends the centred Mangoldt wave to a bounded
function at every cutoff, with its sign retained. -/
theorem bounded_positive_detector_response {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) :
    let V := logShiftWave (fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n) Φ
    ∀ T : ℝ, 0 ≤ T → Integrable (fun t => V t*positivePrimeDetector (T-t)) ∧
      |∫ t, V t*positivePrimeDetector (T-t)| ≤
        (2*(75+2*|Real.eulerMascheroniConstant|))*(∫ u, |Φ u|) := by
  let w := fun v : ℝ => (primeMeanTest v:ℂ)
  let a := alternatingDivisorCoeff
  let b := alternatingPrimeExcess
  let D := 2*(75+2*|Real.eulerMascheroniConstant|)
  have hreal (c : ArithmeticFunction ℝ) (x : ℝ) :
      arithmeticKernel c w x=(arithmeticKernel c primeMeanTest x:ℂ) := by
    simp [arithmeticKernel,w,Complex.real_smul,Complex.ofReal_sum,Complex.ofReal_mul,smul_eq_mul]
  have hac : Continuous (logDilationKernel a w) := by
    apply continuous_logDilationKernel_of_increments _ _ (zero_le_one : (0:ℝ) ≤ 1)
    · rw [hreal]; exact_mod_cast primeMeanKernel_eq_zero (x := 1) le_rfl
    intro x y hx hy
    rw [hreal,hreal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have h := primeMeanKernel_increment_bounds hx hy
    have hl : Real.log x ≤ Real.log y := Real.log_le_log (zero_lt_one.trans_le hx) hy
    change |primeMeanKernel y-primeMeanKernel x| ≤ _
    rw [abs_of_nonneg (by linarith only [h.1,hl] : 0 ≤ primeMeanKernel y-primeMeanKernel x)]
    linarith only [h.2,hl]
  have ha (v : ℝ) : logDilationKernel a w v=(positivePrimeDetector v:ℂ) :=
    logDilationKernel_ofReal _ _ _
  have hnorm (v : ℝ) : ‖logDilationKernel a w v‖ ≤ 2 := by
    rw [ha,Complex.norm_real,Real.norm_of_nonneg (positivePrimeDetector_nonneg _)]
    exact positivePrimeDetector_le_two v
  have hbound (v : ℝ) (hv : 0 ≤ v) : ‖logDilationKernel b w v‖ ≤ D := by
    rw [logDilationKernel,hreal,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (abs_alternatingPrimeExcess_meanTest (Real.one_le_exp_iff.2 hv))
      (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_half,mul_left_comm,← Real.exp_add,show -v/2+v/2=0 by ring,Real.exp_zero,mul_one]
  intro T hT
  obtain ⟨hV,hq,heq⟩ := integral_centredMangoldtWave_mul_alternating hc.measurable hC hb w hac.measurable hnorm T
  simp only [ha,← Complex.ofReal_mul] at hV heq
  refine ⟨hV.re,?_⟩
  have h := congrArg norm heq
  rw [integral_ofReal,Complex.norm_real,Real.norm_eq_abs] at h
  rw [h,← integral_const_mul]
  apply norm_integral_le_integral_norm.trans
  apply integral_mono hq.norm (hi.abs.const_mul D)
  intro u
  by_cases hu : 0 ≤ u
  · simp [hs _ hu]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm D]
  exact mul_le_mul_of_nonneg_left (hbound _ (sub_nonneg.2 ((le_of_not_ge hu).trans hT))) (abs_nonneg _)

#print axioms bounded_positive_detector_response
end GaloisForLFunctions.ExclusionOfTheCriticalState
