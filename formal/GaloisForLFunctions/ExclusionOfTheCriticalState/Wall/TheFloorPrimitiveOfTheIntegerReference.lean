import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LogarithmicTranslationsAgainstACausalKernel
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegerWaveHasVanishingMeanAbsoluteError

/-!
# The floor primitive of integer quadrature

A single exponential integration of the integer wave counts positive indices
below the moving cutoff. Subtracting the continuum turns this count into
the bounded floor discrepancy, without differentiating the state.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

private def causalHalfKernel (v : ℝ) : ℂ := (Ici 0).indicator (fun r : ℝ => (Real.exp (-r/2):ℂ)) v

private theorem causalHalfKernel_bound (v : ℝ) : ‖causalHalfKernel v‖ ≤ 1 := by
  by_cases hv : 0 ≤ v
  · rw [causalHalfKernel,indicator_of_mem (show v ∈ Ici 0 from hv),Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  · simp [causalHalfKernel,hv]

private theorem reciprocal_sqrt_square_summable : Summable (fun n : ℕ => |(Real.sqrt n)⁻¹|/(n:ℝ)^2) := by
  have hs := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  rw [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact div_le_div_of_nonneg_right (inv_le_one_of_one_le₀ h1) (sq_nonneg _)

private theorem half_kernel_discrete_sum (v : ℝ) :
    (∑' n : ℕ, (((Real.sqrt n)⁻¹:ℝ):ℂ)*causalHalfKernel (v-Real.log n)) =
      (⌊Real.exp v⌋₊:ℂ)*(Real.exp (-v/2):ℂ) := by
  let N := ⌊Real.exp v⌋₊
  have htest {n : ℕ} (hn : 0 < n) : n ≤ N ↔ 0 ≤ v-Real.log n := by
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
    rw [sub_nonneg,Real.log_le_iff_le_exp hn0]
    exact Nat.le_floor_iff (Real.exp_pos v).le
  rw [tsum_eq_sum (s := Finset.Icc 1 N) (fun n hn => ?_)]
  · calc _ = ∑ _n ∈ Finset.Icc 1 N, (Real.exp (-v/2):ℂ) := by
               apply Finset.sum_congr rfl
               intro n hn
               obtain ⟨h1,hN⟩ := Finset.mem_Icc.1 hn
               have hn0 : 0 < (n:ℝ) := by exact_mod_cast h1
               have hs := (htest h1).1 hN
               rw [causalHalfKernel,indicator_of_mem (show v-Real.log n ∈ Ici 0 from hs)]
               have he : Real.exp (-(v-Real.log n)/2) = Real.exp (-v/2)*Real.sqrt n := by
                 have hr : Real.sqrt n = Real.exp (Real.log n/2) := by rw [Real.exp_half,Real.exp_log hn0]
                 rw [hr,← Real.exp_add]; congr 1; ring
               rw [he,← Complex.ofReal_mul]
               congr 1
               field_simp [(Real.sqrt_pos.2 hn0).ne']
    _ = _ := by simp [N]
  · rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    have hv : v-Real.log n ∉ Ici 0 := fun ha => hn (Finset.mem_Icc.2 ⟨h,(htest h).2 ha⟩)
    rw [causalHalfKernel,indicator_of_notMem hv,mul_zero]

/-- The integer count below the moving cutoff gives the exact exponential primitive. -/
theorem integerReference_exp_primitive {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (T : ℝ) :
    IntegrableOn (fun t => Real.exp (t/2)*integerReferenceWave Φ t) (Iic T) ∧
    (∫ t in Iic T, Real.exp (t/2)*integerReferenceWave Φ t) =
      ∫ u, (⌊Real.exp (T-u)⌋₊:ℝ)*Real.exp (u/2)*Φ u := by
  have hK : Measurable causalHalfKernel := (by fun_prop : Measurable (fun r : ℝ => (Real.exp (-r/2):ℂ))).indicator measurableSet_Ici
  have hAll := integral_logShiftWave_mul_causal (b := fun n : ℕ => (Real.sqrt n)⁻¹) (by simp)
    reciprocal_sqrt_square_summable hc.measurable hC hb hK (fun v hv =>
      indicator_of_notMem (show v ∉ Ici 0 from not_le.mpr hv) _) causalHalfKernel_bound T
  have hw (t : ℝ) : logShiftWave (fun n : ℕ => (Real.sqrt n)⁻¹) Φ t = integerReferenceWave Φ t :=
    tsum_continuousIntegerAtom hb t
  have hexp (t : ℝ) : Real.exp (-(T-t)/2) = Real.exp (-T/2)*Real.exp (t/2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hl (t : ℝ) : ((logShiftWave (fun n : ℕ => (Real.sqrt n)⁻¹) Φ t:ℝ):ℂ)*causalHalfKernel (T-t) =
      (Real.exp (-T/2):ℂ)*(((Iic T).indicator (fun u : ℝ => Real.exp (u/2)*integerReferenceWave Φ u) t:ℝ):ℂ) := by
    by_cases ht : t ≤ T
    · rw [hw,causalHalfKernel,indicator_of_mem (show T-t ∈ Ici 0 from sub_nonneg.2 ht),
        indicator_of_mem (show t ∈ Iic T from ht),hexp,Complex.ofReal_mul,Complex.ofReal_mul]; ring
    · rw [causalHalfKernel,indicator_of_notMem (show T-t ∉ Ici 0 from fun h => ht (sub_nonneg.1 h)),
        indicator_of_notMem (show t ∉ Iic T from ht)]; simp
  have hr (u : ℝ) : (Φ u:ℂ)*((⌊Real.exp (T-u)⌋₊:ℂ)*(Real.exp (-(T-u)/2):ℂ)) =
      (Real.exp (-T/2):ℂ)*(((⌊Real.exp (T-u)⌋₊:ℝ)*Real.exp (u/2)*Φ u:ℝ):ℂ) := by
    rw [hexp]; push_cast; ring
  have hi := hAll.1
  simp_rw [hl] at hi
  have hn := Complex.ofReal_ne_zero.mpr (Real.exp_pos (-T/2)).ne'
  have hi' := ((integrable_const_mul_iff (isUnit_iff_ne_zero.2 hn) _).1 hi).re
  refine ⟨(integrable_indicator_iff measurableSet_Iic).1 hi',?_⟩
  have h := hAll.2.2
  simp_rw [hl,half_kernel_discrete_sum,hr] at h
  rw [integral_const_mul,integral_const_mul,integral_complex_ofReal,integral_complex_ofReal,
    integral_indicator measurableSet_Iic] at h
  exact Complex.ofReal_injective (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') h)

/-- The centered primitive is exactly the fractional part at the moving cutoff.
Its absolute value is bounded independently of the cutoff. -/
theorem integerReference_centered_primitive {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (hp : Integrable fun u : ℝ => Real.exp (-u/2)*Φ u)
    (hm : Integrable fun u : ℝ => Real.exp (u/2)*Φ u) (T : ℝ) :
    let A := ∫ u, Real.exp (-u/2)*Φ u
    let V := ∫ t in Iic T, Real.exp (t/2)*(integerReferenceWave Φ t-Real.exp (t/2)*A)
    V = -(∫ u, Int.fract (Real.exp (T-u))*(Real.exp (u/2)*Φ u)) ∧
      |V| ≤ ∫ u, |Real.exp (u/2)*Φ u| := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let q := fun u : ℝ => Int.fract (Real.exp (T-u))*(Real.exp (u/2)*Φ u)
  have hq (u : ℝ) : |q u| ≤ |Real.exp (u/2)*Φ u| := by
    dsimp only [q]
    rw [abs_mul,abs_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Int.fract_lt_one _).le
  have hmeas : Measurable q := (measurable_fract.comp (by fun_prop :
    Measurable fun u : ℝ => Real.exp (T-u))).mul (by fun_prop)
  have hiq : Integrable q := hm.abs.mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hq u)
  have he (u : ℝ) : (⌊Real.exp (T-u)⌋₊:ℝ)*Real.exp (u/2)*Φ u =
      Real.exp T*(Real.exp (-u/2)*Φ u)-q u := by
    have hfloor : (⌊Real.exp (T-u)⌋₊:ℝ) = Real.exp (T-u)-Int.fract (Real.exp (T-u)) := by
      rw [Int.self_sub_fract]
      exact_mod_cast Int.natCast_floor_eq_floor (Real.exp_pos (T-u)).le
    have hprod : Real.exp (T-u)*Real.exp (u/2) = Real.exp T*Real.exp (-u/2) := by
      rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    rw [hfloor,sub_mul,sub_mul,hprod]; dsimp only [q]; ring
  obtain ⟨hi,h⟩ := integerReference_exp_primitive hc hC hb T
  have hsub (t : ℝ) : Real.exp (t/2)*(integerReferenceWave Φ t-Real.exp (t/2)*A) =
      Real.exp (t/2)*integerReferenceWave Φ t-Real.exp t*A := by
    rw [mul_sub,← mul_assoc,← Real.exp_add,show t/2+t/2=t by ring]
  have hval : (∫ t in Iic T, Real.exp (t/2)*(integerReferenceWave Φ t-Real.exp (t/2)*A)) = -(∫ u, q u) := by
    simp_rw [hsub]
    rw [integral_sub hi ((integrableOn_exp_Iic T).mul_const A),h,integral_mul_const,integral_exp_Iic]
    simp_rw [he]
    rw [integral_sub (hp.const_mul _) hiq,integral_const_mul]
    dsimp only [A]; ring
  refine ⟨hval,?_⟩
  change |∫ t in Iic T, Real.exp (t/2)*(integerReferenceWave Φ t-Real.exp (t/2)*A)| ≤ _
  rw [hval,abs_neg]
  exact abs_integral_le_integral_abs.trans (integral_mono hiq.abs hm.abs hq)

/-- The critical state forced by failure of RH has a uniformly bounded,
explicit exponential primitive of its integer quadrature error. -/
theorem riemannHypothesis_or_bounded_integer_quadrature_primitive : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ T : ℝ, let A := ∫ u, Real.exp (-u/2)*Φ u
        let V := ∫ t in Iic T, Real.exp (t/2)*(integerReferenceWave Φ t-Real.exp (t/2)*A)
        V = -(∫ u, Int.fract (Real.exp (T-u))*(Real.exp (u/2)*Φ u)) ∧
          |V| ≤ ∫ u, |Real.exp (u/2)*Φ u| := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,heq,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hw {p : ℝ} (hp : -4 < p) : Integrable fun u => Real.exp (p*u)*Φ u := by
    apply (integrable_mul_rexp_of_domain hd hp).congr
    filter_upwards [heq] with u hu
    rw [hu,mul_comm]
  have hp : Integrable fun u : ℝ => Real.exp (-u/2)*Φ u := by
    simpa only [show ∀ u : ℝ, (-1/2)*u = -u/2 by intro u; ring] using hw (by norm_num : (-4:ℝ) < -1/2)
  have hm : Integrable fun u : ℝ => Real.exp (u/2)*Φ u := by
    simpa only [show ∀ u : ℝ, (1/2)*u = u/2 by intro u; ring] using hw (by norm_num : (-4:ℝ) < 1/2)
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,heq,integerReference_centered_primitive hΦ hC hb hp hm⟩

#print axioms integerReference_exp_primitive
#print axioms integerReference_centered_primitive
#print axioms riemannHypothesis_or_bounded_integer_quadrature_primitive

end GaloisForLFunctions.ExclusionOfTheCriticalState
