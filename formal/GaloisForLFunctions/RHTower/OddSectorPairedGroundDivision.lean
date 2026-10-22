import GaloisForLFunctions.RHTower.OddSectorFiniteGroundReduction
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFullFormRealRootedGround
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilEvenSectorCrossZeros

/-!
# Paired Fourier division in the arithmetic-corrected odd ground space

The exact arithmetic multiplier makes the shifted form nonnegative on odd
vectors. Its null space is closed under division by `w²-z²` at every Fourier
zero off the two axes. The quadratic splitting preserves the full signed pole
term as well as every finite arithmetic correction; no pole constraint or
positivity of the blind minimum is needed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature CCMFullRealRootedGround

/-- The odd part of the exact arithmetic-corrected ground eigenspace. -/
def oddArithmeticGroundSpace (a : SuzukiPositiveAperture) :
    Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | u ∈ arithmeticGroundSpace a ∧ ccmArchimedeanFormReflection a u = -u}
  zero_mem' := ⟨(arithmeticGroundSpace a).zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu,ho⟩ ⟨hv,hp⟩
    exact ⟨(arithmeticGroundSpace a).add_mem hu hv, by rw [map_add,ho,hp,neg_add]⟩
  smul_mem' := by
    rintro c u ⟨hu,ho⟩
    exact ⟨(arithmeticGroundSpace a).smul_mem c hu, by rw [map_smul,ho,smul_neg]⟩

theorem oddArithmeticGroundSpace_finiteDimensional (a : SuzukiPositiveAperture) :
    FiniteDimensional ℂ (oddArithmeticGroundSpace a) := by
  haveI := arithmeticGroundSpace_finiteDimensional a
  exact Submodule.finiteDimensional_of_le (show oddArithmeticGroundSpace a ≤
    arithmeticGroundSpace a from fun _ h => h.1)

theorem blindMinimizer_mem_oddArithmeticGroundSpace (a : SuzukiPositiveAperture) :
    (blindMinimizer a).1 ∈ oddArithmeticGroundSpace a :=
  ⟨(blind_minimum_iff_mem_arithmeticGroundSpace a (blindMinimizer a)).mp rfl,
    (blindMinimizer a).2.1⟩

theorem oddArithmeticGroundSpace_nontrivial (a : SuzukiPositiveAperture) :
    Nontrivial (oddArithmeticGroundSpace a) := by
  apply nontrivial_of_ne
    (⟨(blindMinimizer a).1,blindMinimizer_mem_oddArithmeticGroundSpace a⟩ :
      oddArithmeticGroundSpace a) 0
  intro h
  have hz : (blindMinimizer a).1 = 0 := congrArg Subtype.val h
  have hn := (blindMinimizer a).2.2.1
  rw [hz,map_zero,norm_zero] at hn
  exact zero_ne_one hn

/-- The whole odd ground space is exactly the null space of the nonnegative shifted form. -/
theorem mem_oddArithmeticGroundSpace_iff (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    u ∈ oddArithmeticGroundSpace a ↔ ccmArchimedeanFormReflection a u = -u ∧
      (arithmeticShiftedForm a u u).re = 0 := by
  constructor
  · rintro ⟨hu,ho⟩
    refine ⟨ho,?_⟩
    rw [arithmeticShiftedForm,(mem_arithmeticGroundSpace_iff a u).mp hu u,sub_self]
    rfl
  · rintro ⟨ho,hu⟩
    refine ⟨(mem_arithmeticGroundSpace_iff a u).mpr ?_,ho⟩
    have hexp (w : CCMArchimedeanFormDomain a) (t : ℝ) :
        (arithmeticShiftedForm a (u + (t : ℂ) • w) (u + (t : ℂ) • w)).re =
          2*t*(arithmeticShiftedForm a u w).re +
            t^2*(arithmeticShiftedForm a w w).re := by
      rw [arithmeticShiftedForm_add_left,arithmeticShiftedForm_add_right,
        arithmeticShiftedForm_add_right,arithmeticShiftedForm_smul_left,
        arithmeticShiftedForm_smul_left,arithmeticShiftedForm_smul_right,
        arithmeticShiftedForm_smul_right,arithmeticShiftedForm_conj a u w]
      simp only [Complex.add_re,Complex.mul_re,Complex.conj_ofReal,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero,Complex.conj_re,Complex.conj_im,hu]
      ring
    have hre (w : CCMArchimedeanFormDomain a)
        (hw : ccmArchimedeanFormReflection a w = -w) :
        (arithmeticShiftedForm a u w).re = 0 := by
      apply eq_zero_of_forall_quadratic_nonneg (arithmeticShiftedForm_odd_nonneg a ⟨w,hw⟩)
      intro t
      rw [← hexp]
      exact arithmeticShiftedForm_odd_nonneg a
        ⟨u + (t : ℂ) • w,by rw [map_add,map_smul,ho,hw,smul_neg,neg_add]⟩
    have hz (w : CCMArchimedeanFormDomain a)
        (hw : ccmArchimedeanFormReflection a w = -w) : arithmeticShiftedForm a u w = 0 := by
      apply Complex.ext
      · exact hre w hw
      · have hi := hre (I • w) (by rw [map_smul,hw,smul_neg])
        rw [arithmeticShiftedForm_smul_right] at hi
        simpa only [Complex.mul_re,Complex.I_re,zero_mul,Complex.I_im,one_mul,
          zero_sub,neg_eq_zero,Complex.zero_im] using hi
    intro v
    have hv := hz (ccmRestrictedWeilOddPart a v) (ccmArchimedeanFormReflection_oddPart a v)
    have hr := arithmeticShiftedForm_reflection a u v
    rw [ho,arithmeticShiftedForm_neg_left] at hr
    rw [ccmRestrictedWeilOddPart,arithmeticShiftedForm_smul_right,
      arithmeticShiftedForm_sub_right] at hv
    have he : arithmeticShiftedForm a u v = 0 := by
      linear_combination hv - (1/2 : ℂ)*hr
    exact sub_eq_zero.mp he

theorem odd_transform_neg (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u) (w : ℂ) :
    unitaryLaplace (timeRep a u) (-w) = -unitaryLaplace (timeRep a u) w := by
  rw [← CCMEvenSector.unitaryLaplace_reflection,hu]
  exact (evalAt a w).map_neg u

/-- Equality of spectral sums preserves the full corrected diagonal, including the pole term. -/
theorem arithmeticShiftedForm_diagonal_balance (a : SuzukiPositiveAperture)
    (u x v w : CCMArchimedeanFormDomain a)
    (hs : ∀ t : ℝ, ‖unitaryLaplace (timeRep a u) t‖^2 +
      ‖unitaryLaplace (timeRep a x) t‖^2 =
      ‖unitaryLaplace (timeRep a v) t‖^2 + ‖unitaryLaplace (timeRep a w) t‖^2)
    (hp : poleTerm a u + poleTerm a x = poleTerm a v + poleTerm a w) :
    (arithmeticShiftedForm a u u).re + (arithmeticShiftedForm a x x).re =
      (arithmeticShiftedForm a v v).re + (arithmeticShiftedForm a w w).re := by
  have hN : ‖ccmArchimedeanFormToAperture a u‖^2 +
      ‖ccmArchimedeanFormToAperture a x‖^2 =
      ‖ccmArchimedeanFormToAperture a v‖^2 + ‖ccmArchimedeanFormToAperture a w‖^2 := by
    rw [← integral_norm_sq_eq,← integral_norm_sq_eq,← integral_norm_sq_eq,
      ← integral_norm_sq_eq,
      ← integral_add (integrable_norm_sq_unitaryLaplace a u)
        (integrable_norm_sq_unitaryLaplace a x),
      ← integral_add (integrable_norm_sq_unitaryLaplace a v)
        (integrable_norm_sq_unitaryLaplace a w)]
    exact integral_congr_ae (Eventually.of_forall hs)
  have hQ : ccmRestrictedWeilSourceQuadratic a u +
      ccmRestrictedWeilSourceQuadratic a x =
      ccmRestrictedWeilSourceQuadratic a v + ccmRestrictedWeilSourceQuadratic a w := by
    rw [source_eq_integral_add_pole,source_eq_integral_add_pole,
      source_eq_integral_add_pole,source_eq_integral_add_pole]
    have hI : (∫ t : ℝ,levelSymbol a t*‖unitaryLaplace (timeRep a u) t‖^2) +
        (∫ t : ℝ,levelSymbol a t*‖unitaryLaplace (timeRep a x) t‖^2) =
        (∫ t : ℝ,levelSymbol a t*‖unitaryLaplace (timeRep a v) t‖^2) +
          ∫ t : ℝ,levelSymbol a t*‖unitaryLaplace (timeRep a w) t‖^2 := by
      rw [← integral_add (integrable_levelSymbol_mul a u) (integrable_levelSymbol_mul a x),
      ← integral_add (integrable_levelSymbol_mul a v) (integrable_levelSymbol_mul a w)]
      exact integral_congr_ae (Eventually.of_forall fun t => by
        dsimp only
        rw [← mul_add,hs t,mul_add])
    linarith
  have ht (s : ℝ) :
      (inner ℂ (logTranslationCLM s (ccmArchimedeanFormToAperture a u).1)
        (ccmArchimedeanFormToAperture a u).1).re +
      (inner ℂ (logTranslationCLM s (ccmArchimedeanFormToAperture a x).1)
        (ccmArchimedeanFormToAperture a x).1).re =
      (inner ℂ (logTranslationCLM s (ccmArchimedeanFormToAperture a v).1)
        (ccmArchimedeanFormToAperture a v).1).re +
      (inner ℂ (logTranslationCLM s (ccmArchimedeanFormToAperture a w).1)
        (ccmArchimedeanFormToAperture a w).1).re := by
    rw [re_inner_logTranslation_eq_integral_cos,re_inner_logTranslation_eq_integral_cos,
      re_inner_logTranslation_eq_integral_cos,re_inner_logTranslation_eq_integral_cos,
      ← integral_add (integrable_cos_mul_norm_sq_ccmFormDomain a u s)
        (integrable_cos_mul_norm_sq_ccmFormDomain a x s),
      ← integral_add (integrable_cos_mul_norm_sq_ccmFormDomain a v s)
        (integrable_cos_mul_norm_sq_ccmFormDomain a w s)]
    apply integral_congr_ae
    filter_upwards [freq_ae a u,freq_ae a x,freq_ae a v,freq_ae a w] with t hu hx hv hw
    rw [hu,hx,hv,hw,← mul_add,hs t,mul_add]
  have hA :
      (inner ℂ (arithmeticCorrection a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re +
      (inner ℂ (arithmeticCorrection a (ccmArchimedeanFormToAperture a x))
        (ccmArchimedeanFormToAperture a x)).re =
      (inner ℂ (arithmeticCorrection a (ccmArchimedeanFormToAperture a v))
        (ccmArchimedeanFormToAperture a v)).re +
      (inner ℂ (arithmeticCorrection a (ccmArchimedeanFormToAperture a w))
        (ccmArchimedeanFormToAperture a w)).re := by
    simp only [inner_arithmeticCorrection,Complex.re_sum,inner_ccmPrimeTransportOperator,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hp := ht (Real.log j.1)
    have hm := ht (-Real.log j.1)
    linear_combination (blindMultiplier a j / Real.sqrt j.1) * (hp + hm)
  have hi (x : CCMArchimedeanFormDomain a) :
      (inner ℂ (ccmArchimedeanFormToAperture a x) (ccmArchimedeanFormToAperture a x)).re =
        ‖ccmArchimedeanFormToAperture a x‖^2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a x)]
    simp [pow_two,Complex.mul_re]
  simp only [arithmeticShiftedForm,arithmeticForm_eq,Complex.sub_re,
    ccmRestrictedWeilForm_self_re_eq_source,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,hi]
  linear_combination hQ - hA - blindMinimum a * hN

private theorem shifted_diagonal_split (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a)
    (hs : ∀ t : ℝ, ‖unitaryLaplace (timeRep a u) t‖^2 =
      ‖unitaryLaplace (timeRep a v) t‖^2 + ‖unitaryLaplace (timeRep a w) t‖^2)
    (hp : poleTerm a u = poleTerm a v + poleTerm a w) :
    (arithmeticShiftedForm a u u).re =
      (arithmeticShiftedForm a v v).re + (arithmeticShiftedForm a w w).re := by
  have hzero (z : ℂ) : unitaryLaplace (timeRep a (0 : CCMArchimedeanFormDomain a)) z = 0 :=
    (evalAt a z).map_zero
  have h := arithmeticShiftedForm_diagonal_balance a u 0 v w
    (fun t => by rw [hzero,norm_zero,zero_pow (by omega),add_zero]; exact hs t)
    (by simpa [poleTerm,hzero] using hp)
  simpa [arithmeticShiftedForm,arithmeticForm] using h

/-- Paired division retains the exact corrected odd ground, including its signed pole term. -/
theorem exists_oddArithmeticGround_div (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : u ∈ oddArithmeticGroundSpace a) {z : ℂ}
    (hz : unitaryLaplace (timeRep a u) z = 0) (him : (z^2).im ≠ 0) :
    ∃ v : CCMArchimedeanFormDomain a, v ∈ oddArithmeticGroundSpace a ∧
      ∀ w : ℂ,unitaryLaplace (timeRep a u) w =
        (w^2-z^2)*unitaryLaplace (timeRep a v) w := by
  obtain ⟨ho,hnull⟩ := (mem_oddArithmeticGroundSpace_iff a u).mp hu
  obtain ⟨hzre,hzim⟩ := (CCMEvenSector.im_sq_ne_zero_iff z).mp him
  have hz0 : z ≠ 0 := fun h => hzre (by rw [h,Complex.zero_re])
  have hnz : -z ≠ z := fun h => hz0 (by linear_combination -h/2)
  have hzm : unitaryLaplace (timeRep a u) (-z) = 0 := by rw [odd_transform_neg a ho,hz,neg_zero]
  obtain ⟨v₁,hv₁⟩ := exists_div a u hz
  have hv₁m : unitaryLaplace (timeRep a v₁) (-z) = 0 := by rw [hv₁ _ hnz,hzm,zero_div]
  obtain ⟨v,hv⟩ := exists_div a v₁ hv₁m
  have hfac₁ (w : ℂ) : unitaryLaplace (timeRep a u) w =
      (w-z)*unitaryLaplace (timeRep a v₁) w := by
    by_cases hw : w=z
    · rw [hw,hz,sub_self,zero_mul]
    · rw [hv₁ w hw]
      field_simp [sub_ne_zero.mpr hw]
  have hfac₂ (w : ℂ) : unitaryLaplace (timeRep a v₁) w =
      (w+z)*unitaryLaplace (timeRep a v) w := by
    by_cases hw : w = -z
    · rw [hw,hv₁m,neg_add_cancel,zero_mul]
    · rw [hv w hw,sub_neg_eq_add]
      field_simp [show w+z ≠ 0 by simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hw]
  have hfac (w : ℂ) : unitaryLaplace (timeRep a u) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w := by
    rw [hfac₁,hfac₂]
    ring
  have hreal (t : ℝ) : (t : ℂ)^2-z^2 ≠ 0 := by
    intro h
    apply him
    have hi := congrArg Complex.im h
    simpa only [Complex.sub_im,← Complex.ofReal_pow,Complex.ofReal_im,
      Complex.zero_im,zero_sub,neg_eq_zero] using hi
  have hvo : ccmArchimedeanFormReflection a v = -v := by
    apply eq_of_transform_eq a
    intro t
    rw [CCMEvenSector.unitaryLaplace_reflection]
    change unitaryLaplace (timeRep a v) (-(t : ℂ)) = (evalAt a t) (-v)
    rw [map_neg,evalAt_apply]
    apply mul_left_cancel₀ (hreal t)
    have h := hfac (-(t : ℂ))
    rw [neg_sq,odd_transform_neg a ho,hfac t] at h
    linear_combination -h
  let c : ℂ := z^2
  let h := u + (I*c.im) • v
  let k := (c.im : ℂ) • v
  have hho : ccmArchimedeanFormReflection a h = -h := by
    dsimp only [h]
    rw [map_add,map_smul,ho,hvo,smul_neg,neg_add]
  have hko : ccmArchimedeanFormReflection a k = -k := by
    dsimp only [k]
    rw [map_smul,hvo,smul_neg]
  have hT (w : ℂ) : unitaryLaplace (timeRep a h) w =
      unitaryLaplace (timeRep a u) w + I*c.im*unitaryLaplace (timeRep a v) w :=
    unitaryLaplace_timeRep_add_smul a u v _ w
  have kT (w : ℂ) : unitaryLaplace (timeRep a k) w =
      (c.im : ℂ)*unitaryLaplace (timeRep a v) w := unitaryLaplace_timeRep_smul a v _ w
  have hs (t : ℝ) : ‖unitaryLaplace (timeRep a u) t‖^2 =
      ‖unitaryLaplace (timeRep a h) t‖^2 + ‖unitaryLaplace (timeRep a k) t‖^2 := by
    rw [hT,kT,hfac]
    change ‖((t : ℂ)^2-c)*unitaryLaplace (timeRep a v) t‖^2 = _
    rw [CCMEvenSector.sq_norm_quadratic_split,add_mul]
  have hp (w : ℂ) :
      conj (unitaryLaplace (timeRep a u) (conj w))*unitaryLaplace (timeRep a u) w =
      conj (unitaryLaplace (timeRep a h) (conj w))*unitaryLaplace (timeRep a h) w +
        conj (unitaryLaplace (timeRep a k) (conj w))*unitaryLaplace (timeRep a k) w := by
    rw [hT,hT,kT,kT,hfac,hfac]
    have he := pair_identity (w^2) c (unitaryLaplace (timeRep a v) (conj w))
      (unitaryLaplace (timeRep a v) w)
    simpa only [map_pow,add_mul,c] using he
  have hPole : poleTerm a u = poleTerm a h + poleTerm a k := by
    have hp_pos := hp (polarPoint (1/2))
    have hp_neg := hp (polarPoint (-1/2))
    rw [conj_polarPoint] at hp_pos hp_neg
    have hn : -(-1/2 : ℝ) = 1/2 := by ring
    rw [hn] at hp_neg
    simp only [poleTerm,Complex.add_re]
    have hr_pos := congrArg Complex.re hp_pos
    have hr_neg := congrArg Complex.re hp_neg
    simp only [Complex.add_re] at hr_pos hr_neg
    linarith
  have hsplit := shifted_diagonal_split a u h k hs hPole
  have hk0 : (arithmeticShiftedForm a k k).re = 0 := by
    linarith [arithmeticShiftedForm_odd_nonneg a ⟨h,hho⟩,
      arithmeticShiftedForm_odd_nonneg a ⟨k,hko⟩]
  have hv0 : (arithmeticShiftedForm a v v).re = 0 := by
    change (arithmeticShiftedForm a ((c.im : ℂ) • v) ((c.im : ℂ) • v)).re = 0 at hk0
    rw [arithmeticShiftedForm_smul_left,arithmeticShiftedForm_smul_right] at hk0
    simp only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] at hk0
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hk0).resolve_left him)).resolve_left him
  exact ⟨v,(mem_oddArithmeticGroundSpace_iff a v).mpr ⟨hvo,hv0⟩,hfac⟩

end RHTower.OddSector
