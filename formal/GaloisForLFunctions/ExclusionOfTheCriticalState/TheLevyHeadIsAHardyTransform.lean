import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadResolvesTheWallCharges
import GaloisForLFunctions.HTGeometry.CarlemanOperatorBound
import GaloisForLFunctions.HTGeometry.SchurKernelOperator
import GaloisForLFunctions.HTGeometry.HardyBoundary.NegativeHalfLineLaplaceHardy

/-!
# The Lévy head is a Hardy transform

The archimedean density is bounded by a multiple of the Carleman kernel.
Its Hankel action therefore preserves `L²` on the positive half-line.
The exponential-mode expansion identifies the Laplace transform of this profile
with the existing Lévy head, giving uniform square bounds on vertical lines.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
open scoped ENNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The archimedean density is globally dominated by the Carleman kernel. -/
theorem archLevyDensity_le_four_div {x : ℝ} (hx : 0 < x) :
    archLevyDensity x ≤ 4 / x := by
  rcases le_or_gt x 1 with hnear | hfar
  · exact (archLevyDensity_le_near hx hnear).trans (by
      rw [div_le_div_iff₀ (by positivity) hx]
      linarith)
  · have hω := archLevyDensity_le_far hfar.le
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x/2))
      (Real.exp_pos (-(x/2))).le
    have hprod : Real.exp (x/2) * Real.exp (-(x/2)) = 1 := by
      rw [← Real.exp_add]
      simp only [add_neg_cancel,Real.exp_zero]
    rw [hprod] at he
    rw [le_div_iff₀ hx]
    have hmul := mul_le_mul_of_nonneg_right hω hx.le
    nlinarith only [he,hmul,Real.exp_pos (-(x/2))]

/-- The Hankel action of the archimedean density on the positive half-line. -/
def levyHankel (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (archLevyDensity (s+t) : ℂ) * f t

theorem stronglyMeasurable_levyHankel {f : ℝ → ℂ} (hf : Measurable f) :
    StronglyMeasurable (levyHankel f) := by
  exact StronglyMeasurable.integral_prod_right
    (f := fun s t : ℝ => (archLevyDensity (s+t) : ℂ)*f t)
    (((Complex.measurable_ofReal.comp
      (measurable_archLevyDensity'.comp (measurable_fst.add measurable_snd))).mul
        (hf.comp measurable_snd)).stronglyMeasurable)

/-- Pointwise domination by the Carleman transform. -/
theorem enorm_levyHankel_le (f : ℝ → ℂ) {s : ℝ} (hs : 0 < s) :
    ‖levyHankel f s‖ₑ ≤ 4 *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1/(s+t)) * ‖f t‖ₑ := by
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ‖(archLevyDensity (s+t) : ℂ)*f t‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), 4*(ENNReal.ofReal (1/(s+t))*‖f t‖ₑ) := by
      refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
      have hst : 0 < s+t := add_pos hs ht
      rw [enorm_mul]
      have hk : ‖(archLevyDensity (s+t) : ℂ)‖ₑ ≤
          4*ENNReal.ofReal (1/(s+t)) := by
        rw [← ofReal_norm,Complex.norm_real,Real.norm_of_nonneg (archLevyDensity_pos hst).le,
          ← ENNReal.ofReal_ofNat (n := 4),← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_one_div] using archLevyDensity_le_four_div hst
      simpa only [mul_assoc] using mul_le_mul' hk (le_rfl : ‖f t‖ₑ ≤ ‖f t‖ₑ)
    _ = _ := lintegral_const_mul' _ _ (by norm_num)

/-- Carleman's inequality puts the archimedean Hankel profile in `L²`. -/
theorem lintegral_levyHankel_sq_le {f : ℝ → ℂ} (hf : Measurable f) :
    (∫⁻ s in Ioi (0 : ℝ), ‖levyHankel f s‖ₑ ^ 2) ≤
      16 * ENNReal.ofReal (Real.pi^2) * ∫⁻ t in Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 := by
  calc
    _ ≤ ∫⁻ s in Ioi (0 : ℝ),
        (4 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1/(s+t))*‖f t‖ₑ)^2 :=
      setLIntegral_mono' measurableSet_Ioi fun s hs =>
        pow_le_pow_left' (enorm_levyHankel_le f hs) 2
    _ = 16 * ∫⁻ s in Ioi (0 : ℝ),
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (1/(s+t))*‖f t‖ₑ)^2 := by
      simp only [mul_pow]
      norm_num only [show (4 : ℝ≥0∞)^2=16 by norm_num]
      exact lintegral_const_mul' _ _ (by norm_num)
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul' (le_refl (16 : ℝ≥0∞)) (lintegral_carleman_sq_le hf.enorm)

/-- The Hankel action preserves square-integrability on the half-line. -/
theorem memLp_levyHankel {f : ℝ → ℂ} (hf : Measurable f)
    (h2 : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (levyHankel f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hi : (∫⁻ t in Ioi (0 : ℝ), ‖f t‖ₑ ^ 2) < ∞ := by
    have h := h2.2
    rw [SchurKernel.eLpNorm_two_eq] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h
  refine ⟨(stronglyMeasurable_levyHankel hf).aestronglyMeasurable, ?_⟩
  rw [SchurKernel.eLpNorm_two_eq]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  exact ((lintegral_levyHankel_sq_le hf).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hi)).ne

/-- The positive-ray profile whose Laplace transform is the Lévy head. -/
def levyHeadProfile (F : ℝ → ℝ) : ℝ → ℂ :=
  levyHankel (fun t => (F (-t) : ℂ))

theorem memLp_levyHeadProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    MemLp (levyHeadProfile F) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (fun t : ℝ => (F (-t) : ℂ)) :=
    Complex.measurable_ofReal.comp (hF.meas.comp measurable_neg)
  exact memLp_levyHankel hm (memLp_reflected_negativeProfile hF.memLp_complex)

/-- Each positive distance resolves the Hankel profile into the archimedean modes. -/
theorem hasSum_levyHeadProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => cexp (-(2*k+1/2 : ℂ)*s)*
      negativeHalfLineLaplace (cx F) (2*k+1/2)) (levyHeadProfile F s) := by
  let r : ℕ → ℝ := fun k => 2*(k : ℝ)+1/2
  let f : ℕ → ℝ → ℂ := fun k t => (Real.exp (-r k*(s+t)) : ℂ)*(F (-t) : ℂ)
  let b : ℕ → ℝ → ℝ := fun k t => Real.exp (-r k*(s+t))*|F (-t)|
  have hbs (t : ℝ) (ht : 0 < t) :
      HasSum (fun k => b k t) (archLevyDensity (s+t)*|F (-t)|) :=
    (RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (add_pos hs ht)).mul_right _
  have hfs (t : ℝ) (ht : 0 < t) :
      HasSum (fun k => f k t) ((archLevyDensity (s+t) : ℂ)*(F (-t) : ℂ)) :=
    (Complex.ofRealCLM.hasSum
      (RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (add_pos hs ht))).mul_right _
  have hI : IntegrableOn (fun t => archLevyDensity (s+t)*|F (-t)|) (Ioi 0) := by
    refine ((hF.integrable.comp_neg.abs).const_mul (4/s)).integrableOn.mono' ?_ ?_
    · exact ((measurable_archLevyDensity'.comp (measurable_const.add measurable_id)).mul
        ((hF.meas.comp measurable_neg).abs)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hst : 0 < s+t := add_pos hs ht
      rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos hst).le (abs_nonneg _))]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (archLevyDensity_le_four_div hst).trans
        (div_le_div_of_nonneg_left (by norm_num) hs (by linarith only [mem_Ioi.mp ht]))
  have hsum : HasSum (fun k => ∫ t in Ioi (0 : ℝ), f k t) (levyHeadProfile F s) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence b
    · intro k
      exact ((by fun_prop : Continuous fun t : ℝ => (Real.exp (-r k*(s+t)) : ℂ)).measurable.mul
        (Complex.measurable_ofReal.comp (hF.meas.comp measurable_neg))).aestronglyMeasurable
    · intro k
      exact Eventually.of_forall fun t => by
        dsimp only [f,b]
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
          Complex.norm_real,Real.norm_eq_abs]
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht => (hbs t ht).summable)
    · exact hI.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht => (hbs t ht).tsum_eq.symm))
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hfs)
  refine hsum.congr_fun fun k => ?_
  have he : (fun t => f k t) = fun t : ℝ =>
      cexp (-(r k : ℂ)*s)*(cexp (-(r k : ℂ)*t)*(F (-t) : ℂ)) := by
    funext t
    dsimp only [f]
    rw [Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he,integral_const_mul]
  have hLap := negativeHalfLineLaplace_eq_laplaceRay_reflect (cx F)
    (fun u hu => by simp only [cx,hF.support u hu,Complex.ofReal_zero]) (r k : ℂ)
  unfold laplaceRay expRay at hLap
  have hint : (∫ t in Ioi (0 : ℝ), cexp (-(r k : ℂ)*t)*(F (-t) : ℂ)) =
      negativeHalfLineLaplace (cx F) (r k : ℂ) := by
    rw [hLap]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [cx,mul_comm,mul_neg]
  rw [hint]
  dsimp only [r]
  push_cast
  rfl

/-- The head is the Laplace transform of its square-integrable Hankel profile. -/
theorem levyHeadTerm_neg_eq_laplaceRay {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {z : ℂ} (hz : 0 < z.re) :
    levyHeadTerm F (-z) = laplaceRay (levyHeadProfile F) z := by
  let r : ℕ → ℝ := fun k => 2*(k : ℝ)+1/2
  let c : ℕ → ℂ := fun k => negativeHalfLineLaplace (cx F) (r k)
  let f : ℕ → ℝ → ℂ := fun k s => c k * cexp (-(z+r k)*s)
  have hr (k : ℕ) : 0 < r k := by dsimp only [r]; positivity
  have hfr (k : ℕ) : (-(z+(r k : ℂ))).re < 0 := by
    simp only [neg_re,add_re,ofReal_re]
    linarith only [hz,hr k]
  have hfi (k : ℕ) : IntegrableOn (f k) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_complex_Ioi (hfr k) 0).const_mul _
  have hfn (k : ℕ) : (∫ s in Ioi (0 : ℝ), ‖f k s‖) =
      ‖c k / ((r k : ℂ)+(z.re : ℂ))‖ := by
    have he (s : ℝ) : ‖f k s‖ = ‖c k‖*Real.exp (-(z.re+r k)*s) := by
      simp only [f,norm_mul,norm_cexp_mul_ofReal,neg_re,add_re,ofReal_re]
    simp_rw [he]
    rw [integral_const_mul,integral_exp_mul_Ioi (by linarith only [hz,hr k]) 0]
    rw [norm_div,← Complex.ofReal_add,Complex.norm_real,
      Real.norm_of_nonneg (by linarith only [hz,hr k])]
    simp only [mul_zero,Real.exp_zero]
    rw [neg_div_neg_eq]
    simp only [div_eq_mul_inv,one_mul,add_comm]
  have hsum : Summable fun k => ∫ s in Ioi (0 : ℝ), ‖f k s‖ := by
    have h := (hasSum_levyHead_resolvents hF
      (p := -(z.re : ℂ)) (by simp only [neg_re,ofReal_re]; linarith only [hz])).summable.norm
    refine h.congr fun k => ?_
    rw [hfn]
    dsimp only [c,r]
    push_cast
    simp only [sub_neg_eq_add]
  have hint : (∫ s in Ioi (0 : ℝ), ∑' k, f k s) =
      ∑' k, ∫ s in Ioi (0 : ℝ), f k s := by
    apply MeasureTheory.integral_tsum
    · exact fun k => (hfi k).aestronglyMeasurable
    · have hi (k : ℕ) : (∫⁻ s in Ioi (0 : ℝ), ‖f k s‖ₑ) =
          ‖∫ s in Ioi (0 : ℝ), ‖f k s‖‖ₑ := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm (hfi k),← ofReal_norm,
          Real.norm_of_nonneg (integral_nonneg fun s => norm_nonneg (f k s))]
      rw [funext hi]
      exact ENNReal.tsum_coe_ne_top_iff_summable.mpr
        (NNReal.summable_coe.mp hsum.abs)
  have hfint (k : ℕ) : (∫ s in Ioi (0 : ℝ), f k s) = c k/((r k : ℂ)+z) := by
    dsimp only [f]
    rw [integral_const_mul,integral_exp_mul_complex_Ioi (hfr k) 0]
    simp only [ofReal_zero,mul_zero,Complex.exp_zero]
    rw [neg_div_neg_eq]
    simp only [div_eq_mul_inv,one_mul,add_comm]
  have hleft : laplaceRay (levyHeadProfile F) z = ∫ s in Ioi (0 : ℝ), ∑' k, f k s := by
    unfold laplaceRay
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have h := (hasSum_levyHeadProfile hF hs).mul_right (expRay z s)
    have he : (fun k : ℕ =>
        (cexp (-(2*k+1/2 : ℂ)*s)*negativeHalfLineLaplace (cx F) (2*k+1/2))*expRay z s) =
        fun k => f k s := by
      funext k
      dsimp only [f,c,r,expRay]
      push_cast
      have hexp : cexp (-(2*(k : ℂ)+1/2)*s) * cexp (-(z*s)) =
          cexp (-(z+(2*(k : ℂ)+1/2))*s) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        _ = negativeHalfLineLaplace (cx F) (2*(k : ℂ)+1/2)*
            (cexp (-(2*(k : ℂ)+1/2)*s)*cexp (-(z*s))) := by ring
        _ = _ := by rw [hexp]
    rw [he] at h
    exact h.tsum_eq.symm
  rw [hleft,hint]
  simp_rw [hfint]
  rw [levyHeadTerm_eq_resolvents hF (by simp only [neg_re]; linarith only [hz])]
  refine tsum_congr fun k => ?_
  dsimp only [c,r]
  push_cast
  simp only [sub_neg_eq_add]

/-- The reflected Lévy head belongs to the Hardy space of the right half-plane. -/
theorem isHalfPlaneHardy_levyHeadTerm {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    IsHalfPlaneHardy (fun z => levyHeadTerm F (-z))
      (∫ s in Ioi (0 : ℝ), ‖levyHeadProfile F s‖^2) := by
  have h := isHalfPlaneHardy_laplaceRay (memLp_levyHeadProfile hF)
  have he : EqOn (fun z => levyHeadTerm F (-z)) (laplaceRay (levyHeadProfile F))
      {z : ℂ | 0 < z.re} := fun z hz => levyHeadTerm_neg_eq_laplaceRay hF hz
  refine ⟨h.holo.congr he, ?_, ?_⟩
  · intro σ hσ
    have heq : (fun ξ => levyHeadTerm F (-(rayLine σ ξ))) =
        fun ξ => laplaceRay (levyHeadProfile F) (rayLine σ ξ) :=
      funext fun ξ => he (by simpa only [mem_setOf_eq,rayLine_re] using hσ)
    rw [heq]
    exact h.memLp σ hσ
  · intro σ hσ
    have heq : (fun ξ => levyHeadTerm F (-(rayLine σ ξ))) =
        fun ξ => laplaceRay (levyHeadProfile F) (rayLine σ ξ) :=
      funext fun ξ => he (by simpa only [mem_setOf_eq,rayLine_re] using hσ)
    simp_rw [congrFun heq]
    exact h.bound σ hσ

end GaloisForLFunctions.ExclusionOfTheCriticalState
