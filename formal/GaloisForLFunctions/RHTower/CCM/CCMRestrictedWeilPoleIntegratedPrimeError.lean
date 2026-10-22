import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompression

/-!
# The exact integrated prime error in the literal Weil pole matrix

The full cross entry equals the integrated Chebyshev deficit plus the exact
Gamma boundary mass, a scalar radius term, and the reciprocal-Mangoldt
correction. Elementary Mertens controls that correction linearly. Thus a
positive literal pole compression would give a quantitative integrated-error
bound, with the actual diagonal and boundary mass still retained. Uniform
bounds on these remaining terms and a fixed-family RH criterion are not
asserted here.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- The integrated Chebyshev deficit on logarithmic radius `0 … 2a`,
written in the physical aperture coordinate. -/
def ccmPoleIntegratedChebyshevDeficit (a : SuzukiPositiveAperture) : ℝ :=
  ∫ x in centralInterval a.1, Real.exp (a.1-x)-Chebyshev.psi (Real.exp (a.1-x))

/-- The reciprocal-Mangoldt correction in the same physical aperture. -/
def ccmPoleIntegratedReciprocalError (a : SuzukiPositiveAperture) : ℝ :=
  ∫ x in centralInterval a.1, ccmReciprocalMangoldtError (a.1+x)

private theorem reciprocal_cumulative_mono : Monotone ccmReciprocalMangoldtCumulative := by
  intro X Y hXY
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hXY)⟩
  · intro n _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

private theorem chebyshev_deficit_integrable (a : SuzukiPositiveAperture) :
    IntegrableOn (fun x => Real.exp (a.1-x)-Chebyshev.psi (Real.exp (a.1-x)))
      (centralInterval a.1) volume := by
  have hm : Antitone (fun x : ℝ => Chebyshev.psi (Real.exp (a.1-x))) := by
    intro x y hxy
    exact Chebyshev.psi_mono (Real.exp_le_exp.mpr (by linarith))
  have hc : Continuous (fun x : ℝ => Real.exp (a.1-x)) := by fun_prop
  exact hc.integrableOn_Icc.sub
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (show -a.1≤a.1 by linarith [a.property])).mp
      (hm.intervalIntegrable (μ:=volume)))

private theorem reciprocal_error_integrable (a : SuzukiPositiveAperture) :
    IntegrableOn (fun x => ccmReciprocalMangoldtError (a.1+x)) (centralInterval a.1) volume := by
  have hm : Monotone (fun x : ℝ => ccmReciprocalMangoldtCumulative (Real.exp (a.1+x))) := by
    intro x y hxy
    exact reciprocal_cumulative_mono (Real.exp_le_exp.mpr (by linarith))
  have hc : Continuous (fun x : ℝ => a.1+x) := by fun_prop
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (show -a.1≤a.1 by linarith [a.property])).mp
    (hm.intervalIntegrable (μ:=volume))).sub hc.integrableOn_Icc

/-- The exact reciprocal correction costs at most a linear radius term, using
only the corpus's elementary Mertens bound. -/
theorem abs_ccmPoleIntegratedReciprocalError_le (a : SuzukiPositiveAperture) :
    |ccmPoleIntegratedReciprocalError a| ≤ (Real.log 4+5)*(2*a.1) := by
  have hm : volume (centralInterval a.1)<⊤ := by
    rw [centralInterval, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h := norm_setIntegral_le_of_norm_le_const_ae (f:=fun x => ccmReciprocalMangoldtError (a.1+x)) hm
    (show ∀ᵐ x ∂volume.restrict (centralInterval a.1),
        ‖ccmReciprocalMangoldtError (a.1+x)‖≤Real.log 4+5 from by
      filter_upwards [ae_restrict_mem (measurableSet_centralInterval a.1)] with x hx
      rw [Real.norm_eq_abs]
      exact abs_ccmReciprocalMangoldtError_le (by have := hx.1; linarith))
  rw [Real.norm_eq_abs, measureReal_def, centralInterval, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [a.property])] at h
  simpa only [ccmPoleIntegratedReciprocalError, centralInterval, sub_neg_eq_add, ← two_mul] using h

private theorem defect_cross_ae (a : SuzukiPositiveAperture) :
    (fun x => inner ℂ ((ccmPolarWeilBoundaryDefect a : SoninL2) x)
      (ccmPolarL2Vector a (-1/2) x)) =ᵐ[volume]
    (centralInterval a.1).indicator (fun x =>
      ((ccmGammaPolarBoundary (a.1-x) (a.1+x)+
        (Real.exp (a.1-x)-Chebyshev.psi (Real.exp (a.1-x)))-
        ccmReciprocalMangoldtError (a.1+x):ℝ):ℂ)) := by
  filter_upwards [ccmPolarWeilBoundaryDefect_coeFn a,ccmPolarL2Vector_coeFn a (-1/2)] with x hd hp
  rw [hd,hp]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx,RCLike.inner_apply,ccmPolarBoundaryArithmeticProfile,
      ccmPolarProfile,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    have he : Real.exp ((-1/2)*x)*Real.exp (x/2)=1 := by
      rw [← Real.exp_add, show (-1/2)*x+x/2=0 by ring,Real.exp_zero]
    rw [← mul_assoc,he,one_mul]
    ring
  · simp only [indicator_of_notMem hx,inner_zero_left]

private theorem defect_cross_integral (a : SuzukiPositiveAperture) :
    inner ℂ (ccmPolarWeilBoundaryDefect a) (ccmPolarApertureVector a (-1/2)) =
      ((ccmGammaPoleCrossBoundaryMass a+ccmPoleIntegratedChebyshevDeficit a-
        ccmPoleIntegratedReciprocalError a:ℝ):ℂ) := by
  change inner ℂ (ccmPolarWeilBoundaryDefect a : SoninL2) (ccmPolarL2Vector a (-1/2)) = _
  rw [L2.inner_def,integral_congr_ae (defect_cross_ae a),
    integral_indicator (measurableSet_centralInterval a.1),integral_complex_ofReal]
  apply congrArg (fun t : ℝ => (t:ℂ))
  have hB : IntegrableOn (fun x => ccmGammaPolarBoundary (a.1-x) (a.1+x))
      (centralInterval a.1) volume := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using integrableOn_ccmGammaPolarBoundary_exp_weight a 0
  have hs := integral_sub (hB.add (chebyshev_deficit_integrable a)) (reciprocal_error_integrable a)
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add hB (chebyshev_deficit_integrable a)]
  rfl

private theorem minus_self (a : SuzukiPositiveAperture) :
    inner ℂ (ccmPolarApertureVector a (-1/2)) (ccmPolarApertureVector a (-1/2)) =
      ((2*Real.sinh a.1:ℝ):ℂ) := by
  have h := l2ReflectionIsometry.inner_map_map
    (ccmPolarL2Vector a (1/2)) (ccmPolarL2Vector a (1/2))
  change inner ℂ (l2Reflection (ccmPolarL2Vector a (1/2)))
    (l2Reflection (ccmPolarL2Vector a (1/2))) = _ at h
  rw [l2Reflection_ccmPolarL2Vector] at h
  change inner ℂ (ccmPolarApertureVector a (-(1/2)))
    (ccmPolarApertureVector a (-(1/2))) =
    inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (1/2)) at h
  simpa only [neg_div] using h.trans (inner_ccmPolarApertureVector_half_self a)

/-- Exact arithmetic cancellation in the cross-pole source: integrated Chebyshev
deficit plus a boundary mass and an elementary, linearly bounded reciprocal error. -/
theorem ccmWeilPoleCross_eq_integratedError (a : SuzukiPositiveAperture) :
    ccmWeilPoleCross a = ccmPoleIntegratedChebyshevDeficit a+
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*a.1)+
      Real.exp (-2*a.1)-1+ccmGammaPoleCrossBoundaryMass a-ccmPoleIntegratedReciprocalError a := by
  have h := defect_cross_integral a
  have hW := ccmPolarWeilRepresentative_represents_form a (1/2) (ccmPolarFormVector a (-1/2))
  rw [ccmArchimedeanFormToAperture_polar,ccmRestrictedWeilForm_pole_cross_eq,
    ← ccmWeilPoleCross_eq] at hW
  have hcross : inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)) =
      ((2*a.1:ℝ):ℂ) := by
    simpa only [neg_neg,neg_div] using inner_ccmPolarApertureVector_opposite a (-1/2)
  rw [ccmPolarWeilBoundaryDefect,inner_add_left,inner_sub_left,
    inner_smul_left (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)),
    inner_smul_left (ccmPolarApertureVector a (-1/2)) (ccmPolarApertureVector a (-1/2)),
    ← hW,hcross,minus_self,Complex.conj_ofReal,Complex.conj_ofReal] at h
  have hR := congrArg Complex.re h
  simp only [← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_add,Complex.ofReal_re] at hR
  have he : Real.exp (-a.1)*(2*Real.sinh a.1)=1-Real.exp (-2*a.1) := by
    rw [Real.sinh_eq]
    have he1 : Real.exp (-a.1)*Real.exp a.1=1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    have he2 : Real.exp (-a.1)*Real.exp (-a.1)=Real.exp (-2*a.1) := by rw [← Real.exp_add];congr 1;ring
    nlinarith
  rw [he] at hR
  linarith

/-- The actual cross entry differs from the integrated Chebyshev deficit by at
most its exact Gamma boundary mass plus an explicit linear radius allowance. -/
theorem abs_integratedChebyshevDeficit_sub_weilPoleCross_le (a : SuzukiPositiveAperture) :
    |ccmPoleIntegratedChebyshevDeficit a-ccmWeilPoleCross a| ≤
      ccmGammaPoleCrossBoundaryMass a+
        (|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+Real.log 4+5)*(2*a.1)+1 := by
  have hEq := ccmWeilPoleCross_eq_integratedError a
  have hM := abs_le.mp (abs_ccmPoleIntegratedReciprocalError_le a)
  have hB := (ccmGammaPoleBoundaryMass_nonneg a).1
  have hK := abs_le.mp (le_refl |-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|)
  have he0 := (Real.exp_pos (-2*a.1)).le
  have he1 : Real.exp (-2*a.1)≤1 := Real.exp_le_one_iff.mpr (by linarith [a.property])
  have ha := a.property
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A positive literal pole compression would control the integrated prime error
by its actual diagonal, Gamma boundary mass, and explicit linear correction. The antecedent is the
remaining source-sign question, not an added axiom. -/
theorem ccmPoleIntegratedChebyshevDeficit_bound_of_compression_nonneg (a : SuzukiPositiveAperture)
    (h : |ccmWeilPoleCross a|≤ccmWeilPoleDiagonal a) :
    |ccmPoleIntegratedChebyshevDeficit a| ≤
      ccmWeilPoleDiagonal a+ccmGammaPoleCrossBoundaryMass a+
        (|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+Real.log 4+5)*(2*a.1)+1 := by
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hc := abs_le.mp h
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end RHTower
