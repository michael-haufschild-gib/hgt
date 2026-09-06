import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePoleMatrix
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundVariance

/-!
# The literal two-pole Weil compression

Both Gamma matrix entries follow from the actual Friedrichs action, including
integrability of their logarithmic boundary masses. Combining the full Gamma,
rank-two polar, and prime-power operators gives the exact diagonal and cross
entries. The diagonal cancels the radius term against reciprocal Mangoldt;
the cross entry retains the moving prime tent. No positivity assumption or
claim of a fixed-exponential RH criterion enters these identities.
-/

open Complex MeasureTheory Set
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private def poleGammaBulk (a : SuzukiPositiveAperture) (x : ℝ) : ℝ :=
  x-a.1-Real.eulerMascheroniConstant-Real.log (2*Real.pi)

private theorem gamma_pole_pair_ae (a : SuzukiPositiveAperture) (s : ℝ) :
    (fun x => inner ℂ ((ccmPolarGammaImage a : SoninL2) x) (ccmPolarL2Vector a s x)) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x =>
        ((Real.exp ((s+1/2)*x)*(poleGammaBulk a x+ccmGammaPolarBoundary (a.1-x) (a.1+x)):ℝ):ℂ)) := by
  filter_upwards [ccmPolarGammaImage_coeFn a,ccmPolarL2Vector_coeFn a s] with x hg hp
  rw [hg,hp]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, RCLike.inner_apply, ccmPolarProfile, Complex.conj_ofReal]
    have he : Real.exp (s*x)*Real.exp (x/2) = Real.exp ((s+1/2)*x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← mul_assoc,he]
    unfold poleGammaBulk
    ring
  · simp only [indicator_of_notMem hx,inner_zero_left]

private theorem gamma_pole_integrable (a : SuzukiPositiveAperture) (s : ℝ) :
    IntegrableOn (fun x => Real.exp ((s+1/2)*x) *
      (poleGammaBulk a x+ccmGammaPolarBoundary (a.1-x) (a.1+x))) (centralInterval a.1) volume := by
  have hi := (L2.integrable_inner (𝕜:=ℂ) (ccmPolarGammaImage a : SoninL2)
    (ccmPolarL2Vector a s)).congr (gamma_pole_pair_ae a s)
  have hC := (integrable_indicator_iff (measurableSet_centralInterval a.1)).mp hi
  exact Complex.reCLM.integrable_comp hC

private theorem gamma_pole_pair (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarGammaImage a) (ccmPolarApertureVector a s) =
      ((∫ x in centralInterval a.1, Real.exp ((s+1/2)*x) *
        (poleGammaBulk a x+ccmGammaPolarBoundary (a.1-x) (a.1+x)) : ℝ):ℂ) := by
  change inner ℂ (ccmPolarGammaImage a : SoninL2) (ccmPolarL2Vector a s) = _
  rw [L2.inner_def, integral_congr_ae (gamma_pole_pair_ae a s),
    integral_indicator (measurableSet_centralInterval a.1), integral_complex_ofReal]

/-- Every real exponential weight of the exact Gamma boundary is integrable on the
closed aperture. Actual operator-domain membership supplies this admission. -/
theorem integrableOn_ccmGammaPolarBoundary_exp_weight (a : SuzukiPositiveAperture) (k : ℝ) :
    IntegrableOn (fun x => Real.exp (k*x)*ccmGammaPolarBoundary (a.1-x) (a.1+x))
      (centralInterval a.1) volume := by
  have h := gamma_pole_integrable a (k-1/2)
  rw [show k-1/2+1/2=k by ring] at h
  have hc : Continuous (fun x => Real.exp (k*x)*poleGammaBulk a x) := by
    unfold poleGammaBulk
    fun_prop
  have hi : IntegrableOn (fun x => Real.exp (k*x)*poleGammaBulk a x)
      (centralInterval a.1) volume := hc.integrableOn_Icc
  refine (h.sub hi).congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp
  ring

/-- Unweighted boundary mass in the opposite-pole Gamma entry. -/
def ccmGammaPoleCrossBoundaryMass (a : SuzukiPositiveAperture) : ℝ :=
  ∫ x in centralInterval a.1, ccmGammaPolarBoundary (a.1-x) (a.1+x)

/-- Exponentially weighted boundary mass in the self-pole Gamma entry. -/
def ccmGammaPoleSelfBoundaryMass (a : SuzukiPositiveAperture) : ℝ :=
  ∫ x in centralInterval a.1, Real.exp x*ccmGammaPolarBoundary (a.1-x) (a.1+x)

private theorem gamma_pole_pair_split (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarGammaImage a) (ccmPolarApertureVector a s) =
      ((∫ x in centralInterval a.1, Real.exp ((s+1/2)*x)*poleGammaBulk a x) +
        ∫ x in centralInterval a.1,
          Real.exp ((s+1/2)*x)*ccmGammaPolarBoundary (a.1-x) (a.1+x) : ℝ) := by
  rw [gamma_pole_pair]
  apply congrArg (fun t : ℝ => (t:ℂ))
  simp_rw [mul_add]
  have hc : Continuous (fun x => Real.exp ((s+1/2)*x)*poleGammaBulk a x) := by
    unfold poleGammaBulk
    fun_prop
  exact integral_add (hc.integrableOn_Icc (μ:=volume))
    (integrableOn_ccmGammaPolarBoundary_exp_weight a (s+1/2))

private theorem integral_bulk_cross (a : SuzukiPositiveAperture) :
    (∫ x in centralInterval a.1, poleGammaBulk a x) =
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*a.1)-2*a.1^2 := by
  have hd (x : ℝ) : HasDerivAt
      (fun y => y^2/2-(a.1+Real.eulerMascheroniConstant+Real.log (2*Real.pi))*y)
      (poleGammaBulk a x) x := by
    convert! (((hasDerivAt_id x).pow 2).div_const 2).sub
      ((hasDerivAt_id x).const_mul (a.1+Real.eulerMascheroniConstant+Real.log (2*Real.pi))) using 1
    simp only [poleGammaBulk, id_eq]
    ring
  have hc : Continuous (poleGammaBulk a) := by unfold poleGammaBulk; fun_prop
  rw [centralInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.property]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)]
  ring

private theorem integral_bulk_self (a : SuzukiPositiveAperture) :
    (∫ x in centralInterval a.1, Real.exp x*poleGammaBulk a x) =
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1) -
        Real.exp a.1 + (2*a.1+1)*Real.exp (-a.1) := by
  have hd (x : ℝ) : HasDerivAt
      (fun y => (poleGammaBulk a y-1)*Real.exp y)
      (Real.exp x*poleGammaBulk a x) x := by
    have hp : HasDerivAt (fun y => poleGammaBulk a y-1) 1 x := by
      simpa only [poleGammaBulk, id_eq] using! ((((hasDerivAt_id x).sub_const a.1).sub_const
        Real.eulerMascheroniConstant).sub_const (Real.log (2*Real.pi))).sub_const 1
    convert! hp.mul (Real.hasDerivAt_exp x) using 1; ring
  have hc : Continuous (fun x => Real.exp x*poleGammaBulk a x) := by
    unfold poleGammaBulk
    fun_prop
  rw [centralInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.property]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)]
  rw [Real.sinh_eq]
  unfold poleGammaBulk
  ring

/-- Exact self-pole Gamma entry, with the weighted boundary mass retained. -/
theorem ccmPolarGammaImage_inner_self (a : SuzukiPositiveAperture) :
    inner ℂ (ccmPolarGammaImage a) (ccmPolarApertureVector a (1/2)) =
      (((-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1) -
        Real.exp a.1 + (2*a.1+1)*Real.exp (-a.1)+ccmGammaPoleSelfBoundaryMass a:ℝ):ℂ) := by
  rw [gamma_pole_pair_split a (1/2), show (1/2:ℝ)+1/2=1 by ring]
  simp only [one_mul, integral_bulk_self, ccmGammaPoleSelfBoundaryMass]

/-- Exact opposite-pole Gamma entry, with the unweighted boundary mass retained. -/
theorem ccmPolarGammaImage_inner_cross (a : SuzukiPositiveAperture) :
    inner ℂ (ccmPolarGammaImage a) (ccmPolarApertureVector a (-1/2)) =
      (((-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*a.1)-2*a.1^2+
        ccmGammaPoleCrossBoundaryMass a:ℝ):ℂ) := by
  rw [gamma_pole_pair_split a (-1/2), show (-1/2:ℝ)+1/2=0 by ring]
  simp only [zero_mul, Real.exp_zero, one_mul, integral_bulk_cross, ccmGammaPoleCrossBoundaryMass]

/-- The boundary term contributes nonnegatively at every real exponential weight. -/
theorem integral_ccmGammaPolarBoundary_exp_weight_nonneg (a : SuzukiPositiveAperture) (k : ℝ) :
    0 ≤ ∫ x in centralInterval a.1,
      Real.exp (k*x)*ccmGammaPolarBoundary (a.1-x) (a.1+x) := by
  rw [centralInterval, integral_Icc_eq_integral_Ioo]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact mul_nonneg (Real.exp_pos _).le
    (ccmGammaPolarBoundary_pos (by linarith [hx.2]) (by linarith [hx.1])).le

/-- Both exact Gamma boundary masses are nonnegative. -/
theorem ccmGammaPoleBoundaryMass_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ ccmGammaPoleCrossBoundaryMass a ∧ 0 ≤ ccmGammaPoleSelfBoundaryMass a := by
  constructor
  · simpa only [ccmGammaPoleCrossBoundaryMass, zero_mul, Real.exp_zero, one_mul] using
      integral_ccmGammaPolarBoundary_exp_weight_nonneg a 0
  · simpa only [ccmGammaPoleSelfBoundaryMass, one_mul] using
      integral_ccmGammaPolarBoundary_exp_weight_nonneg a 1

/-- The actual full Weil self entry of the positive exponential pole. -/
def ccmWeilPoleDiagonal (a : SuzukiPositiveAperture) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a (ccmPolarFormVector a (1/2))

/-- The actual full Weil opposite-pole entry, before any sign assumption. -/
def ccmWeilPoleCross (a : SuzukiPositiveAperture) : ℝ :=
  (ccmRestrictedWeilForm a (ccmPolarFormVector a (1/2))
    (ccmPolarFormVector a (-1/2))).re

private theorem weil_pole_pair (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmRestrictedWeilForm a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a s) =
      inner ℂ (ccmPolarGammaImage a) (ccmPolarApertureVector a s) +
      inner ℂ (ccmPolarOperator a (ccmPolarApertureVector a (1/2))) (ccmPolarApertureVector a s) -
      inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2))) (ccmPolarApertureVector a s) := by
  rw [ccmPolarWeilRepresentative_represents_form, ccmArchimedeanFormToAperture_polar,
    ← ccmRestrictedWeilOperator_polar_apply,
    ccmRestrictedWeilOperator_polarHalf_eq_gamma_polar_prime, inner_sub_left, inner_add_left]

private theorem inner_minus_self (a : SuzukiPositiveAperture) :
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

/-- Exact diagonal of the literal full Weil pole compression. -/
theorem ccmWeilPoleDiagonal_eq (a : SuzukiPositiveAperture) :
    ccmWeilPoleDiagonal a =
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1) -
      Real.exp a.1+(2*a.1+1)*Real.exp (-a.1)+ccmGammaPoleSelfBoundaryMass a +
      2*(2*a.1)*(2*Real.sinh a.1) -
      (2*Real.exp a.1*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)) -
        2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1))) := by
  unfold ccmWeilPoleDiagonal
  rw [← ccmRestrictedWeilForm_self_re_eq_source, weil_pole_pair,
    ccmPolarGammaImage_inner_self, ccmFinitePrimeOperator_polar_self,
    ccmPolarOperator_polarPlus_apply, inner_add_left]
  rw [inner_smul_left (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (1/2)) ((2*a.1:ℝ):ℂ),
    inner_smul_left (ccmPolarApertureVector a (-1/2)) (ccmPolarApertureVector a (1/2)) ((2*Real.sinh a.1:ℝ):ℂ)]
  simp only [Complex.conj_ofReal, inner_ccmPolarApertureVector_half_self,
    show (-1/2:ℝ)=-(1/2) by ring, inner_ccmPolarApertureVector_opposite]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.ofReal_re]
  ring

/-- The diagonal's linear radius term cancels exactly against reciprocal Mangoldt. -/
theorem ccmWeilPoleDiagonal_eq_error (a : SuzukiPositiveAperture) :
    ccmWeilPoleDiagonal a =
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1) -
      Real.exp a.1+(1-2*a.1)*Real.exp (-a.1)+ccmGammaPoleSelfBoundaryMass a -
      2*Real.exp a.1*ccmReciprocalMangoldtError (2*a.1) +
      2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)) := by
  rw [ccmWeilPoleDiagonal_eq, ccmReciprocalMangoldtError, Real.sinh_eq]
  ring

/-- The opposite-pole full Weil entry is real and retains the complete moving prime tent. -/
theorem ccmRestrictedWeilForm_pole_cross_eq (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilForm a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a (-1/2)) =
      (((-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*a.1)+2*a.1^2+
        (2*Real.sinh a.1)^2+ccmGammaPoleCrossBoundaryMass a-ccmPolarPrimeTent a:ℝ):ℂ) := by
  rw [weil_pole_pair, ccmPolarGammaImage_inner_cross, ccmFinitePrimeOperator_polar_cross,
    ccmPolarOperator_polarPlus_apply, inner_add_left]
  have hc : inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)) =
      ((2*a.1:ℝ):ℂ) := by
    simpa only [neg_neg, neg_div] using inner_ccmPolarApertureVector_opposite a (-1/2)
  rw [inner_smul_left (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)) ((2*a.1:ℝ):ℂ),
    inner_smul_left (ccmPolarApertureVector a (-1/2)) (ccmPolarApertureVector a (-1/2)) ((2*Real.sinh a.1:ℝ):ℂ)]
  simp only [Complex.conj_ofReal, hc, inner_minus_self]
  push_cast
  ring

/-- Exact real cross entry of the full Weil pole matrix. -/
theorem ccmWeilPoleCross_eq (a : SuzukiPositiveAperture) :
    ccmWeilPoleCross a =
      (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*a.1)+2*a.1^2+
        (2*Real.sinh a.1)^2+ccmGammaPoleCrossBoundaryMass a-ccmPolarPrimeTent a := by
  rw [ccmWeilPoleCross, ccmRestrictedWeilForm_pole_cross_eq, Complex.ofReal_re]

end RHTower
