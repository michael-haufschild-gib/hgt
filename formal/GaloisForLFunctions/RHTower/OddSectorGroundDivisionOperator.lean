import GaloisForLFunctions.RHTower.OddSectorGroundOriginInterpolation
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanLogWeightEquivalence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogDenseFormCore

/-!
# Ground-normalized squared-frequency division

Subtracting the value of an odd source at a nonzero point times the canonical
ground generator makes paired division possible at the same aperture. At an
imaginary point the quotient gains a full physical-to-form norm estimate. This
is the compact resolvent mechanism for the corrected odd spectral problem.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature

theorem eq_of_sq_mul_transform_eq (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (z : ℂ)
    (h : ∀ w : ℂ, (w^2-z^2)*unitaryLaplace (timeRep a u) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w) : u = v := by
  have hc (x : CCMArchimedeanFormDomain a) : Continuous (unitaryLaplace (timeRep a x)) :=
    (CCMXiStrip.differentiable_unitaryLaplace a.2.le
      (integrable_timeRep a x) (supportedIn_timeRep a x)).continuous
  have he : unitaryLaplace (timeRep a u) = unitaryLaplace (timeRep a v) := by
    apply Continuous.ext_on
      (dense_univ.sdiff_finite (Polynomial.finite_setOf_isRoot
        (Polynomial.monic_X_pow_sub_C (z^2) two_ne_zero).ne_zero)) (hc u) (hc v)
    intro w hw
    have hn : w^2-z^2 ≠ 0 := by simpa [Polynomial.IsRoot.def] using hw.2
    exact mul_left_cancel₀ hn (h w)
  exact eq_of_transform_eq a fun t => congrFun he t

/-- Odd projection followed by the unique ground subtraction that kills one
prescribed nonzero evaluation. -/
def groundDivisionInput (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) (z : ℂ) (u : CCMArchimedeanFormDomain a) :
    CCMArchimedeanFormDomain a :=
  ccmRestrictedWeilOddPart a u -
    (unitaryLaplace (timeRep a (ccmRestrictedWeilOddPart a u)) z /
      unitaryLaplace (timeRep a G) z) • G

private theorem exists_groundDivision (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hz : unitaryLaplace (timeRep a G) z ≠ 0)
    (u : CCMArchimedeanFormDomain a) :
    ∃ v : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a v = -v ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a (groundDivisionInput a G z u)) w =
        (w^2-z^2)*unitaryLaplace (timeRep a v) w := by
  apply exists_odd_paired_div a (u := groundDivisionInput a G z u) ?_ hz0 ?_
  · simp only [groundDivisionInput,map_sub,map_smul,
      ccmArchimedeanFormReflection_oddPart,hG.1.2,smul_neg,neg_sub_neg,neg_sub]
  · change (evalAt a z) (ccmRestrictedWeilOddPart a u -
      (unitaryLaplace (timeRep a (ccmRestrictedWeilOddPart a u)) z /
        unitaryLaplace (timeRep a G) z) • G) = 0
    rw [map_sub,map_smul,evalAt_apply,evalAt_apply,smul_eq_mul,
      div_mul_cancel₀ _ hz,sub_self]

/-- Canonical paired quotient; uniqueness of the transform removes all
dependence on the existential division construction. -/
def groundDivision (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hz : unitaryLaplace (timeRep a G) z ≠ 0)
    (u : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain a :=
  Classical.choose (exists_groundDivision a hG hz0 hz u)

theorem groundDivision_odd (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hz : unitaryLaplace (timeRep a G) z ≠ 0)
    (u : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormReflection a (groundDivision a hG hz0 hz u) =
      -groundDivision a hG hz0 hz u :=
  (Classical.choose_spec (exists_groundDivision a hG hz0 hz u)).1

theorem groundDivision_factor (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hz : unitaryLaplace (timeRep a G) z ≠ 0)
    (u : CCMArchimedeanFormDomain a) (w : ℂ) :
    unitaryLaplace (timeRep a (groundDivisionInput a G z u)) w =
      (w^2-z^2)*unitaryLaplace (timeRep a (groundDivision a hG hz0 hz u)) w :=
  (Classical.choose_spec (exists_groundDivision a hG hz0 hz u)).2 w

private theorem oddPart_add (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilOddPart a (u+v) =
      ccmRestrictedWeilOddPart a u + ccmRestrictedWeilOddPart a v := by
  simp only [ccmRestrictedWeilOddPart,map_add]
  module

private theorem oddPart_smul (a : SuzukiPositiveAperture)
    (c : ℂ) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilOddPart a (c • u) = c • ccmRestrictedWeilOddPart a u := by
  simp only [ccmRestrictedWeilOddPart,map_smul]
  module

theorem groundDivisionInput_add (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) (z : ℂ) (u v : CCMArchimedeanFormDomain a) :
    groundDivisionInput a G z (u+v) =
      groundDivisionInput a G z u + groundDivisionInput a G z v := by
  unfold groundDivisionInput
  rw [oddPart_add]
  change _ - ((evalAt a z) (ccmRestrictedWeilOddPart a u + ccmRestrictedWeilOddPart a v) /
    unitaryLaplace (timeRep a G) z) • G = _
  rw [map_add,add_div]
  simp only [evalAt_apply]
  module

theorem groundDivisionInput_smul (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) (z c : ℂ) (u : CCMArchimedeanFormDomain a) :
    groundDivisionInput a G z (c • u) = c • groundDivisionInput a G z u := by
  unfold groundDivisionInput
  rw [oddPart_smul,unitaryLaplace_timeRep_smul,mul_div_assoc]
  module

/-- Linear squared-frequency difference quotient on the full form domain;
it first projects to odd sources. -/
def groundDivisionLM (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hz : unitaryLaplace (timeRep a G) z ≠ 0) :
    CCMArchimedeanFormDomain a →ₗ[ℂ] CCMArchimedeanFormDomain a where
  toFun := groundDivision a hG hz0 hz
  map_add' u v := by
    apply eq_of_sq_mul_transform_eq a _ _ z
    intro w
    rw [← groundDivision_factor a hG hz0 hz (u+v),groundDivisionInput_add]
    change (evalAt a w) (groundDivisionInput a G z u + groundDivisionInput a G z v) =
      (w^2-z^2)*(evalAt a w)
        (groundDivision a hG hz0 hz u + groundDivision a hG hz0 hz v)
    rw [map_add,map_add]
    simp only [evalAt_apply]
    rw [groundDivision_factor a hG hz0 hz u,
      groundDivision_factor a hG hz0 hz v,mul_add]
  map_smul' c u := by
    change groundDivision a hG hz0 hz (c • u) = c • groundDivision a hG hz0 hz u
    apply eq_of_sq_mul_transform_eq a _ _ z
    intro w
    rw [← groundDivision_factor a hG hz0 hz (c • u),groundDivisionInput_smul,
      unitaryLaplace_timeRep_smul,unitaryLaplace_timeRep_smul,
      groundDivision_factor a hG hz0 hz u]
    ring

/-- Fixed-aperture form norm is the exact weighted transform norm. -/
theorem form_norm_sq_eq_transform_integral (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ‖u‖^2 = ∫ t : ℝ, ccmArchimedeanFormWeight t *
      ‖unitaryLaplace (timeRep a u) t‖^2 := by
  change ‖u.1‖^2 = _
  rw [norm_sq_ccmArchimedeanFourierL2]
  exact integral_congr_ae ((freq_ae a u).mono fun t ht => by
    dsimp only at ht ⊢
    rw [ht])

/-- Paired division at an imaginary point improves physical mass to full
logarithmic form regularity, with no sign condition on the arithmetic form. -/
theorem paired_division_physical_norm_bound (a : SuzukiPositiveAperture)
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : CCMArchimedeanFormDomain a,
      (∀ w : ℂ, unitaryLaplace (timeRep a u) w =
        (w^2-(I*(b : ℂ))^2)*unitaryLaplace (timeRep a v) w) →
      ‖v‖ ≤ C * ‖ccmArchimedeanFormToAperture a u‖ := by
  let k : ℝ := max 1 (b^2)⁻¹
  let A : ℝ := 2*ccmArchimedeanLogComparisonConstant*k^2
  have hk1 : 1 ≤ k := le_max_left _ _
  have hk : 0 < k := zero_lt_one.trans_le hk1
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hkb : 1 ≤ k*b^2 := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 (b^2)⁻¹) hb2.le
    simpa only [inv_mul_cancel₀ hb2.ne'] using h
  have hC : 0 < ccmArchimedeanLogComparisonConstant :=
    zero_lt_one.trans_le one_le_ccmArchimedeanLogComparisonConstant
  have hA : 0 < A := mul_pos (mul_pos two_pos hC) (sq_pos_of_pos hk)
  have hw (t : ℝ) : ccmArchimedeanFormWeight t ≤ A*(t^2+b^2)^2 := by
    have hlog := suzukiLogWeight_le_one_add_abs t
    have harch := ccmArchimedeanFormWeight_le_logComparison t
    have hsmall : 1+|t| ≤ 2*(1+t^2)^2 := by
      nlinarith [sq_nonneg (|t|-1),sq_abs t,sq_nonneg (t^2)]
    have hlin : 1+t^2 ≤ k*(t^2+b^2) := by
      have := mul_le_mul_of_nonneg_right hk1 (sq_nonneg t)
      nlinarith
    have hsq : (1+t^2)^2 ≤ k^2*(t^2+b^2)^2 := by
      have hr := sq_le_sq₀ (by positivity : 0 ≤ 1+t^2)
        (by positivity : 0 ≤ k*(t^2+b^2))
      have hh := hr.mpr hlin
      nlinarith
    have h1 := mul_le_mul_of_nonneg_left hlog hC.le
    have h2 := mul_le_mul_of_nonneg_left hsmall hC.le
    have h3 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2*ccmArchimedeanLogComparisonConstant)
    dsimp only [A]
    nlinarith
  refine ⟨A+1,by positivity,?_⟩
  intro u v hfac
  have hnorm (t : ℝ) : ‖unitaryLaplace (timeRep a u) t‖^2 =
      (t^2+b^2)^2*‖unitaryLaplace (timeRep a v) t‖^2 := by
    have he : (t : ℂ)^2-(I*(b : ℂ))^2 = ((t^2+b^2 : ℝ) : ℂ) := by
      push_cast
      rw [mul_pow,I_sq]
      ring
    rw [hfac,he,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hsq : ‖v‖^2 ≤ A*‖ccmArchimedeanFormToAperture a u‖^2 := by
    rw [form_norm_sq_eq_transform_integral,← integral_norm_sq_eq,
      ← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun t => mul_nonneg (ccmArchimedeanFormWeight_pos t).le (sq_nonneg _))
      ((integrable_norm_sq_unitaryLaplace a u).const_mul A)
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [hnorm]
      nlinarith [mul_le_mul_of_nonneg_right (hw t)
        (sq_nonneg ‖unitaryLaplace (timeRep a v) t‖)]
  have hmargin : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
  apply (sq_le_sq₀ (norm_nonneg v)
    (mul_nonneg (by positivity : 0 ≤ A+1)
      (norm_nonneg (ccmArchimedeanFormToAperture a u)))).mp
  rw [mul_pow]
  exact hsq.trans (mul_le_mul_of_nonneg_right hmargin
    (sq_nonneg ‖ccmArchimedeanFormToAperture a u‖))

private theorem physical_norm_oddPart_le (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilOddPart a u)‖ ≤
      ‖ccmArchimedeanFormToAperture a u‖ := by
  have hr : ‖ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u)‖ =
      ‖ccmArchimedeanFormToAperture a u‖ := by
    change ‖((ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) :
      suzukiApertureHilbert a) : SoninL2)‖ =
      ‖((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2)‖
    rw [ccmArchimedeanFormToAperture_reflection]
    exact l2ReflectionIsometry.norm_map _
  rw [ccmRestrictedWeilOddPart,map_smul,map_sub,norm_smul]
  have h := norm_sub_le (ccmArchimedeanFormToAperture a u)
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u))
  rw [hr] at h
  have hc : ‖(2 : ℂ)⁻¹‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  linarith

private theorem transform_imaginary_bound (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (b : ℝ) :
    ‖unitaryLaplace (timeRep a u) (I*(b : ℂ))‖ ≤
      ‖ccmPolarApertureVector a (2*Real.pi*b)‖ *
        ‖ccmArchimedeanFormToAperture a u‖ := by
  have he : polarPoint (2*Real.pi*b) = I*(b : ℂ) := by
    unfold polarPoint
    push_cast
    field_simp
  rw [← he,← inner_polar_eq]
  exact norm_inner_le_norm (𝕜 := ℂ) (ccmPolarApertureVector a (2*Real.pi*b))
    (ccmArchimedeanFormToAperture a u)

/-- The normalized division is bounded by physical mass, not merely the
stronger form norm. -/
theorem groundDivision_physical_bound (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CCMArchimedeanFormDomain a,
      ‖groundDivision a hG (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')) hz u‖ ≤
        C * ‖ccmArchimedeanFormToAperture a u‖ := by
  obtain ⟨D,hD,hd⟩ := paired_division_physical_norm_bound a b hb
  let B : ℝ := ‖ccmPolarApertureVector a (2*Real.pi*b)‖ /
    ‖unitaryLaplace (timeRep a G) (I*(b : ℂ))‖ * ‖ccmArchimedeanFormToAperture a G‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨D*(1+B),mul_pos hD (by positivity),fun u => ?_⟩
  have hin : ‖ccmArchimedeanFormToAperture a (groundDivisionInput a G (I*(b : ℂ)) u)‖ ≤
      (1+B)*‖ccmArchimedeanFormToAperture a u‖ := by
    let v := ccmRestrictedWeilOddPart a u
    have hev := transform_imaginary_bound a v b
    have hproj := physical_norm_oddPart_le a u
    have hcoeff : ‖unitaryLaplace (timeRep a v) (I*(b : ℂ)) /
        unitaryLaplace (timeRep a G) (I*(b : ℂ))‖ *
          ‖ccmArchimedeanFormToAperture a G‖ ≤
        B*‖ccmArchimedeanFormToAperture a v‖ := by
      rw [norm_div]
      have hh := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hev
          (norm_nonneg (unitaryLaplace (timeRep a G) (I*(b : ℂ)))))
        (norm_nonneg (ccmArchimedeanFormToAperture a G))
      calc
        _ ≤ (‖ccmPolarApertureVector a (2*Real.pi*b)‖ *
            ‖ccmArchimedeanFormToAperture a v‖) /
            ‖unitaryLaplace (timeRep a G) (I*(b : ℂ))‖ *
            ‖ccmArchimedeanFormToAperture a G‖ := hh
        _ = B*‖ccmArchimedeanFormToAperture a v‖ := by dsimp only [B]; ring
    unfold groundDivisionInput
    rw [map_sub,map_smul]
    have hsub := norm_sub_le (ccmArchimedeanFormToAperture a v)
      ((unitaryLaplace (timeRep a v) (I*(b : ℂ)) /
        unitaryLaplace (timeRep a G) (I*(b : ℂ))) • ccmArchimedeanFormToAperture a G)
    rw [norm_smul] at hsub
    have hmul := mul_le_mul_of_nonneg_left hproj hB
    change ‖_ - _‖ ≤ _
    change ‖ccmArchimedeanFormToAperture a v‖ ≤ _ at hproj
    nlinarith
  have hbound := hd (groundDivisionInput a G (I*(b : ℂ)) u)
    (groundDivision a hG (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')) hz u)
    (groundDivision_factor a hG _ hz u)
  have hh := mul_le_mul_of_nonneg_left hin hD.le
  nlinarith

/-- Compact ground-normalized resolvent on the actual complete form domain. -/
def groundDivisionCLM (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  ((groundDivisionLM a hG (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')) hz).extendOfNorm
    (ccmArchimedeanFormToAperture a).toLinearMap).comp (ccmArchimedeanFormToAperture a)

theorem groundDivisionCLM_apply (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    (u : CCMArchimedeanFormDomain a) :
    groundDivisionCLM a hG b hb hz u =
      groundDivision a hG (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')) hz u := by
  obtain ⟨C,_,hC⟩ := groundDivision_physical_bound a hG b hb hz
  exact LinearMap.extendOfNorm_eq (denseRange_ccmArchimedeanFormToAperture a) ⟨C,hC⟩ u

theorem groundDivisionCLM_isCompact (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0) :
    IsCompactOperator (groundDivisionCLM a hG b hb hz) :=
  (isCompactOperator_ccmArchimedeanFormToAperture a).clm_comp _

end RHTower.OddSector
