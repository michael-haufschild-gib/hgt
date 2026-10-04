import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarOperatorDomain
import GaloisForLFunctions.RHTower.SuzukiDirichletFormCore

/-!
# Full Gamma multiplier admission for sharply restricted smooth tests

The derivative primitive on [-a,a] equals g-g(-a), without an endpoint-vanishing
assumption. Adding the actual constant pole recovers the literal sharp cutoff.
The existing primitive and polar operator-domain theorems then admit its full
Gamma Fourier multiplier in L2. This is test admission, not a global-domain
claim for the canonical ground.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct FourierTransform
noncomputable section
namespace RHTower
attribute [local instance] Measure.Subtype.measureSpace


private theorem derivative_zeroExtend_inside
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    suzukiApertureZeroExtend (suzukiSmoothDerivativeCoordinate a g hg hc) =ᵐ[
      volume.restrict (Icc (-a.1) a.1)] deriv g := by
  change ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1), _
  rw [ae_restrict_iff_subtype measurableSet_Icc]
  filter_upwards [suzukiApertureRepresentative_ae (suzukiSmoothDerivativeCoordinate a g hg hc),
    suzukiSmoothDerivativeCoordinate_coeFn a g hg hc] with x hx hd
  rw [suzukiApertureZeroExtend_apply, hx, hd]

theorem suzukiAperturePrimitive_smoothDerivativeCoordinate_boundary
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    (suzukiAperturePrimitive a.1 (suzukiSmoothDerivativeCoordinate a g hg hc) :
      SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
        fun x => g (x : ℝ) - g (-a.1) := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x :=
    fun x => (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  have hint (t : SuzukiApertureInterval a.1) :
      IntervalIntegrable (deriv g) volume (-a.1) (t:ℝ) :=
    ((contDiff_infty_iff_deriv.mp hg).2.continuous).intervalIntegrable _ _
  have hz := (ae_restrict_iff' measurableSet_Icc).mp
    (derivative_zeroExtend_inside a g hg hc)
  filter_upwards [suzukiAperturePrimitive_coeFn a.1
    (suzukiSmoothDerivativeCoordinate a g hg hc)] with t ht
  rw [ht, suzukiAperturePrefix_eq_intervalIntegral]
  calc
    (∫ x in (-a.1)..(t:ℝ), suzukiApertureZeroExtend
        (suzukiSmoothDerivativeCoordinate a g hg hc) x) =
      ∫ x in (-a.1)..(t:ℝ), deriv g x := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hz] with x hx hxt
        rw [uIoc_of_le t.property.1] at hxt
        exact hx ⟨hxt.1.le, hxt.2.trans t.property.2⟩
    _ = g (t:ℝ) - g (-a.1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hint t)

def ccmSharpSmoothFormLift (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    CCMArchimedeanFormDomain a :=
  suzukiAperturePrimitiveCCMFormVector a (suzukiSmoothDerivativeCoordinate a g hg hc) +
    g (-a.1) • ccmPolarFormVector a 0

theorem memLp_ccmArchimedeanMultiplierProfile_sharpSmooth
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    MemLp (ccmArchimedeanMultiplierProfile (ccmSharpSmoothFormLift a g hg hc).1) 2 volume := by
  have h1 := memLp_ccmArchimedeanMultiplierProfile_primitiveCCMFormVector a
    (suzukiSmoothDerivativeCoordinate a g hg hc)
  have h2 := (memLp_ccmArchimedeanMultiplierProfile_polar a 0).const_smul (g (-a.1))
  apply (h1.add h2).ae_eq
  have ha := (Lp.coeFn_add
    (suzukiAperturePrimitiveCCMFormVector a (suzukiSmoothDerivativeCoordinate a g hg hc)).1
    (g (-a.1) • (ccmPolarFormVector a 0).1)).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hs := (Lp.coeFn_smul (g (-a.1)) (ccmPolarFormVector a 0).1).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  filter_upwards [ha, hs] with ξ haξ hsξ
  symm
  change (ccmArchimedeanFormWeight ξ:ℂ) *
    (((suzukiAperturePrimitiveCCMFormVector a
      (suzukiSmoothDerivativeCoordinate a g hg hc)).1 +
        g (-a.1) • (ccmPolarFormVector a 0).1) ξ) = _
  rw [haξ]
  simp only [Pi.add_apply]
  rw [hsξ]
  simp only [ccmArchimedeanMultiplierProfile, Pi.smul_apply, smul_eq_mul]
  ring

theorem ccmSharpSmoothFormLift_physical
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ((ccmArchimedeanFormToAperture a (ccmSharpSmoothFormLift a g hg hc) : SoninL2) :
      ℝ → ℂ) =ᵐ[volume] (Icc (-a.1) a.1).indicator g := by
  let d := suzukiSmoothDerivativeCoordinate a g hg hc
  let p := suzukiAperturePrimitive a.1 d
  have hprim : suzukiApertureZeroExtend p =ᵐ[volume]
      (Icc (-a.1) a.1).indicator (fun x => g x - g (-a.1)) := by
    apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
    · rw [ae_restrict_iff_subtype measurableSet_Icc]
      filter_upwards [suzukiApertureRepresentative_ae p,
        suzukiAperturePrimitive_smoothDerivativeCoordinate_boundary a g hg hc]
          with x hx hp
      rw [suzukiApertureZeroExtend_apply, hx, Set.indicator_of_mem x.property]
      exact hp
    · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc.compl] with x hx
      rw [suzukiApertureZeroExtend_eq_zero_of_notMem p hx, Set.indicator_of_notMem hx]
  have hphys : (ccmArchimedeanFormToAperture a (ccmSharpSmoothFormLift a g hg hc) : SoninL2) =
      suzukiApertureZeroExtendL2 p + g (-a.1) • ccmPolarL2Vector a 0 := by
    rw [ccmSharpSmoothFormLift, map_add, map_smul,
      ccmArchimedeanFormToAperture_primitiveCCMFormVector,
      ccmArchimedeanFormToAperture_polar]
    rfl
  rw [hphys]
  filter_upwards [Lp.coeFn_add (suzukiApertureZeroExtendL2 p)
    (g (-a.1) • ccmPolarL2Vector a 0),
    Lp.coeFn_smul (g (-a.1)) (ccmPolarL2Vector a 0),
    suzukiApertureZeroExtendL2_coeFn p, hprim, ccmPolarL2Vector_coeFn a 0]
      with x hadd hsmul hp he hpol
  rw [hadd]
  change suzukiApertureZeroExtendL2 p x +
    (g (-a.1) • ccmPolarL2Vector a 0 : SoninL2) x = _
  rw [hsmul, hp, he]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hpol]
  by_cases hx : x ∈ Icc (-a.1) a.1
  · simp only [centralInterval, Set.indicator_of_mem hx, ccmPolarProfile, zero_mul,
      Real.exp_zero, Complex.ofReal_one, mul_one]
    ring
  · simp [centralInterval, hx]

end RHTower
