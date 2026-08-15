import GaloisForLFunctions.HTGeometry.CarlemanWeightedStrip
import GaloisForLFunctions.HTGeometry.CompactHyperplanePerturbation
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts
import GaloisForLFunctions.HTGeometry.DenseCoreHyperplane
import GaloisForLFunctions.HTGeometry.WeakDerivativeConstant
import GaloisForLFunctions.RHTower.SuzukiTaSmoothCore
import GaloisForLFunctions.RHTower.SuzukiFriedrichsExtension

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiTaExponentialContinuous (a : SuzukiPositiveAperture) (ε : ℝ) :
    C(SuzukiApertureInterval a.1, ℂ) where
  toFun x := (Real.exp (ε * (x : ℝ)) : ℂ)
  continuous_toFun := by fun_prop

def suzukiTaExponentialL2 (a : SuzukiPositiveAperture) (ε : ℝ) :
    SuzukiApertureIntervalL2 a.1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiTaExponentialContinuous a ε)

def suzukiTaMoment (a : SuzukiPositiveAperture) (ε : ℝ) :
    SuzukiTaHilbert a →L[ℂ] ℂ :=
  (innerSL ℂ (suzukiTaExponentialL2 a ε)).comp (suzukiTaPhysicalEmbedding a)

theorem suzukiTaPhysicalEmbedding_smoothCore_ae
    (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a u) :
      SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
        fun x => u (x : ℝ) := by
  change (suzukiWeilIntervalFormEmbedding a
      (suzukiTaSmoothCoreToSource a u).toCCMFormVector :
        SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  rw [suzukiWeilIntervalFormEmbedding_complexSmooth]
  let test : SoninL2 := suzukiComplexTestL2 u u.contDiff u.hasCompactSupport
  have htest : (fun x : SuzukiApertureInterval a.1 => test (x : ℝ)) =ᵐ[volume]
      fun x => u (x : ℝ) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp
      (ae_restrict_of_ae (suzukiComplexTestL2_coeFn u u.contDiff u.hasCompactSupport))
  exact (suzukiApertureRestrictL2_coeFn a.1 test).trans
    ((suzukiApertureRestrictRepresentative_ae a.1 test).trans htest)

theorem suzukiTaMoment_smoothCore_eq_subtypeIntegral
    (a : SuzukiPositiveAperture) (ε : ℝ) (u : SuzukiTaSmoothCore a) :
    suzukiTaMoment a ε (suzukiTaSmoothCoreToHilbert a u) =
      ∫ x : SuzukiApertureInterval a.1,
        (Real.exp (ε * (x : ℝ)) : ℂ) * u (x : ℝ) := by
  rw [suzukiTaMoment, ContinuousLinearMap.comp_apply]
  change inner ℂ (suzukiTaExponentialL2 a ε)
      (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a u)) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaExponentialContinuous a ε),
    suzukiTaPhysicalEmbedding_smoothCore_ae a u] with x hw hu
  have hw' : (suzukiTaExponentialL2 a ε : SuzukiApertureInterval a.1 → ℂ) x =
      (Real.exp (ε * (x : ℝ)) : ℂ) := by
    simpa [suzukiTaExponentialL2, suzukiTaExponentialContinuous] using hw
  rw [hw', hu, RCLike.inner_apply]
  change u (x : ℝ) * (starRingEnd ℂ) (Complex.ofReal (Real.exp (ε * (x : ℝ)))) =
    Complex.ofReal (Real.exp (ε * (x : ℝ))) * u (x : ℝ)
  rw [Complex.conj_ofReal]
  exact mul_comm _ _

theorem suzukiTaMoment_smoothCore_eq_integral
    (a : SuzukiPositiveAperture) (ε : ℝ) (u : SuzukiTaSmoothCore a) :
    suzukiTaMoment a ε (suzukiTaSmoothCoreToHilbert a u) =
      ∫ x : ℝ, (Real.exp (ε * x) : ℂ) * u x := by
  rw [suzukiTaMoment_smoothCore_eq_subtypeIntegral]
  calc
    (∫ x : SuzukiApertureInterval a.1,
        (Real.exp (ε * (x : ℝ)) : ℂ) * u (x : ℝ)) =
        ∫ x in Icc (-a.1) a.1, (Real.exp (ε * x) : ℂ) * u x :=
      by
        simpa only [SuzukiApertureInterval] using
          (MeasureTheory.integral_subtype measurableSet_Icc
            (fun x : ℝ => (Real.exp (ε * x) : ℂ) * u x))
    _ = ∫ x : ℝ, (Real.exp (ε * x) : ℂ) * u x := by
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxt : x ∉ tsupport (u : ℝ → ℂ) := by
        intro hmem
        exact hx (Ioo_subset_Icc_self (u.tsupport_subset hmem))
      rw [image_eq_zero_of_notMem_tsupport hxt, mul_zero]

def suzukiTaUnitIntegralBump (a : SuzukiPositiveAperture) : ℝ → ℝ :=
  Classical.choose (exists_test_integral_one (a := -a.1) (b := a.1) (by linarith [a.2]))

theorem suzukiTaUnitIntegralBump_smooth (a : SuzukiPositiveAperture) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiTaUnitIntegralBump a) :=
  (Classical.choose_spec
    (exists_test_integral_one (a := -a.1) (b := a.1) (by linarith [a.2]))).1

theorem suzukiTaUnitIntegralBump_compact (a : SuzukiPositiveAperture) :
    HasCompactSupport (suzukiTaUnitIntegralBump a) :=
  (Classical.choose_spec
    (exists_test_integral_one (a := -a.1) (b := a.1) (by linarith [a.2]))).2.1

theorem suzukiTaUnitIntegralBump_tsupport (a : SuzukiPositiveAperture) :
    tsupport (suzukiTaUnitIntegralBump a) ⊆ Ioo (-a.1) a.1 :=
  (Classical.choose_spec
    (exists_test_integral_one (a := -a.1) (b := a.1) (by linarith [a.2]))).2.2.1

theorem integral_suzukiTaUnitIntegralBump (a : SuzukiPositiveAperture) :
    (∫ x : ℝ, suzukiTaUnitIntegralBump a x) = 1 :=
  (Classical.choose_spec
    (exists_test_integral_one (a := -a.1) (b := a.1) (by linarith [a.2]))).2.2.2

def suzukiTaMomentNormalizer (a : SuzukiPositiveAperture) (ε : ℝ) :
    SuzukiTaSmoothCore a where
  toFun x := (Real.exp (-ε * x) : ℂ) * (suzukiTaUnitIntegralBump a x : ℂ)
  contDiff' := by
    have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-ε * x)) := by
      fun_prop
    have hreal : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => Real.exp (-ε * x) * suzukiTaUnitIntegralBump a x) := by
      exact hexp.mul (suzukiTaUnitIntegralBump_smooth a)
    convert Complex.ofRealCLM.contDiff.comp hreal using 1
    funext x
    simp
  hasCompactSupport' := by
    refine HasCompactSupport.intro (suzukiTaUnitIntegralBump_compact a) ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  tsupport_subset' := by
    refine (closure_minimal ?_ (isClosed_tsupport (suzukiTaUnitIntegralBump a))).trans
      (suzukiTaUnitIntegralBump_tsupport a)
    intro x hx
    apply subset_closure
    intro hb
    exact hx (by simp [hb])

@[simp] theorem suzukiTaMomentNormalizer_apply
    (a : SuzukiPositiveAperture) (ε x : ℝ) :
    suzukiTaMomentNormalizer a ε x =
      (Real.exp (-ε * x) : ℂ) * (suzukiTaUnitIntegralBump a x : ℂ) := rfl

theorem suzukiTaMoment_normalizer
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    suzukiTaMoment a ε
      (suzukiTaSmoothCoreToHilbert a (suzukiTaMomentNormalizer a ε)) = 1 := by
  rw [suzukiTaMoment_smoothCore_eq_integral]
  have hfun : (fun x : ℝ =>
      (Real.exp (ε * x) : ℂ) * suzukiTaMomentNormalizer a ε x) =
      fun x => (suzukiTaUnitIntegralBump a x : ℂ) := by
    funext x
    rw [suzukiTaMomentNormalizer_apply]
    norm_cast
    rw [← mul_assoc, ← Real.exp_add]
    have : ε * x + -ε * x = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  have hi : (∫ x : ℝ, (suzukiTaUnitIntegralBump a x : ℂ)) =
      Complex.ofReal (∫ x : ℝ, suzukiTaUnitIntegralBump a x) := by
    exact integral_ofReal (𝕜 := ℂ)
  rw [hfun, hi, integral_suzukiTaUnitIntegralBump]
  norm_num

/-- Native shifted differential expression `i(d/dx + ε)` on Suzuki's smooth core. -/
def suzukiTaSmoothCoreShift (a : SuzukiPositiveAperture) (ε : ℝ) :
    SuzukiTaSmoothCore a →ₗ[ℂ] SuzukiTaSmoothCore a :=
  suzukiTaSmoothCoreIDeriv a +
    (((ε : ℂ) * I) • LinearMap.id)

@[simp] theorem suzukiTaSmoothCoreShift_apply
    (a : SuzukiPositiveAperture) (ε : ℝ) (u : SuzukiTaSmoothCore a) (x : ℝ) :
    suzukiTaSmoothCoreShift a ε u x =
      I * deriv u x + ((ε : ℂ) * I) * u x := by
  simp [suzukiTaSmoothCoreShift, suzukiTaSmoothCoreIDeriv_apply]

/-- Shifted smooth-core range in the energy Hilbert space. -/
def suzukiTaSmoothCoreShiftToHilbert (a : SuzukiPositiveAperture) (ε : ℝ) :
    SuzukiTaSmoothCore a →ₗ[ℂ] SuzukiTaHilbert a :=
  (suzukiTaSmoothCoreToHilbert a).comp (suzukiTaSmoothCoreShift a ε)

theorem suzukiTaMoment_shift_eq_zero
    (a : SuzukiPositiveAperture) (ε : ℝ) (u : SuzukiTaSmoothCore a) :
    suzukiTaMoment a ε (suzukiTaSmoothCoreShiftToHilbert a ε u) = 0 := by
  rw [suzukiTaSmoothCoreShiftToHilbert, LinearMap.comp_apply,
    suzukiTaMoment_smoothCore_eq_integral]
  let F : ℝ → ℂ := carlemanConjugate ε u
  have hF : ContDiff ℝ 1 F := by
    change ContDiff ℝ 1
      (fun x : ℝ => Complex.ofReal (Real.exp (ε * x)) * u x)
    have hexp : ContDiff ℝ 1 (fun x : ℝ => Real.exp (ε * x)) := by
      fun_prop
    exact (Complex.ofRealCLM.contDiff.comp hexp).mul (u.contDiff.of_le (by simp))
  have hFc : HasCompactSupport F := by
    dsimp [F, carlemanConjugate]
    exact u.hasCompactSupport.mul_left
  have hzero : (∫ x : ℝ, deriv F x) = 0 :=
    integral_complex_deriv_eq_zero_of_hasCompactSupport hF hFc
  have hpoint : (fun x : ℝ =>
      (Real.exp (ε * x) : ℂ) * suzukiTaSmoothCoreShift a ε u x) =
      fun x => I * deriv F x := by
    funext x
    rw [suzukiTaSmoothCoreShift_apply]
    dsimp only [F]
    rw [deriv_carlemanConjugate (u.contDiff.differentiable (by simp))]
    push_cast
    ring
  rw [hpoint, integral_const_mul, hzero, mul_zero]

theorem exists_suzukiTaSmoothCore_supportRadius
    (a : SuzukiPositiveAperture) (g : SuzukiTaSmoothCore a) :
    ∃ r : ℝ, 0 ≤ r ∧ r < a.1 ∧ Function.support g ⊆ Ioo (-r) r := by
  by_cases hne : (tsupport (g : ℝ → ℂ)).Nonempty
  · obtain ⟨x, hx, hmax⟩ := g.hasCompactSupport.exists_isMaxOn hne
      continuous_abs.continuousOn
    have hxlt : |x| < a.1 := abs_lt.mpr (g.tsupport_subset hx)
    let r := (|x| + a.1) / 2
    have hr0 : 0 ≤ r := by
      dsimp only [r]
      linarith [abs_nonneg x, a.2]
    have hrlt : r < a.1 := by
      dsimp only [r]
      linarith
    refine ⟨r, hr0, hrlt, ?_⟩
    intro y hy
    have hyabs : |y| ≤ |x| := hmax (subset_closure hy)
    have hyabslt : |y| < r := by
      dsimp only [r]
      linarith
    exact abs_lt.mp hyabslt
  · refine ⟨0, le_rfl, a.2, ?_⟩
    intro y hy
    exact False.elim (hne ⟨y, subset_closure hy⟩)

def suzukiTaSmoothCoreSupportRadius
    (a : SuzukiPositiveAperture) (g : SuzukiTaSmoothCore a) : ℝ :=
  Classical.choose (exists_suzukiTaSmoothCore_supportRadius a g)

theorem suzukiTaSmoothCoreSupportRadius_nonneg
    (a : SuzukiPositiveAperture) (g : SuzukiTaSmoothCore a) :
    0 ≤ suzukiTaSmoothCoreSupportRadius a g :=
  (Classical.choose_spec (exists_suzukiTaSmoothCore_supportRadius a g)).1

theorem suzukiTaSmoothCoreSupportRadius_lt
    (a : SuzukiPositiveAperture) (g : SuzukiTaSmoothCore a) :
    suzukiTaSmoothCoreSupportRadius a g < a.1 :=
  (Classical.choose_spec (exists_suzukiTaSmoothCore_supportRadius a g)).2.1

theorem suzukiTaSmoothCore_support_subset_radius
    (a : SuzukiPositiveAperture) (g : SuzukiTaSmoothCore a) :
    Function.support g ⊆
      Ioo (-suzukiTaSmoothCoreSupportRadius a g) (suzukiTaSmoothCoreSupportRadius a g) :=
  (Classical.choose_spec (exists_suzukiTaSmoothCore_supportRadius a g)).2.2

def suzukiTaWeightedCore (ε : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  carlemanConjugate ε g

theorem contDiff_suzukiTaWeightedCore
    (ε : ℝ) {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiTaWeightedCore ε g) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : ℝ => Complex.ofReal (Real.exp (ε * x)) * g x)
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (ε * x)) := by
    fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hexp).mul hg

theorem suzukiTaWeightedCore_support_subset
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a) :
    Function.support (suzukiTaWeightedCore ε g) ⊆
      Ioo (-suzukiTaSmoothCoreSupportRadius a g) (suzukiTaSmoothCoreSupportRadius a g) := by
  intro x hx
  apply suzukiTaSmoothCore_support_subset_radius a g
  intro hg
  exact hx (by simp [suzukiTaWeightedCore, carlemanConjugate, hg])

def suzukiTaWeightedPrimitive
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a) : ℝ → ℂ :=
  suzukiSmoothIntegralPrimitive (suzukiTaSmoothCoreSupportRadius a g)
    (suzukiTaWeightedCore ε g)

theorem contDiff_suzukiTaWeightedPrimitive
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiTaWeightedPrimitive a ε g) :=
  contDiff_suzukiSmoothIntegralPrimitive _ _
    (contDiff_suzukiTaWeightedCore ε g.contDiff)

theorem deriv_suzukiTaWeightedPrimitive
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a) (x : ℝ) :
    deriv (suzukiTaWeightedPrimitive a ε g) x = suzukiTaWeightedCore ε g x :=
  deriv_suzukiSmoothIntegralPrimitive _ _
    (contDiff_suzukiTaWeightedCore ε g.contDiff).continuous x

def suzukiTaShiftedPrimitiveSolution
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a)
    (hzero : (∫ x : ℝ, suzukiTaWeightedCore ε g x) = 0) :
    SuzukiTaSmoothCore a where
  toFun x := -I * carlemanConjugate (-ε) (suzukiTaWeightedPrimitive a ε g) x
  contDiff' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ =>
      -I * (Complex.ofReal (Real.exp (-ε * x)) * suzukiTaWeightedPrimitive a ε g x))
    have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-ε * x)) := by
      fun_prop
    exact contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp hexp).mul
      (contDiff_suzukiTaWeightedPrimitive a ε g))
  hasCompactSupport' := by
    have hp := hasCompactSupport_suzukiSmoothIntegralPrimitive
      (suzukiTaWeightedCore_support_subset a ε g) hzero
    exact hp.mul_left.mul_left
  tsupport_subset' := by
    let p : ℝ → ℂ := suzukiTaWeightedPrimitive a ε g
    have hp : tsupport p ⊆
        Icc (-suzukiTaSmoothCoreSupportRadius a g)
          (suzukiTaSmoothCoreSupportRadius a g) :=
      tsupport_suzukiSmoothIntegralPrimitive_subset
        (suzukiTaWeightedCore_support_subset a ε g) hzero
    have hsol : tsupport (fun x : ℝ =>
        -I * carlemanConjugate (-ε) p x) ⊆ tsupport p := by
      apply closure_minimal
      · intro x hx
        apply subset_closure
        intro hp0
        exact hx (by simp [carlemanConjugate, hp0])
      · exact isClosed_tsupport p
    intro x hx
    have hi := hp (hsol hx)
    exact ⟨lt_of_lt_of_le (neg_lt_neg (suzukiTaSmoothCoreSupportRadius_lt a g)) hi.1,
      lt_of_le_of_lt hi.2 (suzukiTaSmoothCoreSupportRadius_lt a g)⟩

@[simp] theorem suzukiTaShiftedPrimitiveSolution_apply
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a)
    (hzero : (∫ x : ℝ, suzukiTaWeightedCore ε g x) = 0) (x : ℝ) :
    suzukiTaShiftedPrimitiveSolution a ε g hzero x =
      -I * carlemanConjugate (-ε) (suzukiTaWeightedPrimitive a ε g) x := rfl

theorem suzukiTaSmoothCoreShift_solution
    (a : SuzukiPositiveAperture) (ε : ℝ) (g : SuzukiTaSmoothCore a)
    (hzero : (∫ x : ℝ, suzukiTaWeightedCore ε g x) = 0) :
    suzukiTaSmoothCoreShift a ε
      (suzukiTaShiftedPrimitiveSolution a ε g hzero) = g := by
  apply DFunLike.coe_injective
  funext x
  rw [suzukiTaSmoothCoreShift_apply]
  let p : ℝ → ℂ := suzukiTaWeightedPrimitive a ε g
  have hpDiff : Differentiable ℝ p :=
    (contDiff_suzukiTaWeightedPrimitive a ε g).differentiable (by simp)
  have hcar := hasDerivAt_carlemanConjugate (σ := -ε) hpDiff x
  have hsol := hcar.const_mul (-I)
  have hderiv : deriv (suzukiTaShiftedPrimitiveSolution a ε g hzero) x =
      -I * ((((-ε) * Real.exp ((-ε) * x) : ℝ) : ℂ) * p x +
        (Real.exp ((-ε) * x) : ℂ) * deriv p x) := by
    change deriv (fun y : ℝ => -I * carlemanConjugate (-ε) p y) x = _
    exact hsol.deriv
  rw [hderiv, suzukiTaShiftedPrimitiveSolution_apply]
  change I *
      (-I * ((((-ε) * Real.exp ((-ε) * x) : ℝ) : ℂ) * p x +
        (Real.exp ((-ε) * x) : ℂ) * deriv p x)) +
      ((ε : ℂ) * I) *
        (-I * ((Real.exp ((-ε) * x) : ℂ) * p x)) = g x
  rw [show deriv p x = suzukiTaWeightedCore ε g x from
    deriv_suzukiTaWeightedPrimitive a ε g x]
  change I *
      (-I * ((((-ε) * Real.exp ((-ε) * x) : ℝ) : ℂ) * p x +
        (Real.exp ((-ε) * x) : ℂ) *
          ((Real.exp (ε * x) : ℂ) * g x))) +
      ((ε : ℂ) * I) *
        (-I * ((Real.exp ((-ε) * x) : ℂ) * p x)) = g x
  have hexp : Real.exp ((-ε) * x) * Real.exp (ε * x) = 1 := by
    rw [← Real.exp_add]
    have : (-ε) * x + ε * x = 0 := by ring
    rw [this, Real.exp_zero]
  have hexpC : (Real.exp (-(ε * x)) : ℂ) * (Real.exp (ε * x) : ℂ) = 1 := by
    norm_cast
    rw [← Real.exp_add]
    simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  rw [hexpC]
  push_cast
  ring

theorem range_suzukiTaSmoothCoreShiftToHilbert_eq_correction
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    LinearMap.range (suzukiTaSmoothCoreShiftToHilbert a ε) =
      LinearMap.range
        (DenseCoreHyperplane.correction
          (suzukiTaSmoothCoreToHilbert a) (suzukiTaMoment a ε)
          (suzukiTaMomentNormalizer a ε)) := by
  let J := suzukiTaSmoothCoreToHilbert a
  let L := suzukiTaMoment a ε
  let q := suzukiTaMomentNormalizer a ε
  have hq : L (J q) = 1 := suzukiTaMoment_normalizer a ε
  rw [DenseCoreHyperplane.range_correction_eq J L q hq]
  apply le_antisymm
  · rintro y ⟨u, rfl⟩
    constructor
    · exact ⟨suzukiTaSmoothCoreShift a ε u, rfl⟩
    · change L (suzukiTaSmoothCoreShiftToHilbert a ε u) = 0
      exact suzukiTaMoment_shift_eq_zero a ε u
  · rintro y ⟨⟨g, hg⟩, hLg⟩
    change L y = 0 at hLg
    have hLJg : L (J g) = 0 := by rw [hg]; exact hLg
    have hzero : (∫ x : ℝ, suzukiTaWeightedCore ε g x) = 0 := by
      change (∫ x : ℝ, (Real.exp (ε * x) : ℂ) * g x) = 0
      rw [← suzukiTaMoment_smoothCore_eq_integral a ε g]
      exact hLJg
    refine ⟨suzukiTaShiftedPrimitiveSolution a ε g hzero, ?_⟩
    change J (suzukiTaSmoothCoreShift a ε
      (suzukiTaShiftedPrimitiveSolution a ε g hzero)) = y
    rw [suzukiTaSmoothCoreShift_solution]
    exact hg

/-- Exact repair of Suzuki's shifted-range closure: no adjoint regularity is assumed. -/
theorem topologicalClosure_range_suzukiTaSmoothCoreShiftToHilbert
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    (LinearMap.range (suzukiTaSmoothCoreShiftToHilbert a ε)).topologicalClosure =
      LinearMap.ker (suzukiTaMoment a ε).toLinearMap := by
  rw [range_suzukiTaSmoothCoreShiftToHilbert_eq_correction]
  exact DenseCoreHyperplane.topologicalClosure_range_correction_eq_ker
    (suzukiTaSmoothCoreToHilbert a) (suzukiTaMoment a ε)
    (suzukiTaMomentNormalizer a ε) (suzukiTaMoment_normalizer a ε)
    (denseRange_suzukiTaSmoothCoreToHilbert a)

/-- The smooth Suzuki core, identified with its concrete dense range in the energy space. -/
noncomputable def suzukiTaSmoothCoreEquivRange (a : SuzukiPositiveAperture) :
    SuzukiTaSmoothCore a ≃ₗ[ℂ]
      LinearMap.range (suzukiTaSmoothCoreToHilbert a) :=
  LinearEquiv.ofInjective (suzukiTaSmoothCoreToHilbert a)
    (suzukiTaSmoothCoreToHilbert_injective a)

/-- The shifted Suzuki derivative `i d/dx + ε i` as a densely defined operator on the
energy Hilbert space. -/
noncomputable def suzukiTaShiftedDerivativePMap
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    SuzukiTaHilbert a →ₗ.[ℂ] SuzukiTaHilbert a where
  domain := LinearMap.range (suzukiTaSmoothCoreToHilbert a)
  toFun := (suzukiTaSmoothCoreShiftToHilbert a ε).comp
    (suzukiTaSmoothCoreEquivRange a).symm.toLinearMap

theorem suzukiTaShiftedDerivativePMap_apply
    (a : SuzukiPositiveAperture) (ε : ℝ) (u : SuzukiTaSmoothCore a) :
    suzukiTaShiftedDerivativePMap a ε
      ((suzukiTaSmoothCoreEquivRange a) u) =
        suzukiTaSmoothCoreShiftToHilbert a ε u := by
  change suzukiTaSmoothCoreShiftToHilbert a ε
      ((suzukiTaSmoothCoreEquivRange a).symm
        ((suzukiTaSmoothCoreEquivRange a) u)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem dense_suzukiTaShiftedDerivativePMap_domain
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    Dense ((suzukiTaShiftedDerivativePMap a ε).domain :
      Set (SuzukiTaHilbert a)) := by
  change Dense (LinearMap.range (suzukiTaSmoothCoreToHilbert a) :
    Set (SuzukiTaHilbert a))
  exact denseRange_suzukiTaSmoothCoreToHilbert a

theorem suzukiTaShiftedDerivativePMap_rangeSubmodule
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    (suzukiTaShiftedDerivativePMap a ε).rangeSubmodule =
      LinearMap.range (suzukiTaSmoothCoreShiftToHilbert a ε) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(suzukiTaSmoothCoreEquivRange a).symm x, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨(suzukiTaSmoothCoreEquivRange a) u, ?_⟩
    exact suzukiTaShiftedDerivativePMap_apply a ε u

/-- The adjoint kernel of the shifted derivative is the orthogonal complement of the concrete
moment hyperplane. -/
theorem suzukiTaShiftedDerivativePMap_adjoint_kernel_eq_moment_orthogonal
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    (suzukiTaShiftedDerivativePMap a ε).adjoint.kernel =
      (LinearMap.ker (suzukiTaMoment a ε).toLinearMap)ᗮ := by
  rw [LinearPMap.adjoint_kernel_eq_orthogonal_range
    (suzukiTaShiftedDerivativePMap a ε)
      (dense_suzukiTaShiftedDerivativePMap_domain a ε)]
  rw [suzukiTaShiftedDerivativePMap_rangeSubmodule]
  rw [← Submodule.orthogonal_closure]
  rw [topologicalClosure_range_suzukiTaSmoothCoreShiftToHilbert]

theorem suzukiTaMoment_adjoint_one_ne_zero
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    (suzukiTaMoment a ε).adjoint (1 : ℂ) ≠ 0 := by
  intro hzero
  have hinner := (suzukiTaMoment a ε).adjoint_inner_left
    (suzukiTaSmoothCoreToHilbert a (suzukiTaMomentNormalizer a ε)) (1 : ℂ)
  rw [hzero, suzukiTaMoment_normalizer a ε] at hinner
  simp at hinner

theorem suzukiTaMoment_adjoint_range_eq_span
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    LinearMap.range (suzukiTaMoment a ε).adjoint.toLinearMap =
      ℂ ∙ (suzukiTaMoment a ε).adjoint (1 : ℂ) := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    simpa using ((suzukiTaMoment a ε).adjoint.map_smul c (1 : ℂ)).symm
  · rw [Submodule.mem_span_singleton]
    rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simpa using ((suzukiTaMoment a ε).adjoint.map_smul c (1 : ℂ))

theorem suzukiTaMoment_kernel_orthogonal_eq_span
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    (LinearMap.ker (suzukiTaMoment a ε).toLinearMap)ᗮ =
      ℂ ∙ (suzukiTaMoment a ε).adjoint (1 : ℂ) := by
  change (suzukiTaMoment a ε).kerᗮ = _
  rw [(suzukiTaMoment a ε).orthogonal_ker]
  rw [suzukiTaMoment_adjoint_range_eq_span]
  have hclosed : IsClosed
      (ℂ ∙ (suzukiTaMoment a ε).adjoint (1 : ℂ) :
        Set (SuzukiTaHilbert a)) :=
    (ℂ ∙ (suzukiTaMoment a ε).adjoint (1 : ℂ)).closed_of_finiteDimensional
  exact hclosed.submodule_topologicalClosure_eq

/-- Exact one-dimensional adjoint kernel for every real shift.  In particular, the two
deficiency shifts `ε = ±1` both have dimension one. -/
theorem finrank_suzukiTaShiftedDerivativePMap_adjoint_kernel
    (a : SuzukiPositiveAperture) (ε : ℝ) :
    Module.finrank ℂ (suzukiTaShiftedDerivativePMap a ε).adjoint.kernel = 1 := by
  rw [suzukiTaShiftedDerivativePMap_adjoint_kernel_eq_moment_orthogonal]
  rw [suzukiTaMoment_kernel_orthogonal_eq_span]
  exact finrank_span_singleton (suzukiTaMoment_adjoint_one_ne_zero a ε)

/-- Suzuki's two shifted-adjoint deficiency dimensions are `(1,1)`. -/
theorem suzukiTaShiftedDerivativePMap_deficiencyIndices
    (a : SuzukiPositiveAperture) :
    Module.finrank ℂ (suzukiTaShiftedDerivativePMap a 1).adjoint.kernel = 1 ∧
      Module.finrank ℂ (suzukiTaShiftedDerivativePMap a (-1)).adjoint.kernel = 1 :=
  ⟨finrank_suzukiTaShiftedDerivativePMap_adjoint_kernel a 1,
    finrank_suzukiTaShiftedDerivativePMap_adjoint_kernel a (-1)⟩

end RHTower
