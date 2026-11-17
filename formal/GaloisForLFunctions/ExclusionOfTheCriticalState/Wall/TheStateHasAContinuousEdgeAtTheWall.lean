import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheStateSolvesALogarithmicEquationAtTheWall
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowSolutionsAreBounded
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsMixedJumpPairing
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.BoundedLipschitzCutoffsPreserveLogarithmicEnergy
import GaloisForLFunctions.RHTower.SoninCarrierApertureChain
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilActualHeadCompletedErrorProducer

/-!
# The state has a continuous edge at the wall

Reflect the collar \`[−½, 0]\` onto the window \`[−¼, ¼]\` by \`x ↦ −¼ − x\` (\`wallReflect\`). The cut state
\`U = χF\` becomes a window function \`u\`, and the bounded forcing of the logarithmic equation at the
wall (\`criticalState_logarithmic_equation_at_wall\`) becomes a bounded window forcing \`g\`. Every
finite-energy window function \`f\` splits into a real and an imaginary wall test, and the
logarithmic full form is conjugate linear in \`f\`, so \`u\` solves the window equation

  \`E(f, u) = ⟨f, g⟩\`   for every finite-energy \`f\` supported in \`[−¼, ¼]\`.

The left edge of the window is the wall. The window edge theorem (\`left_edge_of_bounded\`) gives:

**Theorem** (\`criticalState_exists_continuous_edge\`). There is a continuous \`Φ\` with \`F(−s) = Φ(s)\` for
almost every \`s ∈ (0, ¼)\`, and \`Φ(s) √log(1/s)\` has a limit as \`s → 0⁺\`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CanonicalSystemOfTheWindowTower
  CriticalHardyTheoryOfTheWindowCone HTGeometry _root_.RHTower

/-! ### The reflection onto the window -/

/-- The reflection \`x ↦ −¼ − x\`; it carries the collar \`[−½, 0]\` onto the window \`[−¼, ¼]\`. -/
def wallReflect (x : ℝ) : ℝ := -(1 / 4) - x

/-- The window of half-width \`¼\`. -/
def wallAperture : SuzukiPositiveAperture := ⟨1 / 4, by norm_num⟩

theorem wallReflect_wallReflect (x : ℝ) : wallReflect (wallReflect x) = x := by
  unfold wallReflect
  ring

theorem measurePreserving_wallReflect : MeasurePreserving wallReflect volume volume := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) (1 / 4)).comp
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  convert h using 1
  funext x
  simp only [Function.comp_apply, wallReflect]
  ring

theorem measurable_wallReflect : Measurable wallReflect := measurePreserving_wallReflect.measurable

theorem ae_comp_wallReflect {p : ℝ → Prop} (h : ∀ᵐ x, p x) : ∀ᵐ y, p (wallReflect y) :=
  measurePreserving_wallReflect.quasiMeasurePreserving.ae h

theorem ae_comp_add {p : ℝ → Prop} (h : ∀ᵐ x, p x) (t : ℝ) : ∀ᵐ y, p (y + t) :=
  (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae h

theorem integral_comp_wallReflect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ → E) : ∫ y, H (wallReflect y) = ∫ x, H x := by
  have h1 : (∫ y, H (-y - 1 / 4)) = ∫ y, H (y - 1 / 4) :=
    integral_neg_eq_self (fun y => H (y - 1 / 4)) volume
  have h2 := integral_sub_right_eq_self (μ := volume) H (1 / 4)
  rw [← h2, ← h1]
  congr 1
  funext y
  unfold wallReflect
  congr 1
  ring

theorem mem_Icc_wallReflect_iff {y : ℝ} :
    wallReflect y ∈ Icc (-(1 / 4 : ℝ)) (1 / 4) ↔ y ∈ Icc (-(1 / 2 : ℝ)) 0 := by
  unfold wallReflect
  simp only [mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Window functions in reflected coordinates -/

/-- The reflected complex lift \`x ↦ V(−¼ − x)\` of a real profile. -/
def wallLiftFun (V : ℝ → ℝ) (x : ℝ) : ℂ := (V (wallReflect x) : ℂ)

theorem memLp_wallLiftFun {V : ℝ → ℝ} (hV : MemLp V 2 volume) : MemLp (wallLiftFun V) 2 volume :=
  (hV.comp_measurePreserving measurePreserving_wallReflect).ofReal (K := ℂ)

/-- The reflected lift as an element of \`L²(ℝ)\`. -/
def wallLift (V : ℝ → ℝ) (hV : MemLp V 2 volume) : RealLineL2 :=
  (memLp_wallLiftFun hV).toLp (wallLiftFun V)

theorem wallLift_comp {V : ℝ → ℝ} (hV : MemLp V 2 volume) :
    ∀ᵐ y, (wallLift V hV : ℝ → ℂ) (wallReflect y) = (V y : ℂ) := by
  filter_upwards [ae_comp_wallReflect (MemLp.coeFn_toLp (memLp_wallLiftFun hV))] with y hy
  rw [wallLift, hy, wallLiftFun, wallReflect_wallReflect]

theorem wallLift_mem_aperture {V : ℝ → ℝ} (hV : MemLp V 2 volume)
    (hs : ∀ᵐ y, y ∉ Icc (-(1 / 2 : ℝ)) 0 → V y = 0) :
    wallLift V hV ∈ suzukiApertureHilbert wallAperture := by
  refine (mem_physicalForbidden_iff _ _ _).mpr ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_wallLiftFun hV), ae_comp_wallReflect hs] with x hx1 hx2 hx
  rw [wallLift, hx1, wallLiftFun, hx2 fun hm => hx ?_, Complex.ofReal_zero]
  have h := mem_Icc_wallReflect_iff.mpr hm
  rwa [wallReflect_wallReflect] at h

theorem wallLift_ae_norm_le {V : ℝ → ℝ} (hV : MemLp V 2 volume) {C : ℝ} (hC : ∀ᵐ y, |V y| ≤ C) :
    ∀ᵐ x, ‖(wallLift V hV : ℝ → ℂ) x‖ ≤ C := by
  filter_upwards [MemLp.coeFn_toLp (memLp_wallLiftFun hV),
    measurePreserving_wallReflect.quasiMeasurePreserving.ae hC] with x hx1 hx2
  rw [wallLift, hx1, wallLiftFun, Complex.norm_real, Real.norm_eq_abs]
  exact hx2

/-! ### Inner products and translation losses in reflected coordinates -/

theorem inner_eq_integral_wallReflect (f g : RealLineL2) :
    inner ℂ f g = ∫ y, conj (f (wallReflect y)) * g (wallReflect y) := by
  rw [L2.inner_def, ← integral_comp_wallReflect]
  simp only [RCLike.inner_apply']

theorem inner_translationLoss_eq (f g : RealLineL2) (t : ℝ) :
    inner ℂ (logTranslationCLM t f - f) (logTranslationCLM t g - g) =
      ∫ y, conj (f (wallReflect y) - f (wallReflect (y + t))) *
        (g (wallReflect y) - g (wallReflect (y + t))) := by
  have hf : ∀ᵐ x, (logTranslationCLM t f - f : RealLineL2) x = f (x + t) - f x := by
    filter_upwards [Lp.coeFn_sub (logTranslationCLM t f) f, logarithmicTranslation_coeFn t f]
      with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hg : ∀ᵐ x, (logTranslationCLM t g - g : RealLineL2) x = g (x + t) - g x := by
    filter_upwards [Lp.coeFn_sub (logTranslationCLM t g) g, logarithmicTranslation_coeFn t g]
      with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  let K : ℝ → ℂ := fun x => conj (f (x + t) - f x) * (g (x + t) - g x)
  calc inner ℂ (logTranslationCLM t f - f) (logTranslationCLM t g - g) = ∫ x, K x := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [hf, hg] with x h1 h2
        rw [h1, h2, RCLike.inner_apply']
    _ = ∫ y, K (wallReflect (y + t)) := by
        rw [integral_add_right_eq_self (fun y => K (wallReflect y)) t, integral_comp_wallReflect]
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [K]
        rw [show wallReflect (y + t) + t = wallReflect y by unfold wallReflect; ring]

theorem norm_sq_translationLoss_eq (f : RealLineL2) (t : ℝ) :
    ‖logTranslationCLM t f - f‖ ^ 2 =
      ∫ y, ‖f (wallReflect y) - f (wallReflect (y + t))‖ ^ 2 := by
  have h := inner_translationLoss_eq f f t
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : (∫ y, conj (f (wallReflect y) - f (wallReflect (y + t))) *
      (f (wallReflect y) - f (wallReflect (y + t)))) =
        ((∫ y, ‖f (wallReflect y) - f (wallReflect (y + t))‖ ^ 2 : ℝ) : ℂ) := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans integral_ofReal
    rw [mul_comm]
    exact_mod_cast Complex.mul_conj' _
  rw [h2] at h
  exact RCLike.ofReal_injective (K := ℂ) ((RCLike.ofReal_pow _ _).trans h)

/-- The translation loss of a reflected lift is the jump energy of the profile. -/
theorem norm_sq_translationLoss_wallLift {V : ℝ → ℝ} (hV : MemLp V 2 volume) (t : ℝ) :
    ‖logTranslationCLM t (wallLift V hV) - wallLift V hV‖ ^ 2 = ∫ y, (V y - V (y + t)) ^ 2 := by
  rw [norm_sq_translationLoss_eq]
  refine integral_congr_ae ?_
  filter_upwards [wallLift_comp hV, ae_comp_add (wallLift_comp hV) t] with y h1 h2
  rw [h1, h2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A reflected lift of a profile of the energy domain has finite logarithmic energy. -/
theorem hasLogarithmicEnergy_wallLift {V : ℝ → ℝ} (hV : CriticalHalfLineEnergyDomain V) :
    HasLogarithmicEnergy (wallLift V hV.memLp_real) := by
  rw [hasLogarithmicEnergy_iff_integrable_jump]
  refine Integrable.mono' hV.integrableOn_levyIntegrand
    (measurable_logReferenceLevyDensity.aestronglyMeasurable.mul
      (((continuous_logTranslationCLM _).sub continuous_const).aestronglyMeasurable.norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_sq_translationLoss_wallLift, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg ht0.le)
      (integral_nonneg fun y => sq_nonneg _))]
  refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun y => sq_nonneg _)
  have := archLogRemainder_nonneg ht0
  unfold archLogRemainder at this
  linarith

/-! ### Real and imaginary wall tests of a window function -/

/-- A component \`π\` of the reflected window function, cut to the collar. -/
def wallTestPart (π : ℂ → ℝ) (f : RealLineL2) : ℝ → ℝ :=
  (Ico (-(1 / 2 : ℝ)) 0).indicator fun y => π (f (wallReflect y))

theorem ae_wallReflect_eq_zero {f : RealLineL2} (hf : f ∈ suzukiApertureHilbert wallAperture) :
    ∀ᵐ y, y ∉ Ico (-(1 / 2 : ℝ)) 0 → f (wallReflect y) = 0 := by
  have h1 := ae_comp_wallReflect ((mem_physicalForbidden_iff _ _ f).mp hf)
  have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) := (Set.countable_singleton 0).ae_notMem volume
  filter_upwards [h1, h0] with y hy hy0 hm
  refine hy fun hc => hm ?_
  have hc' : y ∈ Icc (-(1 / 2 : ℝ)) 0 := mem_Icc_wallReflect_iff.mp hc
  exact ⟨hc'.1, lt_of_le_of_ne hc'.2 hy0⟩

theorem ae_wallTestPart_eq {π : ℂ → ℝ} (hπ0 : π 0 = 0) {f : RealLineL2}
    (hf : f ∈ suzukiApertureHilbert wallAperture) :
    ∀ᵐ y, wallTestPart π f y = π (f (wallReflect y)) := by
  filter_upwards [ae_wallReflect_eq_zero hf] with y hy
  by_cases hm : y ∈ Ico (-(1 / 2 : ℝ)) 0
  · rw [wallTestPart, indicator_of_mem hm]
  · rw [wallTestPart, indicator_of_notMem hm, hy hm, hπ0]

theorem ae_wallReflect_eq_re_add_im {f : RealLineL2} (hf : f ∈ suzukiApertureHilbert wallAperture) :
    ∀ᵐ y, f (wallReflect y) =
      (wallTestPart Complex.re f y : ℂ) + (wallTestPart Complex.im f y : ℂ) * I := by
  filter_upwards [ae_wallTestPart_eq (π := Complex.re) Complex.zero_re hf,
    ae_wallTestPart_eq (π := Complex.im) Complex.zero_im hf] with y h1 h2
  rw [h1, h2, Complex.re_add_im]

/-- **A component of a finite-energy window function is a wall test.** Its Lévy energy is bounded by
the logarithmic jump energy plus the bounded remainder kernel. -/
theorem isWallTest_wallTestPart {π : ℂ → ℝ} (hπ : Continuous π)
    (hπsub : ∀ z w, π (z - w) = π z - π w) (hπb : ∀ z, |π z| ≤ ‖z‖) {f : RealLineL2}
    (hf : f ∈ suzukiApertureHilbert wallAperture) (hfe : HasLogarithmicEnergy f) :
    IsWallTest (wallTestPart π f) := by
  have hπ0 : π 0 = 0 := by
    have h := hπsub 0 0
    simp only [sub_self] at h
    linarith
  have hfm : Measurable fun y => f (wallReflect y) :=
    (Lp.stronglyMeasurable f).measurable.comp measurable_wallReflect
  have hGm : Measurable (wallTestPart π f) := (hπ.measurable.comp hfm).indicator measurableSet_Ico
  have hvan : ∀ y, y ∉ Ico (-(1 / 2 : ℝ)) 0 → wallTestPart π f y = 0 := fun y hy =>
    indicator_of_notMem hy _
  have hfL : MemLp (fun y => f (wallReflect y)) 2 volume :=
    (Lp.memLp f).comp_measurePreserving measurePreserving_wallReflect
  have hf2 : Integrable fun y => ‖f (wallReflect y)‖ ^ 2 :=
    hfL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hGle : ∀ y, wallTestPart π f y ^ 2 ≤ ‖f (wallReflect y)‖ ^ 2 := by
    intro y
    by_cases hm : y ∈ Ico (-(1 / 2 : ℝ)) 0
    · rw [wallTestPart, indicator_of_mem hm, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hπb _) 2
    · rw [hvan y hm, zero_pow two_ne_zero]
      exact sq_nonneg _
  have hG2 : Integrable fun y => wallTestPart π f y ^ 2 :=
    hf2.mono' (hGm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hGle y)
  have hind : Integrable ((Ico (-(1 / 2 : ℝ)) 0).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const measure_Ico_lt_top.ne)
  have hG1 : Integrable (wallTestPart π f) := by
    refine (hG2.add hind).mono' hGm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    by_cases hm : y ∈ Ico (-(1 / 2 : ℝ)) 0
    · rw [Pi.add_apply, indicator_of_mem hm, Real.norm_eq_abs]
      nlinarith [sq_abs (wallTestPart π f y), sq_nonneg (|wallTestPart π f y| - 1 / 2)]
    · rw [Pi.add_apply, indicator_of_notMem hm, hvan y hm, norm_zero]
      norm_num
  have hexp : Integrable fun y => wallTestPart π f y ^ 2 * Real.exp (-(8 * y)) := by
    refine (hG2.const_mul (Real.exp 4)).mono' ((hGm.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    by_cases hm : y ∈ Ico (-(1 / 2 : ℝ)) 0
    · have he : Real.exp (-(8 * y)) ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith [hm.1])
      rw [mul_comm (Real.exp 4)]
      exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
    · rw [hvan y hm]
      simp
  have hsupp : ∀ u, 0 ≤ u → wallTestPart π f u = 0 := fun u hu =>
    hvan u fun hm => absurd hm.2 (not_lt.mpr hu)
  refine ⟨⟨hGm, hG1, hG2, hexp, hsupp, ?_⟩, fun x hx => hvan x fun hm => hx (Ico_subset_Icc_self hm)⟩
  refine integrable_gamma_of_lintegral_levy_ne_top hG1 hG2 ?_
  have hjump := (hasLogarithmicEnergy_iff_integrable_jump f).mp hfe
  set M : ℝ := ∫ u, wallTestPart π f u ^ 2 with hMdef
  have hB : IntegrableOn (fun x => logReferenceLevyDensity x * ‖logTranslationCLM x f - f‖ ^ 2 +
      4 * M * archLogRemainder x) (Ioi 0) :=
    hjump.add (integrableOn_archLogRemainder.const_mul (4 * M))
  have hM0 : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hle : ∀ x ∈ Ioi (0 : ℝ), archLevyDensity x *
      (∫ u, (wallTestPart π f u - wallTestPart π f (u + x)) ^ 2) ≤
        logReferenceLevyDensity x * ‖logTranslationCLM x f - f‖ ^ 2 +
          4 * M * archLogRemainder x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hGL : MemLp (wallTestPart π f) 2 volume :=
      (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr hG2
    have hΔ : Integrable fun u => (wallTestPart π f u - wallTestPart π f (u + x)) ^ 2 :=
      integrable_sq_of_memLp (hGL.sub (memLp_two_shift hGL x))
    have hfx : MemLp (fun y => f (wallReflect (y + x))) 2 volume :=
      hfL.comp_measurePreserving (measurePreserving_add_right volume x)
    have hΔf : Integrable fun y => ‖f (wallReflect y) - f (wallReflect (y + x))‖ ^ 2 :=
      (hfL.sub hfx).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have h1 : (∫ u, (wallTestPart π f u - wallTestPart π f (u + x)) ^ 2) ≤
        ‖logTranslationCLM x f - f‖ ^ 2 := by
      rw [norm_sq_translationLoss_eq]
      refine integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _) hΔf ?_
      filter_upwards [ae_wallTestPart_eq hπ0 hf, ae_comp_add (ae_wallTestPart_eq hπ0 hf) x]
        with y h1 h2
      rw [h1, h2, ← hπsub, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hπb _) 2
    have h2 : (∫ u, (wallTestPart π f u - wallTestPart π f (u + x)) ^ 2) ≤ 4 * M := by
      have hs := integrable_sq_of_memLp (memLp_two_shift hGL x)
      have hsI : (∫ u, wallTestPart π f (u + x) ^ 2) = M :=
        integral_add_right_eq_self (fun u => wallTestPart π f u ^ 2) x
      calc (∫ u, (wallTestPart π f u - wallTestPart π f (u + x)) ^ 2) ≤
            ∫ u, (2 * wallTestPart π f u ^ 2 + 2 * wallTestPart π f (u + x) ^ 2) :=
            integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
              ((hG2.const_mul 2).add (hs.const_mul 2)) (Eventually.of_forall fun u => by
                nlinarith [sq_nonneg (wallTestPart π f u + wallTestPart π f (u + x))])
        _ = 4 * M := by
            rw [integral_add (hG2.const_mul 2) (hs.const_mul 2), integral_const_mul,
              integral_const_mul, hsI]
            ring
    have hω : archLevyDensity x = logReferenceLevyDensity x + archLogRemainder x := by
      unfold archLogRemainder
      ring
    rw [hω, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 (logReferenceLevyDensity_nonneg hx0.le))
      (by rw [mul_comm (archLogRemainder x)]
          exact mul_le_mul_of_nonneg_right h2 (archLogRemainder_nonneg hx0))
  have hBnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x =>
      logReferenceLevyDensity x * ‖logTranslationCLM x f - f‖ ^ 2 + 4 * M * archLogRemainder x :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
      add_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg (le_of_lt hx)) (sq_nonneg _))
        (mul_nonneg (by positivity) (archLogRemainder_nonneg hx))
  refine (lt_of_le_of_lt (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono
    fun x hx => ENNReal.ofReal_le_ofReal (hle x hx))) ?_).ne
  rw [← ofReal_integral_eq_lintegral_ofReal hB hBnn]
  exact ENNReal.ofReal_lt_top

/-! ### The window equation of the cut state -/

theorem integral_ofReal_sub_I_mul {μ : Measure ℝ} {a b : ℝ → ℝ} (ha : Integrable a μ)
    (hb : Integrable b μ) :
    ∫ y, ((a y : ℂ) - I * (b y : ℂ)) ∂μ =
      ((∫ y, a y ∂μ : ℝ) : ℂ) - I * ((∫ y, b y ∂μ : ℝ) : ℂ) := by
  have ha' : Integrable (fun y => (a y : ℂ)) μ := ha.ofReal
  have hb' : Integrable (fun y => I * (b y : ℂ)) μ := hb.ofReal.const_mul I
  rw [integral_sub ha' hb', integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

theorem conj_ofReal_add_ofReal_mul_I (a b : ℝ) :
    conj ((a : ℂ) + (b : ℂ) * I) = (a : ℂ) - I * (b : ℂ) := by
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **The state has a continuous edge at the wall.** There is a continuous \`Φ\` equal to \`s ↦ F(−s)\`
almost everywhere on \`(0, ¼)\`, and \`Φ(s) √log(1/s)\` converges as \`s → 0⁺\`. -/
theorem criticalState_exists_continuous_edge {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ (∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) ∧
      ∃ ℓ : ℝ, Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC0, -, hb⟩ := criticalState_ae_abs_le hW ht hF
  obtain ⟨h, hhm, ⟨Cg, hCg⟩, hheq⟩ := criticalState_logarithmic_equation_at_wall hW ht hF
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ → ℝ, U = fun u => wallRamp u * F u := ⟨_, rfl⟩
  have hU : CriticalHalfLineEnergyDomain U := by
    subst hUdef
    exact criticalHalfLineEnergyDomain_lipschitz_mul hd measurable_wallRamp abs_wallRamp_le_one
      abs_wallRamp_sub_le
  have hUb : ∀ᵐ u, |U u| ≤ C := hb.mono fun u hu => by
    simp only [hUdef]
    rw [abs_mul]
    calc |wallRamp u| * |F u| ≤ 1 * C :=
          mul_le_mul (abs_wallRamp_le_one u) hu (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hUs : ∀ᵐ y, y ∉ Icc (-(1 / 2 : ℝ)) 0 → U y = 0 := Eventually.of_forall fun y hy => by
    simp only [hUdef]
    rcases not_and_or.mp (show ¬(-(1 / 2 : ℝ) ≤ y ∧ y ≤ 0) from hy) with h1 | h1
    · rw [wallRamp_of_le (by linarith), zero_mul]
    · rw [hF.2.2.2.2.2.1 y (by linarith), mul_zero]
  have hheqU : ∀ G, IsWallTest G → (∫ u, U u * G u) + ∫ x in Ioi 0, logReferenceLevyDensity x *
      ∫ u, (U u - U (u + x)) * (G u - G (u + x)) = ∫ y, G y * h y := by
    subst hUdef
    exact hheq
  have hUL := hU.memLp_real
  -- the window solution and its forcing
  set uL := wallLift U hUL with huLdef
  have huA : uL ∈ suzukiApertureHilbert wallAperture := wallLift_mem_aperture hUL hUs
  have hu : HasLogarithmicEnergy uL := hasLogarithmicEnergy_wallLift hU
  have hub : ∀ᵐ x, ‖(uL : ℝ → ℂ) x‖ ≤ C := wallLift_ae_norm_le hUL hUb
  have hUc := wallLift_comp hUL
  set gR : ℝ → ℝ := (Icc (-(1 / 2 : ℝ)) 0).indicator h with hgRdef
  have hgRb : ∀ᵐ y, |gR y| ≤ |Cg| := by
    filter_upwards [hCg] with y hy
    by_cases hm : y ∈ Icc (-(1 / 2 : ℝ)) 0
    · rw [hgRdef, indicator_of_mem hm]
      exact (hy hm).trans (le_abs_self _)
    · rw [hgRdef, indicator_of_notMem hm, abs_zero]
      exact abs_nonneg _
  have hgRL : MemLp gR 2 volume := by
    refine MemLp.of_le (memLp_indicator_const (s := Icc (-(1 / 2 : ℝ)) 0) 2 measurableSet_Icc
      (|Cg|) (Or.inr measure_Icc_lt_top.ne)) (hhm.indicator measurableSet_Icc) ?_
    filter_upwards [hgRb] with y hy
    by_cases hm : y ∈ Icc (-(1 / 2 : ℝ)) 0
    · rw [indicator_of_mem hm, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
      exact hy
    · simp only [hgRdef, indicator_of_notMem hm, norm_zero, le_refl]
  set gL := wallLift gR hgRL with hgLdef
  have hgA : gL ∈ suzukiApertureHilbert wallAperture :=
    wallLift_mem_aperture hgRL (Eventually.of_forall fun y hy => indicator_of_notMem hy _)
  have hgb : ∀ᵐ x, ‖(gL : ℝ → ℂ) x‖ ≤ |Cg| := wallLift_ae_norm_le hgRL hgRb
  have hgc := wallLift_comp hgRL
  -- the window equation
  have hsolve : ∀ f : suzukiApertureHilbert wallAperture, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) uL = inner ℂ (f : RealLineL2) gL := by
    intro f hfe
    have hfA : (f : RealLineL2) ∈ suzukiApertureHilbert wallAperture := f.2
    have hRe := isWallTest_wallTestPart (π := Complex.re) Complex.continuous_re
      (fun z w => Complex.sub_re z w) Complex.abs_re_le_norm hfA hfe
    have hIm := isWallTest_wallTestPart (π := Complex.im) Complex.continuous_im
      (fun z w => Complex.sub_im z w) Complex.abs_im_le_norm hfA hfe
    have hdec := ae_wallReflect_eq_re_add_im hfA
    set φ₁ := wallTestPart Complex.re (f : RealLineL2) with hφ₁
    set φ₂ := wallTestPart Complex.im (f : RealLineL2) with hφ₂
    have h1L := hRe.domain.memLp_real
    have h2L := hIm.domain.memLp_real
    have e1 : inner ℂ (f : RealLineL2) uL =
        ((∫ y, U y * φ₁ y : ℝ) : ℂ) - I * ((∫ y, U y * φ₂ y : ℝ) : ℂ) := by
      rw [inner_eq_integral_wallReflect, ← integral_ofReal_sub_I_mul
        (integrable_mul_of_memLp hUL h1L) (integrable_mul_of_memLp hUL h2L)]
      refine integral_congr_ae ?_
      filter_upwards [hdec, hUc] with y hy1 hy2
      rw [hy1, hy2, conj_ofReal_add_ofReal_mul_I]
      push_cast
      ring
    have e2 : ∀ t : ℝ, inner ℂ (logTranslationCLM t (f : RealLineL2) - (f : RealLineL2))
        (logTranslationCLM t uL - uL) =
          ((∫ y, (U y - U (y + t)) * (φ₁ y - φ₁ (y + t)) : ℝ) : ℂ) -
            I * ((∫ y, (U y - U (y + t)) * (φ₂ y - φ₂ (y + t)) : ℝ) : ℂ) := by
      intro t
      have i1 : Integrable fun y => (U y - U (y + t)) * (φ₁ y - φ₁ (y + t)) :=
        integrable_mul_of_memLp (hUL.sub (memLp_two_shift hUL t)) (h1L.sub (memLp_two_shift h1L t))
      have i2 : Integrable fun y => (U y - U (y + t)) * (φ₂ y - φ₂ (y + t)) :=
        integrable_mul_of_memLp (hUL.sub (memLp_two_shift hUL t)) (h2L.sub (memLp_two_shift h2L t))
      rw [inner_translationLoss_eq, ← integral_ofReal_sub_I_mul i1 i2]
      refine integral_congr_ae ?_
      filter_upwards [hdec, ae_comp_add hdec t, hUc, ae_comp_add hUc t] with y hy1 hy2 hy3 hy4
      rw [hy1, hy2, hy3, hy4,
        show ((φ₁ y : ℂ) + (φ₂ y : ℂ) * I) - ((φ₁ (y + t) : ℂ) + (φ₂ (y + t) : ℂ) * I) =
          (((φ₁ y - φ₁ (y + t) : ℝ)) : ℂ) + ((φ₂ y - φ₂ (y + t) : ℝ) : ℂ) * I by push_cast; ring,
        conj_ofReal_add_ofReal_mul_I]
      push_cast
      ring
    have e3 : (∫ t in Ioi 0, (logReferenceLevyDensity t : ℂ) *
        inner ℂ (logTranslationCLM t (f : RealLineL2) - (f : RealLineL2))
          (logTranslationCLM t uL - uL)) =
        ((∫ t in Ioi 0, logReferenceLevyDensity t *
            ∫ y, (U y - U (y + t)) * (φ₁ y - φ₁ (y + t)) : ℝ) : ℂ) -
          I * ((∫ t in Ioi 0, logReferenceLevyDensity t *
            ∫ y, (U y - U (y + t)) * (φ₂ y - φ₂ (y + t)) : ℝ) : ℂ) := by
      rw [← integral_ofReal_sub_I_mul (integrableOn_logJump hU hRe.domain)
        (integrableOn_logJump hU hIm.domain)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [e2 t]
      push_cast
      ring
    have e4 : inner ℂ (f : RealLineL2) gL =
        ((∫ y, φ₁ y * h y : ℝ) : ℂ) - I * ((∫ y, φ₂ y * h y : ℝ) : ℂ) := by
      rw [inner_eq_integral_wallReflect, ← integral_ofReal_sub_I_mul
        (hRe.integrable_mul hhm hCg) (hIm.integrable_mul hhm hCg)]
      refine integral_congr_ae ?_
      filter_upwards [hdec, hgc] with y hy1 hy2
      rw [hy1, hy2, conj_ofReal_add_ofReal_mul_I]
      by_cases hm : y ∈ Icc (-(1 / 2 : ℝ)) 0
      · rw [hgRdef, indicator_of_mem hm]
        push_cast
        ring
      · rw [hRe.vanish y hm, hIm.vanish y hm]
        push_cast
        ring
    have w1 := hheqU φ₁ hRe
    have w2 := hheqU φ₂ hIm
    rw [logarithmicFullForm_eq_inner_add_jump hfe hu, e1, e3, e4, ← w1, ← w2]
    push_cast
    ring
  -- the left edge of the window is the wall
  obtain ⟨hcont, hrep, hlim⟩ := left_edge_of_bounded wallAperture ⟨uL, huA⟩ ⟨gL, hgA⟩ hu hsolve
    hC0 hub (abs_nonneg Cg) hgb
  set Gr := logarithmicGreenRepresentative
    (logarithmicApertureLeftForcing wallAperture ⟨uL, huA⟩ ⟨gL, hgA⟩) with hGr
  refine ⟨fun s => (Gr s).re, Complex.continuous_re.comp hcont, ?_, _,
    Tendsto.congr (fun s => ?_) ((Complex.continuous_re.tendsto _).comp hlim)⟩
  · have h1 : ∀ᵐ s : ℝ, s - 1 / 4 ≤ 0 → (uL : ℝ → ℂ) (s - 1 / 4) = Gr (s - 1 / 4 + 1 / 4) :=
      (measurePreserving_sub_right (volume : Measure ℝ) (1 / 4)).quasiMeasurePreserving.ae hrep
    have h2 : ∀ᵐ s : ℝ, (uL : ℝ → ℂ) (wallReflect (-s)) = (U (-s) : ℂ) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hUc
    filter_upwards [h1, h2] with s hs1 hs2 hs
    show F (-s) = (Gr s).re
    have e : wallReflect (-s) = s - 1 / 4 := by
      unfold wallReflect
      ring
    rw [e] at hs2
    have hG := hs1 (by linarith [hs.2])
    rw [hs2, show s - 1 / 4 + 1 / 4 = s by ring] at hG
    rw [← hG, Complex.ofReal_re]
    simp only [hUdef]
    rw [wallRamp_of_ge (by linarith [hs.2]), one_mul]
  · simp only [Function.comp_apply, Complex.re_mul_ofReal]

#print axioms criticalState_exists_continuous_edge

end GaloisForLFunctions.ExclusionOfTheCriticalState
