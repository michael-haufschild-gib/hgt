import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewTraceFormula
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewL2Form

/-!
# Nondegeneracy of Suzuki's screw-kernel operator under RH

This module proves the necessity direction of Suzuki (2023), Theorem 1.4 for the literal
trace-class integral operator already constructed in `SuzukiScrewTraceClass`.  The two existing
realizations of `L²(-a,a)` are bridged exactly: subtype-valued interval `L²`, used by the operator,
and fixed points of zero extension in whole-line `L²`, used by the strict form theorem.  The bridge
preserves Suzuki's literal double-kernel form.  Strict positivity under RH therefore makes the
literal operator injective, equivalently excludes zero as an eigenvalue.

The converse direction of Theorem 1.4 is not claimed here.  Its source proof uses maximal-aperture
continuation and uniform infinite Gram--Schmidt estimates, not merely abstract operator algebra.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Measurable representative of an interval `L²` class. -/
def suzukiApertureRepresentative {a : ℝ} (f : SuzukiApertureIntervalL2 a) :
    SuzukiApertureInterval a → ℂ :=
  (Lp.aestronglyMeasurable f).aemeasurable.mk f

theorem measurable_suzukiApertureRepresentative {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    Measurable (suzukiApertureRepresentative f) :=
  (Lp.aestronglyMeasurable f).aemeasurable.measurable_mk

theorem suzukiApertureRepresentative_ae {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    suzukiApertureRepresentative f =ᵐ[volume] f :=
  (Lp.aestronglyMeasurable f).aemeasurable.ae_eq_mk.symm

/-- Literal zero extension of an interval `L²` representative to the real line. -/
def suzukiApertureZeroExtend {a : ℝ} (f : SuzukiApertureIntervalL2 a) : ℝ → ℂ :=
  Function.extend Subtype.val (suzukiApertureRepresentative f) 0

theorem suzukiApertureZeroExtend_apply {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) (x : SuzukiApertureInterval a) :
    suzukiApertureZeroExtend f x = suzukiApertureRepresentative f x := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ x

theorem suzukiApertureZeroExtend_eq_zero_of_notMem {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) {x : ℝ} (hx : x ∉ Icc (-a) a) :
    suzukiApertureZeroExtend f x = 0 := by
  have hnot : ¬∃ y : SuzukiApertureInterval a, (y : ℝ) = x := by
    rintro ⟨y, rfl⟩
    exact hx y.property
  rw [suzukiApertureZeroExtend, Function.extend_apply' _ _ _ hnot]
  rfl

theorem suzukiApertureZeroExtend_aestronglyMeasurable {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    AEStronglyMeasurable (suzukiApertureZeroExtend f) := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  exact ((MeasurableEmbedding.subtype_coe measurableSet_Icc).measurable_extend
    (measurable_suzukiApertureRepresentative f) measurable_const).aemeasurable

theorem suzukiApertureZeroExtend_memLp {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    MemLp (suzukiApertureZeroExtend f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (suzukiApertureZeroExtend_aestronglyMeasurable f)).2
  have hsub : Integrable
      (fun x : SuzukiApertureInterval a => ‖suzukiApertureRepresentative f x‖ ^ 2) := by
    refine ((Lp.memLp f).integrable_norm_pow (by norm_num)).congr ?_
    filter_upwards [suzukiApertureRepresentative_ae f] with x hx
    rw [hx]
  have hon : IntegrableOn (fun x : ℝ => ‖suzukiApertureZeroExtend f x‖ ^ 2)
      (Icc (-a) a) := by
    rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
    refine hsub.congr (ae_of_all _ fun x => ?_)
    dsimp only [Function.comp_apply]
    rw [suzukiApertureZeroExtend_apply]
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem f hx, norm_zero]
    norm_num

/-- Zero extension as a whole-line `L²` vector. -/
def suzukiApertureZeroExtendL2 {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) : SoninL2 :=
  (suzukiApertureZeroExtend_memLp f).toLp (suzukiApertureZeroExtend f)

theorem suzukiApertureZeroExtendL2_coeFn {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    suzukiApertureZeroExtendL2 f =ᵐ[volume] suzukiApertureZeroExtend f :=
  MemLp.coeFn_toLp (suzukiApertureZeroExtend_memLp f)

theorem suzukiApertureZeroExtendL2_cutoff {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    suzukiCutoff a (suzukiApertureZeroExtendL2 f) =
      suzukiApertureZeroExtendL2 f := by
  apply Lp.ext
  filter_upwards [
    indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc (suzukiApertureZeroExtendL2 f),
    suzukiApertureZeroExtendL2_coeFn f] with x hcut hext
  rw [hcut, hext]
  by_cases hx : x ∈ Icc (-a) a
  · rw [indicator_of_mem hx]
    exact hext
  · rw [indicator_of_notMem hx, suzukiApertureZeroExtend_eq_zero_of_notMem f hx]

theorem suzukiApertureZeroExtendL2_injective {a : ℝ} :
    Function.Injective (suzukiApertureZeroExtendL2 (a := a)) := by
  intro f g hfg
  apply Lp.ext
  have hl2 : ((suzukiApertureZeroExtendL2 f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (suzukiApertureZeroExtendL2 g : SoninL2) := by
    rw [hfg]
  have hwhole : (suzukiApertureZeroExtend f : ℝ → ℂ) =ᵐ[volume]
      suzukiApertureZeroExtend g :=
    (suzukiApertureZeroExtendL2_coeFn f).symm.trans
      (hl2.trans (suzukiApertureZeroExtendL2_coeFn g))
  have hsub :
      (fun x : SuzukiApertureInterval a => suzukiApertureZeroExtend f x) =ᵐ[volume]
        fun x => suzukiApertureZeroExtend g x :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp (ae_restrict_of_ae hwhole)
  filter_upwards [hsub, suzukiApertureRepresentative_ae f,
    suzukiApertureRepresentative_ae g] with x hfgx hfx hgx
  rw [suzukiApertureZeroExtend_apply, suzukiApertureZeroExtend_apply, hfx, hgx] at hfgx
  exact hfgx

/-- Suzuki's literal bounded-aperture Hermitian form, with source convention linear in the first
argument. -/
def suzukiScrewIntervalForm (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) : ℂ :=
  ∫ t : SuzukiApertureInterval a, ∫ u : SuzukiApertureInterval a,
    suzukiScrewKernel (t : ℝ) (u : ℝ) * f u * (starRingEnd ℂ) (g t)

/-- Whole-line fixed-point form equals the literal interval `L²` double-kernel form. -/
theorem suzukiScrewL2Form_zeroExtend_eq_intervalForm {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    suzukiScrewL2Form a (suzukiApertureZeroExtendL2 f)
        (suzukiApertureZeroExtendL2 f) =
      ∫ t : SuzukiApertureInterval a, ∫ u : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (u : ℝ) * f u * (starRingEnd ℂ) (f t) := by
  rw [suzukiScrewL2Form, suzukiApertureZeroExtendL2_cutoff f]
  have hcoe := suzukiApertureZeroExtendL2_coeFn f
  calc
    (∫ t : ℝ, ∫ u : ℝ,
        suzukiScrewKernel t u * (suzukiApertureZeroExtendL2 f) u *
          (starRingEnd ℂ) ((suzukiApertureZeroExtendL2 f) t)) =
      ∫ t : ℝ, ∫ u : ℝ,
        suzukiScrewKernel t u * suzukiApertureZeroExtend f u *
          (starRingEnd ℂ) (suzukiApertureZeroExtend f t) := by
        apply integral_congr_ae
        filter_upwards [hcoe] with t ht
        rw [ht]
        apply integral_congr_ae
        filter_upwards [hcoe] with u hu
        rw [hu]
    _ = _ := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      · rw [← integral_subtype measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [suzukiApertureRepresentative_ae f] with t ht
        rw [suzukiApertureZeroExtend_apply, ht]
        rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
        · rw [← integral_subtype measurableSet_Icc]
          apply integral_congr_ae
          filter_upwards [suzukiApertureRepresentative_ae f] with u hu
          rw [suzukiApertureZeroExtend_apply, hu]
        · intro u hu
          rw [suzukiApertureZeroExtend_eq_zero_of_notMem f hu]
          ring
      · intro t ht
        rw [suzukiApertureZeroExtend_eq_zero_of_notMem f ht]
        simp

/-- The interval double-kernel form is the quadratic pairing of Suzuki's literal integral
operator. -/
theorem inner_suzukiScrewIntegralOperator_eq_intervalForm {a : ℝ} (ha : 0 ≤ a)
    (f : SuzukiApertureIntervalL2 a) :
    inner ℂ (suzukiScrewIntegralOperator a f) f =
      ∫ t : SuzukiApertureInterval a, ∫ u : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (u : ℝ) * f u * (starRingEnd ℂ) (f t) := by
  obtain ⟨C, hC⟩ := exists_suzukiScrewKernel_norm_bound a
  have hL : inner ℂ (suzukiScrewIntegralOperator a f) f =
      ∫ t : SuzukiApertureInterval a,
        ∫ u : SuzukiApertureInterval a,
          (starRingEnd ℂ) (f u) *
            (starRingEnd ℂ) (suzukiScrewKernel (t : ℝ) (u : ℝ)) * f t := by
    rw [inner_suzukiApertureL2_eq_integral]
    apply integral_congr_ae
    filter_upwards [suzukiScrewIntegralOperator_coeFn ha f] with t ht
    rw [ht, ← integral_conj, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with u
    simp only [map_mul]
    ring
  rw [hL]
  calc
    (∫ t : SuzukiApertureInterval a,
        ∫ u : SuzukiApertureInterval a,
          (starRingEnd ℂ) (f u) *
            (starRingEnd ℂ) (suzukiScrewKernel (t : ℝ) (u : ℝ)) * f t) =
      ∫ u : SuzukiApertureInterval a,
        ∫ t : SuzukiApertureInterval a,
          (starRingEnd ℂ) (f u) *
            (starRingEnd ℂ) (suzukiScrewKernel (t : ℝ) (u : ℝ)) * f t :=
        integral_integral_swap (integrable_suzukiScrewKernel_pair hC f f)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with u
      rw [suzukiScrewKernel_conj_swap]
      ring

/-- Exact sesquilinear representation of Suzuki's interval form by his literal integral
operator. -/
theorem inner_suzukiScrewIntegralOperator_eq_intervalForm_pair {a : ℝ} (ha : 0 ≤ a)
    (f g : SuzukiApertureIntervalL2 a) :
    inner ℂ g (suzukiScrewIntegralOperator a f) = suzukiScrewIntervalForm a f g := by
  rw [inner_suzukiApertureL2_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiScrewIntegralOperator_coeFn ha f] with t ht
  rw [ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- Suzuki's literal interval form is Hermitian. -/
theorem suzukiScrewIntervalForm_conj_symm {a : ℝ} (ha : 0 ≤ a)
    (f g : SuzukiApertureIntervalL2 a) :
    (starRingEnd ℂ) (suzukiScrewIntervalForm a g f) = suzukiScrewIntervalForm a f g := by
  rw [← inner_suzukiScrewIntegralOperator_eq_intervalForm_pair ha,
    ← inner_suzukiScrewIntegralOperator_eq_intervalForm_pair ha,
    inner_conj_symm]
  exact suzukiScrewIntegralOperator_isSymmetric ha g f

/-- Radical-zero definition of nondegeneracy for Suzuki's literal interval form. -/
def SuzukiScrewIntervalFormNondegenerate (a : ℝ) : Prop :=
  ∀ f : SuzukiApertureIntervalL2 a,
    (∀ g : SuzukiApertureIntervalL2 a, suzukiScrewIntervalForm a f g = 0) → f = 0

/-- The second assertion in Suzuki (2023), Theorem 1.4: nondegeneracy of the literal Hermitian
form is exactly absence of a zero eigenvector for the literal integral operator. -/
theorem suzukiScrewIntervalForm_nondegenerate_iff_operator_injective {a : ℝ} (ha : 0 ≤ a) :
    SuzukiScrewIntervalFormNondegenerate a ↔
      Function.Injective (suzukiScrewIntegralOperator a) := by
  constructor
  · intro hnon f g hfg
    rw [← sub_eq_zero]
    apply hnon (f - g)
    intro h
    rw [← inner_suzukiScrewIntegralOperator_eq_intervalForm_pair ha]
    rw [map_sub, hfg, sub_self]
    simp
  · intro hinj f hf
    apply hinj
    rw [map_zero]
    have hself : inner ℂ (suzukiScrewIntegralOperator a f)
        (suzukiScrewIntegralOperator a f) = 0 := by
      rw [inner_suzukiScrewIntegralOperator_eq_intervalForm_pair ha]
      exact hf (suzukiScrewIntegralOperator a f)
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp hself

/-- Exact point-spectrum wording of Suzuki's operator condition: zero is absent as an eigenvalue
exactly when the literal interval operator is injective. -/
theorem suzukiScrewIntegralOperator_zero_not_eigenvalue_iff_injective (a : ℝ) :
    ¬ Module.End.HasEigenvalue
        (suzukiScrewIntegralOperator a : Module.End ℂ (SuzukiApertureIntervalL2 a)) 0 ↔
      Function.Injective (suzukiScrewIntegralOperator a) := by
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero, not_ne_iff]
  exact LinearMap.ker_eq_bot

/-- The two formulations printed in Suzuki (2023), Theorem 1.4 are literally equivalent: the
Hermitian form has zero radical iff zero is not an eigenvalue of its integral operator. -/
theorem suzukiScrewIntervalForm_nondegenerate_iff_zero_not_eigenvalue {a : ℝ} (ha : 0 ≤ a) :
    SuzukiScrewIntervalFormNondegenerate a ↔
      ¬ Module.End.HasEigenvalue
        (suzukiScrewIntegralOperator a : Module.End ℂ (SuzukiApertureIntervalL2 a)) 0 := by
  rw [suzukiScrewIntervalForm_nondegenerate_iff_operator_injective ha,
    suzukiScrewIntegralOperator_zero_not_eigenvalue_iff_injective]

/-- RH excludes zero from the point spectrum of Suzuki's literal bounded-aperture operator. -/
theorem suzukiScrewIntegralOperator_injective_of_riemannHypothesis
    (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a) :
    Function.Injective (suzukiScrewIntegralOperator a) := by
  intro f g hfg
  rw [← sub_eq_zero]
  let d : SuzukiApertureIntervalL2 a := f - g
  have hdop : suzukiScrewIntegralOperator a d = 0 := by
    dsimp [d]
    rw [map_sub, hfg, sub_self]
  by_contra hd
  let F : SuzukiApertureL2 a :=
    ⟨suzukiApertureZeroExtendL2 d, suzukiApertureZeroExtendL2_cutoff d⟩
  have hF : (F : SoninL2) ≠ 0 := by
    intro hzero
    change suzukiApertureZeroExtendL2 d = 0 at hzero
    apply hd
    apply Lp.ext
    have hwhole : suzukiApertureZeroExtend d =ᵐ[volume] (0 : ℝ → ℂ) := by
      have hl2 : ((suzukiApertureZeroExtendL2 d : SoninL2) : ℝ → ℂ) =ᵐ[volume]
          (0 : SoninL2) := by rw [hzero]
      exact (suzukiApertureZeroExtendL2_coeFn d).symm.trans
        (hl2.trans (Lp.coeFn_zero ℂ 2 volume))
    have hsub :
        (fun x : SuzukiApertureInterval a => suzukiApertureZeroExtend d x) =ᵐ[volume]
          (0 : SuzukiApertureInterval a → ℂ) :=
      (ae_restrict_iff_subtype measurableSet_Icc).mp (ae_restrict_of_ae hwhole)
    filter_upwards [hsub, suzukiApertureRepresentative_ae d,
      Lp.coeFn_zero ℂ 2 (volume : Measure (SuzukiApertureInterval a))] with x hx hrep hzero'
    rw [suzukiApertureZeroExtend_apply, hrep] at hx
    exact hx.trans hzero'.symm
  have hpos := suzuki_theorem_one_three_strict_l2 hRH ha F hF
  have hform := suzukiScrewL2Form_zeroExtend_eq_intervalForm d
  have hinner := inner_suzukiScrewIntegralOperator_eq_intervalForm ha.le d
  have hzero : inner ℂ (suzukiScrewIntegralOperator a d) d = 0 := by
    rw [hdop]
    simp
  rw [hform, ← hinner, hzero] at hpos
  norm_num at hpos

/-- Closed necessity half of Suzuki (2023), Theorem 1.4. -/
theorem riemannHypothesis_implies_suzukiScrewOperators_nondegenerate :
    RiemannHypothesis →
      ∀ a : ℝ, 0 < a → Function.Injective (suzukiScrewIntegralOperator a) := by
  intro hRH a ha
  exact suzukiScrewIntegralOperator_injective_of_riemannHypothesis hRH ha

/-- Closed point-spectrum wording of the necessity half of Suzuki (2023), Theorem 1.4. -/
theorem riemannHypothesis_implies_suzukiScrewOperators_zero_not_eigenvalue :
    RiemannHypothesis →
      ∀ a : ℝ, 0 < a →
        ¬ Module.End.HasEigenvalue
          (suzukiScrewIntegralOperator a : Module.End ℂ (SuzukiApertureIntervalL2 a)) 0 := by
  intro hRH a ha
  exact (suzukiScrewIntegralOperator_zero_not_eigenvalue_iff_injective a).2
    (suzukiScrewIntegralOperator_injective_of_riemannHypothesis hRH ha)

/-- Closed form-language necessity half of Suzuki (2023), Theorem 1.4. -/
theorem riemannHypothesis_implies_suzukiScrewIntervalForms_nondegenerate :
    RiemannHypothesis →
      ∀ a : ℝ, 0 < a → SuzukiScrewIntervalFormNondegenerate a := by
  intro hRH a ha
  exact (suzukiScrewIntervalForm_nondegenerate_iff_operator_injective ha.le).2
    (suzukiScrewIntegralOperator_injective_of_riemannHypothesis hRH ha)

end RHTower
