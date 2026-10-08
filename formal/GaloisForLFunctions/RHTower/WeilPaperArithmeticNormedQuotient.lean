import GaloisForLFunctions.RHTower.WeilPaperClosedArithmeticPenalties
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Gamma optimization on the arithmetic normed quotient

Every feasible probability expectation descends to the Banach quotient by
closed integer arithmetic directions. The attained gamma value descends as a
concave 1-Lipschitz function. Constants retain their exact norm, so the quotient
is nontrivial and the Lipschitz bound is sharp. Quotient distance also controls
the error when transferring a minimizer between spectral penalties.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

variable {ι : Type*}

/-- Feasible probability expectation as a continuous linear functional on effective penalties. -/
def paperArithmeticQuotientExpectation (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) : PaperArithmeticPenaltyQuotient →L[ℝ] ℝ :=
  paperClosedArithmeticPenalties.liftQL (paperSpectralExpectationCLM μ.1)
    (paperClosedArithmeticPenalties_le_expectation_ker c F μ)

@[simp] theorem paperArithmeticQuotientExpectation_class
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (μ : PaperObservedSpectralCompletion c F)
    (G : ℝ →ᵇ ℝ) :
    paperArithmeticQuotientExpectation c F μ (paperArithmeticPenaltyClass G) =
      ∫ ξ, G ξ ∂(μ.1 : Measure ℝ) := rfl

/-- Probability expectation remains contractive after all closed arithmetic directions are removed. -/
theorem abs_paperArithmeticQuotientExpectation_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (μ : PaperObservedSpectralCompletion c F)
    (q : PaperArithmeticPenaltyQuotient) :
    |paperArithmeticQuotientExpectation c F μ q| ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨G, hG, hnorm⟩ := Submodule.Quotient.norm_mk_lt q hε
  change paperArithmeticPenaltyClass G = q at hG
  have hi := G.norm_integral_le_norm (μ.1 : Measure ℝ)
  rw [Real.norm_eq_abs] at hi
  calc
    _ = |∫ ξ, G ξ ∂(μ.1 : Measure ℝ)| := by
      rw [← hG, paperArithmeticQuotientExpectation_class]
    _ ≤ ‖G‖ := hi
    _ ≤ ‖q‖ + ε := hnorm.le

/-- The minimum actual gamma energy is well-defined on arithmetic penalty classes. -/
def paperArithmeticQuotientGammaValue (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    PaperArithmeticPenaltyQuotient → ℝ :=
  Quotient.lift (paperObservedGammaValue c F) (fun G H h =>
    paperObservedGammaValue_eq_of_class_eq c F G H (Quotient.sound h))

@[simp] theorem paperArithmeticQuotientGammaValue_class
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) :
    paperArithmeticQuotientGammaValue c F (paperArithmeticPenaltyClass G) =
      paperObservedGammaValue c F G := rfl

/-- The value difference is bounded by the actual quotient norm, without choosing a best representative. -/
theorem paperObservedGammaValue_closed_quotient_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) :
    |paperObservedGammaValue c F G - paperObservedGammaValue c F H| ≤
      ‖paperArithmeticPenaltyClass (G - H)‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨K, hK, hnorm⟩ := Submodule.Quotient.norm_mk_lt
    (paperArithmeticPenaltyClass (G - H)) hε
  change paperArithmeticPenaltyClass K = paperArithmeticPenaltyClass (G - H) at hK
  have he : paperArithmeticPenaltyClass (H + K) = paperArithmeticPenaltyClass G := by
    rw [map_add, hK, map_sub]
    abel
  have hv := paperObservedGammaValue_eq_of_class_eq c F (H + K) G he
  have hb := abs_paperObservedGammaValue_sub_le c F (H + K) H
  rw [hv, show H + K - H = K by abel] at hb
  exact hb.trans hnorm.le

/-- Removing invisible directions gives the sharp global Lipschitz estimate. -/
theorem lipschitzWith_paperArithmeticQuotientGammaValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    LipschitzWith 1 (paperArithmeticQuotientGammaValue c F) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro q r
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties q
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties r
  change dist (paperObservedGammaValue c F G) (paperObservedGammaValue c F H) ≤
    (1 : ℝ≥0) * dist (paperArithmeticPenaltyClass G) (paperArithmeticPenaltyClass H)
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, map_sub] using
    paperObservedGammaValue_closed_quotient_bound c F G H

theorem continuous_paperArithmeticQuotientGammaValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    Continuous (paperArithmeticQuotientGammaValue c F) :=
  (lipschitzWith_paperArithmeticQuotientGammaValue c F).continuous

/-- Concavity survives passage to effective penalty classes. -/
theorem paperArithmeticQuotientGammaValue_concave
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (q r : PaperArithmeticPenaltyQuotient)
    (t : Icc (0 : ℝ) 1) :
    t.1 * paperArithmeticQuotientGammaValue c F q +
        (1 - t.1) * paperArithmeticQuotientGammaValue c F r ≤
      paperArithmeticQuotientGammaValue c F (t.1 • q + (1 - t.1) • r) := by
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties q
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties r
  exact paperObservedGammaValue_concave c F G H t

/-- Constants act by exact affine translations on the quotient value. -/
theorem paperArithmeticQuotientGammaValue_add_const
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (q : PaperArithmeticPenaltyQuotient) (a : ℝ) :
    paperArithmeticQuotientGammaValue c F
        (q + paperArithmeticPenaltyClass (BoundedContinuousFunction.const ℝ a)) =
      paperArithmeticQuotientGammaValue c F q + a := by
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties q
  exact paperObservedGammaValue_add_const c F G a

/-- Constants keep their full norm after quotienting; no nonzero constant is an invisible direction. -/
theorem norm_paperArithmeticPenaltyClass_const (c : ComplexNullMixture) (a : ℝ) :
    ‖paperArithmeticPenaltyClass (BoundedContinuousFunction.const ℝ a)‖ = |a| := by
  apply le_antisymm
  · exact (Submodule.Quotient.norm_mk_le paperClosedArithmeticPenalties _).trans_eq
      (by rw [BoundedContinuousFunction.norm_const_eq, Real.norm_eq_abs])
  · let F : Empty → ℝ →ᵇ ℂ := fun _ => 0
    have hb := paperObservedGammaValue_closed_quotient_bound c F
      (0 + BoundedContinuousFunction.const ℝ a) 0
    rw [paperObservedGammaValue_add_const] at hb
    simpa only [zero_add, add_sub_cancel_left, sub_zero] using hb

/-- Constant shifts attain the quotient Lipschitz bound exactly. -/
theorem paperArithmeticQuotientGammaValue_constant_distance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (q : PaperArithmeticPenaltyQuotient) (a : ℝ) :
    |paperArithmeticQuotientGammaValue c F
        (q + paperArithmeticPenaltyClass (BoundedContinuousFunction.const ℝ a)) -
      paperArithmeticQuotientGammaValue c F q| =
        ‖paperArithmeticPenaltyClass (BoundedContinuousFunction.const ℝ a)‖ := by
  rw [paperArithmeticQuotientGammaValue_add_const, norm_paperArithmeticPenaltyClass_const c]
  congr 1
  ring

/-- The arithmetic quotient does not collapse the unit penalty. -/
theorem paperArithmeticPenaltyClass_one_ne_zero (c : ComplexNullMixture) :
    paperArithmeticPenaltyClass (BoundedContinuousFunction.const ℝ (1 : ℝ)) ≠ 0 := by
  intro h
  have hn := norm_paperArithmeticPenaltyClass_const c 1
  have hz : ‖(0 : PaperArithmeticPenaltyQuotient)‖ = 0 :=
    @norm_zero PaperArithmeticPenaltyQuotient _
  rw [h, hz, abs_one] at hn
  exact zero_ne_one hn

/-- The closed invisible subspace is proper, despite containing all integer logarithmic penalties. -/
theorem paperClosedArithmeticPenalties_ne_top (c : ComplexNullMixture) :
    paperClosedArithmeticPenalties ≠ ⊤ := by
  intro h
  apply paperArithmeticPenaltyClass_one_ne_zero c
  exact (Submodule.Quotient.mk_eq_zero _).mpr (by rw [h]; trivial)

/-- The gamma objective itself descends to an affine function on effective penalties. -/
def paperArithmeticQuotientGammaObjective
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (μ : PaperObservedSpectralCompletion c F)
    (q : PaperArithmeticPenaltyQuotient) : ℝ :=
  (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) +
    paperArithmeticQuotientExpectation c F μ q

@[simp] theorem paperArithmeticQuotientGammaObjective_class
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (μ : PaperObservedSpectralCompletion c F)
    (G : ℝ →ᵇ ℝ) :
    paperArithmeticQuotientGammaObjective c F μ (paperArithmeticPenaltyClass G) =
      paperPerturbedGammaExpectation G μ.1 := rfl

/-- The quotient value is below every actual feasible affine objective. -/
theorem paperArithmeticQuotientGammaValue_le_objective
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (μ : PaperObservedSpectralCompletion c F)
    (q : PaperArithmeticPenaltyQuotient) :
    paperArithmeticQuotientGammaValue c F q ≤ paperArithmeticQuotientGammaObjective c F μ q := by
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties q
  exact paperObservedGammaValue_le c F G μ

/-- Every effective penalty has an attained minimizer giving a supporting continuous linear functional. -/
theorem exists_paperArithmeticQuotientGamma_support
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (q : PaperArithmeticPenaltyQuotient) :
    ∃ μ : PaperObservedSpectralCompletion c F,
      paperArithmeticQuotientGammaObjective c F μ q = paperArithmeticQuotientGammaValue c F q ∧
      ∀ r : PaperArithmeticPenaltyQuotient,
        paperArithmeticQuotientGammaValue c F r ≤ paperArithmeticQuotientGammaValue c F q +
          paperArithmeticQuotientExpectation c F μ (r - q) := by
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties q
  refine ⟨paperObservedGammaMinimizer c F G, rfl, ?_⟩
  intro r
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective paperClosedArithmeticPenalties r
  exact paperObservedGammaValue_supergradient c F G H

/-- Optimizer transfer is controlled by effective penalty distance, including uniform-limit cancellation. -/
theorem paperObservedGammaMinimizer_closed_quotient_transfer_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) :
    0 ≤ paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 -
        paperObservedGammaValue c F G ∧
      paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 -
        paperObservedGammaValue c F G ≤ 2 * ‖paperArithmeticPenaltyClass (G - H)‖ := by
  let μ := paperObservedGammaMinimizer c F H
  have hm := paperObservedGammaValue_le c F G μ
  have hd := paperPerturbedGammaExpectation_sub μ.1 G H
  have hi := abs_paperArithmeticQuotientExpectation_le c F μ (paperArithmeticPenaltyClass (G - H))
  rw [paperArithmeticQuotientExpectation_class] at hi
  have hv := paperObservedGammaValue_closed_quotient_bound c F G H
  have hi' := (abs_le.mp hi).2
  have hv' := (abs_le.mp hv).1
  change paperPerturbedGammaExpectation G μ.1 - paperObservedGammaValue c F H = _ at hd
  constructor <;> linarith

end RHTower.WeilWorkPBAP
