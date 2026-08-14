import GaloisForLFunctions.RHTower.FieldOnePadicValuationUnitDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped BigOperators ENNReal

variable (p : ℕ) [Fact p.Prime]


noncomputable instance fieldOneMultiplicativeIntMeasurableSpace :
    MeasurableSpace (Multiplicative ℤ) := borel (Multiplicative ℤ)

instance fieldOneMultiplicativeIntBorelSpace :
    BorelSpace (Multiplicative ℤ) := ⟨rfl⟩

noncomputable instance fieldOnePadicNonzeroMeasurableSpace :
    MeasurableSpace ℚ_[p]ˣ := borel ℚ_[p]ˣ

instance fieldOnePadicNonzeroBorelSpace : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

instance fieldOneMultiplicativeIntCountIsHaar :
    IsHaarMeasure (Measure.count : Measure (Multiplicative ℤ)) where
  toIsMulLeftInvariant := inferInstance
  lt_top_of_isCompact K hK := by
    rw [Measure.count_apply_lt_top]
    exact hK.finite_of_discrete
  open_pos U _hU hne := Measure.count_ne_zero hne

def fieldOnePadicValuationUnitProductHaar :
    Measure (Multiplicative ℤ × ℤ_[p]ˣ) :=
  Measure.count.prod (fieldOnePadicUnitNormalizedHaar p)

instance fieldOnePadicValuationUnitProductHaar_isHaar :
    IsHaarMeasure (fieldOnePadicValuationUnitProductHaar p) := by
  unfold fieldOnePadicValuationUnitProductHaar
  infer_instance

def fieldOnePadicValuationUnitContinuousMulEquiv :
    Multiplicative ℤ × ℤ_[p]ˣ ≃ₜ* ℚ_[p]ˣ where
  toMulEquiv := fieldOnePadicValuationUnitMulEquiv p
  continuous_toFun := continuous_fieldOnePadicValuationUnitForward p
  continuous_invFun := continuous_fieldOnePadicValuationUnitMulEquiv_symm p

def fieldOnePadicMultiplicativeHaar : Measure ℚ_[p]ˣ :=
  (fieldOnePadicValuationUnitProductHaar p).map
    (fieldOnePadicValuationUnitContinuousMulEquiv p)

instance fieldOnePadicMultiplicativeHaar_isHaar :
    IsHaarMeasure (fieldOnePadicMultiplicativeHaar p) := by
  unfold fieldOnePadicMultiplicativeHaar
  infer_instance

def fieldOnePadicUnitShell : Set ℚ_[p]ˣ :=
  {a | Padic.valuation (a : ℚ_[p]) = 0}

theorem measurableSet_fieldOnePadicUnitShell :
    MeasurableSet (fieldOnePadicUnitShell p) := by
  have hcont := continuous_fieldOnePadic_valuation p
  have hopen : IsOpen
      ({Multiplicative.ofAdd (0 : ℤ)} : Set (Multiplicative ℤ)) :=
    isOpen_discrete _
  have hpre := hopen.measurableSet.preimage hcont.measurable
  convert hpre using 1
  ext a
  simp only [fieldOnePadicUnitShell, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff]
  exact Multiplicative.ofAdd.injective.eq_iff

theorem fieldOnePadicValuationUnitContinuousMulEquiv_preimage_unitShell :
    (fieldOnePadicValuationUnitContinuousMulEquiv p) ⁻¹'
        fieldOnePadicUnitShell p =
      ({Multiplicative.ofAdd (0 : ℤ)} : Set (Multiplicative ℤ)) ×ˢ
        (Set.univ : Set ℤ_[p]ˣ) := by
  ext z
  simp only [Set.mem_preimage, fieldOnePadicUnitShell, Set.mem_setOf_eq,
    Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
  rw [show
      Padic.valuation
        (((fieldOnePadicValuationUnitContinuousMulEquiv p) z : ℚ_[p]ˣ) : ℚ_[p]) =
        z.1.toAdd by
      exact fieldOnePadic_valuation_forward p z]
  exact Multiplicative.toAdd.injective.eq_iff.symm

@[simp] theorem fieldOnePadicMultiplicativeHaar_unitShell :
    fieldOnePadicMultiplicativeHaar p (fieldOnePadicUnitShell p) = 1 := by
  let e := (fieldOnePadicValuationUnitContinuousMulEquiv p).toHomeomorph.toMeasurableEquiv
  rw [fieldOnePadicMultiplicativeHaar,
    show Measure.map (fieldOnePadicValuationUnitContinuousMulEquiv p)
        (fieldOnePadicValuationUnitProductHaar p) =
      Measure.map e (fieldOnePadicValuationUnitProductHaar p) by rfl,
    e.map_apply]
  change (fieldOnePadicValuationUnitProductHaar p)
    ((fieldOnePadicValuationUnitContinuousMulEquiv p) ⁻¹'
      fieldOnePadicUnitShell p) = 1
  rw [
    fieldOnePadicValuationUnitContinuousMulEquiv_preimage_unitShell]
  rw [fieldOnePadicValuationUnitProductHaar, Measure.prod_prod]
  simp

theorem fieldOnePadicMultiplicativeHaar_integral_eq_tsum
    (f : ℚ_[p]ˣ → ℂ)
    (hf : Integrable f (fieldOnePadicMultiplicativeHaar p)) :
    ∫ a, f a ∂fieldOnePadicMultiplicativeHaar p =
      ∑' m : Multiplicative ℤ,
        ∫ u : ℤ_[p]ˣ,
          f (fieldOnePadicValuationUnitContinuousMulEquiv p (m, u))
          ∂fieldOnePadicUnitNormalizedHaar p := by
  rw [fieldOnePadicMultiplicativeHaar] at hf ⊢
  let e := fieldOnePadicValuationUnitContinuousMulEquiv p
  let μ := fieldOnePadicValuationUnitProductHaar p
  have he : Measurable e := e.measurable
  have hcomp : Integrable (fun z => f (e z)) μ := by
    exact (integrable_map_measure hf.aestronglyMeasurable he.aemeasurable).mp hf
  rw [integral_map he.aemeasurable hf.aestronglyMeasurable]
  rw [fieldOnePadicValuationUnitProductHaar, integral_prod _ hcomp]
  have houter := hcomp.integral_prod_left
  rw [integral_countable houter]
  congr 1 with m
  dsimp only [e]
  simp [Measure.real, Measure.count_apply]

end
end GaloisForLFunctions.RHTower

