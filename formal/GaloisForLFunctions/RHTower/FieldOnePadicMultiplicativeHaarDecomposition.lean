import GaloisForLFunctions.RHTower.FieldOnePadicValuationUnitDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Multiplicative Haar measure on `ℚ_p^×` via the valuation–unit decomposition

The map `(k, u) ↦ p^k u` is an isomorphism of topological groups `ℤ × ℤ_p^× ≅ ℚ_p^×`. This
module transports the product of counting measure on `ℤ` and the normalized Haar probability
measure on `ℤ_p^×` along this isomorphism to obtain a Haar measure on `ℚ_p^×`. The unit shell
`{a : v_p(a) = 0} = ℤ_p^×` has measure `1`, and integrals of integrable functions decompose as a
sum over valuations: `∫ f = ∑_{k ∈ ℤ} ∫_{ℤ_p^×} f(p^k u) du`.

## Main results

- `fieldOnePadicValuationUnitContinuousMulEquiv`: the topological group isomorphism
  `ℤ × ℤ_p^× ≃ₜ* ℚ_p^×`, `(k, u) ↦ p^k u`.
- `fieldOnePadicMultiplicativeHaar`: the transported measure, a Haar measure on `ℚ_p^×`.
- `fieldOnePadicMultiplicativeHaar_unitShell`: the unit shell has measure `1`.
- `fieldOnePadicMultiplicativeHaar_integral_eq_tsum`: for integrable `f`,
  `∫ f = ∑_{k ∈ ℤ} ∫_{ℤ_p^×} f(p^k u) du`.

## Hypotheses

Unconditional; the integral decomposition assumes `f` integrable for the multiplicative Haar
measure.
-/

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

/-- Counting measure on the discrete group `ℤ` (written multiplicatively) is a Haar measure. -/
instance fieldOneMultiplicativeIntCountIsHaar :
    IsHaarMeasure (Measure.count : Measure (Multiplicative ℤ)) where
  toIsMulLeftInvariant := inferInstance
  lt_top_of_isCompact K hK := by
    rw [Measure.count_apply_lt_top]
    exact hK.finite_of_discrete
  open_pos U _hU hne := Measure.count_ne_zero hne

/-- Product of counting measure on `ℤ` and the normalized Haar probability measure on `ℤ_p^×`. -/
def fieldOnePadicValuationUnitProductHaar :
    Measure (Multiplicative ℤ × ℤ_[p]ˣ) :=
  Measure.count.prod (fieldOnePadicUnitNormalizedHaar p)

instance fieldOnePadicValuationUnitProductHaar_isHaar :
    IsHaarMeasure (fieldOnePadicValuationUnitProductHaar p) := by
  unfold fieldOnePadicValuationUnitProductHaar
  infer_instance

/-- The valuation–unit decomposition `ℤ × ℤ_p^× ≃ₜ* ℚ_p^×`, `(k, u) ↦ p^k u`, as an isomorphism of
topological groups. -/
def fieldOnePadicValuationUnitContinuousMulEquiv :
    Multiplicative ℤ × ℤ_[p]ˣ ≃ₜ* ℚ_[p]ˣ where
  toMulEquiv := fieldOnePadicValuationUnitMulEquiv p
  continuous_toFun := continuous_fieldOnePadicValuationUnitForward p
  continuous_invFun := continuous_fieldOnePadicValuationUnitMulEquiv_symm p

/-- Multiplicative Haar measure on `ℚ_p^×`: the pushforward of counting measure times normalized unit
Haar measure along `(k, u) ↦ p^k u`. -/
def fieldOnePadicMultiplicativeHaar : Measure ℚ_[p]ˣ :=
  (fieldOnePadicValuationUnitProductHaar p).map
    (fieldOnePadicValuationUnitContinuousMulEquiv p)

/-- The transported measure on `ℚ_p^×` is a Haar measure. -/
instance fieldOnePadicMultiplicativeHaar_isHaar :
    IsHaarMeasure (fieldOnePadicMultiplicativeHaar p) := by
  unfold fieldOnePadicMultiplicativeHaar
  infer_instance

/-- The unit shell `{a ∈ ℚ_p^× : v_p(a) = 0}`. -/
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

/-- The unit shell `{v_p(a) = 0}` has multiplicative Haar measure `1`. -/
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

/-- Valuation decomposition of multiplicative Haar integrals: for integrable `f` on `ℚ_p^×`,
`∫ f = ∑_{k ∈ ℤ} ∫_{ℤ_p^×} f(p^k u) du`. -/
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

