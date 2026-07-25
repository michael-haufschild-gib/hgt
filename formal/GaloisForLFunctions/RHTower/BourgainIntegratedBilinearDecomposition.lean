/-
# Integrated separated linear-to-bilinear decomposition

The pointwise three-color inequality is lifted to arbitrary measures.  The
integrability assumptions are purely structural and are discharged
automatically for the continuous finite exponential sums on Bourgain's
bounded integration regions.
-/
import GaloisForLFunctions.RHTower.BourgainSeparatedBilinearDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Pointwise separated diagonal/bilinear majorant. -/
def bourgainThreeColorBilinearMajorant
    {Ω : Type*} (K : ℕ) (f : Fin K → Ω → ℂ) (x : Ω) : ℝ :=
  (3 : ℝ) ^ (11 : ℕ) *
    ∑ c : Fin 3,
      ((2 : ℝ) ^ (12 : ℕ) *
          ∑ i ∈ bourgainColorBlockFinset K c,
            ‖f i x‖ ^ (12 : ℕ) +
        ((bourgainColorBlockFinset K c).card : ℝ) ^ (18 : ℕ) *
          ∑ i ∈ bourgainColorBlockFinset K c,
            ∑ j ∈ (bourgainColorBlockFinset K c).filter
                (fun j => j ≠ i),
              ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ))

/-- The three-color expression majorizes the twelfth power pointwise. -/
theorem norm_sum_pow_twelve_le_bourgainThreeColorBilinearMajorant
    {Ω : Type*} (K : ℕ) (f : Fin K → Ω → ℂ) (x : Ω) :
    ‖∑ i : Fin K, f i x‖ ^ (12 : ℕ) ≤
      bourgainThreeColorBilinearMajorant K f x := by
  exact norm_finSum_pow_twelve_le_threeColor_bilinear K (fun i => f i x)

/-- The separated majorant is integrable whenever all diagonal and bilinear
pieces are integrable. -/
theorem integrable_bourgainThreeColorBilinearMajorant
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℕ) (f : Fin K → Ω → ℂ)
    (hdiag :
      ∀ i : Fin K, Integrable (fun x => ‖f i x‖ ^ (12 : ℕ)) μ)
    (hpair :
      ∀ (c : Fin 3) (i : Fin K),
        i ∈ bourgainColorBlockFinset K c →
        ∀ j : Fin K,
          j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i) →
          Integrable
            (fun x => ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ)) μ) :
    Integrable (bourgainThreeColorBilinearMajorant K f) μ := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro c hc
  apply Integrable.add
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro i hi
    exact hdiag i
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hpair c i hi j hj

/-- **Integrated Bourgain--Guth decomposition.** -/
theorem integral_norm_sum_pow_twelve_le_bourgainThreeColorBilinearMajorant
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℕ) (f : Fin K → Ω → ℂ)
    (hleft :
      Integrable (fun x => ‖∑ i : Fin K, f i x‖ ^ (12 : ℕ)) μ)
    (hdiag :
      ∀ i : Fin K, Integrable (fun x => ‖f i x‖ ^ (12 : ℕ)) μ)
    (hpair :
      ∀ (c : Fin 3) (i : Fin K),
        i ∈ bourgainColorBlockFinset K c →
        ∀ j : Fin K,
          j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i) →
          Integrable
            (fun x => ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ)) μ) :
    (∫ x, ‖∑ i : Fin K, f i x‖ ^ (12 : ℕ) ∂μ) ≤
      ∫ x, bourgainThreeColorBilinearMajorant K f x ∂μ := by
  apply integral_mono_ae hleft
    (integrable_bourgainThreeColorBilinearMajorant μ K f hdiag hpair)
  exact Filter.Eventually.of_forall fun x =>
    norm_sum_pow_twelve_le_bourgainThreeColorBilinearMajorant K f x

end

end RHTower
