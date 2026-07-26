/-
# Tonelli decomposition for finite real phase spaces

This module gives a reusable head-tail Tonelli identity for Lebesgue measure
on `Fin (n+1) → ℝ`.  It is the measure-theoretic connector between
four-dimensional phase-coordinate set integrals and iterated real integrals.
-/
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace RHTower

noncomputable section

/-- Split the first coordinate from Lebesgue integration on
`Fin (n+1) → ℝ`. -/
theorem lintegral_fin_succ
    (n : ℕ) (f : (Fin (n + 1) → ℝ) → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, f x) =
      ∫⁻ a : ℝ, ∫⁻ u : Fin n → ℝ, f (Fin.cons a u) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  have hp := volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  have hmap := hp.lintegral_comp_emb e.measurableEmbedding
    (fun p => f (e.symm p))
  have hmap' :
      (∫⁻ x, f x) = ∫⁻ p, f (e.symm p) := by
    calc
      (∫⁻ x, f x) = ∫⁻ x, f (e.symm (e x)) := by
        apply lintegral_congr
        intro x
        rw [e.symm_apply_apply]
      _ = ∫⁻ p, f (e.symm p) := hmap
  rw [hmap']
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod]
  · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv]
  · exact (hf.comp e.symm.measurable).aemeasurable

/-- Four-dimensional Lebesgue integral as four iterated one-dimensional
Lebesgue integrals, in coordinate order `0,1,2,3`. -/
theorem lintegral_fin_four
    (f : (Fin 4 → ℝ) → ENNReal) (hf : Measurable f) :
    (∫⁻ x, f x) =
      ∫⁻ x₀ : ℝ, ∫⁻ x₁ : ℝ, ∫⁻ x₂ : ℝ, ∫⁻ x₃ : ℝ,
        f ![x₀, x₁, x₂, x₃] := by
  rw [lintegral_fin_succ 3 f hf]
  apply lintegral_congr
  intro x₀
  rw [lintegral_fin_succ 2
    (fun u => f (Fin.cons x₀ u)) (by fun_prop)]
  apply lintegral_congr
  intro x₁
  rw [lintegral_fin_succ 1
    (fun u => f (Fin.cons x₀ (Fin.cons x₁ u))) (by fun_prop)]
  apply lintegral_congr
  intro x₂
  rw [lintegral_fin_succ 0
    (fun u => f (Fin.cons x₀ (Fin.cons x₁ (Fin.cons x₂ u))))
    (by fun_prop)]
  apply lintegral_congr
  intro x₃
  rw [MeasureTheory.Measure.volume_pi_eq_dirac
    (fun i : Fin 0 => isEmptyElim i)]
  rw [lintegral_dirac' _ (by fun_prop)]
  simp
  apply congrArg f
  ext i
  fin_cases i <;> rfl

/-- Lebesgue integration over a four-dimensional sup-norm cube is exactly
four iterated integrations over the corresponding closed intervals. -/
theorem setLIntegral_fin_four_normCube
    {R : ℝ} (hR : 0 ≤ R)
    (f : (Fin 4 → ℝ) → ENNReal) (hf : Measurable f) :
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ R}, f x) =
      ∫⁻ x₀ in Set.Icc (-R) R,
        ∫⁻ x₁ in Set.Icc (-R) R,
          ∫⁻ x₂ in Set.Icc (-R) R,
            ∫⁻ x₃ in Set.Icc (-R) R,
              f ![x₀, x₁, x₂, x₃] := by
  let A : Set (Fin 4 → ℝ) := {x | ‖x‖ ≤ R}
  have hA : MeasurableSet A := by
    exact measurableSet_Iic.preimage
      ((continuous_norm.comp continuous_id).measurable)
  rw [← lintegral_indicator hA]
  rw [lintegral_fin_four _ (hf.indicator hA)]
  simp_rw [← lintegral_indicator measurableSet_Icc]
  have hcube (x₀ x₁ x₂ x₃ : ℝ) :
      (∀ i : Fin 4, ‖![x₀, x₁, x₂, x₃] i‖ ≤ R) ↔
        ((-R ≤ x₀ ∧ x₀ ≤ R) ∧
          (-R ≤ x₁ ∧ x₁ ≤ R) ∧
          (-R ≤ x₂ ∧ x₂ ≤ R) ∧
          (-R ≤ x₃ ∧ x₃ ≤ R)) := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Real.norm_eq_abs, abs_le] using h (0 : Fin 4)
      · simpa [Real.norm_eq_abs, abs_le] using h (1 : Fin 4)
      · simpa [Real.norm_eq_abs, abs_le] using h (2 : Fin 4)
      · simpa [Real.norm_eq_abs, abs_le] using h (3 : Fin 4)
    · rintro ⟨h₀, h₁, h₂, h₃⟩ i
      fin_cases i
      · simpa [Real.norm_eq_abs, abs_le] using h₀
      · simpa [Real.norm_eq_abs, abs_le] using h₁
      · simpa [Real.norm_eq_abs, abs_le] using h₂
      · simpa [Real.norm_eq_abs, abs_le] using h₃
  simp only [Set.indicator, Set.mem_Icc, A, Set.mem_setOf_eq,
    pi_norm_le_iff_of_nonneg hR, hcube]
  apply lintegral_congr
  intro x₀
  by_cases h₀ : -R ≤ x₀ ∧ x₀ ≤ R
  · simp only [h₀, true_and, ↓reduceIte]
    apply lintegral_congr
    intro x₁
    by_cases h₁ : -R ≤ x₁ ∧ x₁ ≤ R
    · simp only [h₁, true_and, ↓reduceIte]
      apply lintegral_congr
      intro x₂
      by_cases h₂ : -R ≤ x₂ ∧ x₂ ≤ R
      · simp only [h₂, true_and, ↓reduceIte]
      · simp [h₂]
    · simp [h₁]
  · simp [h₀]

/-- A nonnegative continuous function on a square may be converted between
an `ENNReal` set integral and the corresponding iterated interval integral.
The coordinate order is reversed by Fubini to match the usual
`∫ y, ∫ x, ...` convention. -/
theorem lintegral_Icc_Icc_ofReal_eq_ofReal_intervalIntegral
    {R : ℝ} (hR : 0 ≤ R)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f))
    (hn : ∀ x y, 0 ≤ f x y) :
    (∫⁻ x in Set.Icc (-R) R,
      ∫⁻ y in Set.Icc (-R) R, ENNReal.ofReal (f x y)) =
      ENNReal.ofReal
        (∫ y in (-R)..R, ∫ x in (-R)..R, f x y) := by
  let I : Set ℝ := Set.Icc (-R) R
  have hcompact : IsCompact (I ×ˢ I) :=
    isCompact_Icc.prod isCompact_Icc
  have hi :
      Integrable (Function.uncurry f)
        ((volume.restrict I).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict]
    exact hf.continuousOn.integrableOn_compact hcompact
  have hnonneg :
      0 ≤ᵐ[((volume.restrict I).prod (volume.restrict I))]
        Function.uncurry f :=
    Filter.Eventually.of_forall fun z => hn z.1 z.2
  calc
    (∫⁻ x in Set.Icc (-R) R,
        ∫⁻ y in Set.Icc (-R) R, ENNReal.ofReal (f x y)) =
        ∫⁻ z, ENNReal.ofReal (Function.uncurry f z)
          ∂((volume.restrict I).prod (volume.restrict I)) := by
            rw [lintegral_prod _
              (hf.measurable.ennreal_ofReal.aemeasurable)]
            rfl
    _ = ENNReal.ofReal
        (∫ z, Function.uncurry f z
          ∂((volume.restrict I).prod (volume.restrict I))) := by
            exact (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    _ = ENNReal.ofReal
        (∫ y in (-R)..R, ∫ x in (-R)..R, f x y) := by
          congr 1
          rw [integral_prod_symm _ hi]
          simp only [I]
          simp_rw [integral_Icc_eq_integral_Ioc]
          rw [← intervalIntegral.integral_of_le (neg_le_self hR)]
          apply intervalIntegral.integral_congr
          intro y _
          change (∫ x in Set.Ioc (-R) R, f x y) =
            ∫ x in (-R)..R, f x y
          rw [← intervalIntegral.integral_of_le (neg_le_self hR)]

/-- Four nested nonnegative integrals factor when the integrand is a product
in the first and last coordinate pairs. -/
theorem lintegral_Icc_four_ofReal_mul_eq
    {R : ℝ}
    (A B : ℝ → ℝ → ℝ)
    (hA : ∀ x y, 0 ≤ A x y)
    (hmA : Measurable (Function.uncurry A))
    (hmB : Measurable (Function.uncurry B)) :
    (∫⁻ x₀ in Set.Icc (-R) R,
      ∫⁻ x₁ in Set.Icc (-R) R,
        ∫⁻ x₂ in Set.Icc (-R) R,
          ∫⁻ x₃ in Set.Icc (-R) R,
            ENNReal.ofReal (A x₀ x₁ * B x₂ x₃)) =
      (∫⁻ x₀ in Set.Icc (-R) R,
        ∫⁻ x₁ in Set.Icc (-R) R, ENNReal.ofReal (A x₀ x₁)) *
      (∫⁻ x₂ in Set.Icc (-R) R,
        ∫⁻ x₃ in Set.Icc (-R) R, ENNReal.ofReal (B x₂ x₃)) := by
  simp_rw [ENNReal.ofReal_mul (hA _ _)]
  have hmA' (x : ℝ) : Measurable fun y => ENNReal.ofReal (A x y) :=
    ((hmA.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)
  have hmB' (x : ℝ) : Measurable fun y => ENNReal.ofReal (B x y) :=
    ((hmB.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)
  have hmAint : Measurable fun x =>
      ∫⁻ y in Set.Icc (-R) R, ENNReal.ofReal (A x y) :=
    (hmA.ennreal_ofReal.lintegral_prod_right :
      Measurable fun x =>
        ∫⁻ y in Set.Icc (-R) R, ENNReal.ofReal (A x y))
  have hmBint : Measurable fun x =>
      ∫⁻ y in Set.Icc (-R) R, ENNReal.ofReal (B x y) :=
    (hmB.ennreal_ofReal.lintegral_prod_right :
      Measurable fun x =>
        ∫⁻ y in Set.Icc (-R) R, ENNReal.ofReal (B x y))
  simp_rw [lintegral_const_mul _ (hmB' _)]
  simp_rw [lintegral_const_mul _ hmBint]
  simp_rw [lintegral_mul_const _ (hmA' _)]
  rw [lintegral_mul_const _ hmAint]

end

end RHTower
