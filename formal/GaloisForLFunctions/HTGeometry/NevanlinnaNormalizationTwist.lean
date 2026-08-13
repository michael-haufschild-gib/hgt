import GaloisForLFunctions.HTGeometry.NevanlinnaConstraintProjector
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Normalization independence of the Nevanlinna carrier projector

A change of the real determinant-one Nevanlinna matrix acts by right multiplication with an
element `g` of `SL(2, ℝ)`.  The twisted matrix data has denominator
`c'(x)σ + d'(x) = c(x)(g₀₀σ + g₀₁) + d(x)(g₁₀σ + g₁₁)`, so its denominator fibers are the
original fibers relabelled along the Möbius action of `g` on the projective line, and the twisted
boundary family carries the original leaves in the relabelled coordinate.  The leaf/label
covariance transport therefore applies with the relabelling `t ↦ g⁻¹ • t`, and the carrier
projector of the twisted family coincides with the original one: the canonical retraction is
independent of the chosen Nevanlinna normalization.

Continuity of the Möbius action on `OnePoint ℝ` is obtained on the finite chart by exhibiting the
action as the projective label of an auxiliary determinant-one matrix data, and at `∞` by the
cocompact limit of the Möbius quotient.
-/

open Filter Topology OnePoint Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace NevanlinnaNormalization

/-- The Möbius action of an `SL(2,ℝ)` element on the finite chart, as determinant-one matrix
data over `ℝ`. -/
def mobiusChartData (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : NevanlinnaMatrixData ℝ where
  a := fun _ => g.1 1 0
  b := fun _ => -g.1 0 0
  c := fun τ => g.1 1 0 * τ + g.1 1 1
  d := fun τ => -(g.1 0 0 * τ + g.1 0 1)
  det_one := by
    intro τ
    have hdet := g.2
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet

theorem toGL_entry (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) :
    (g.toGL : Matrix (Fin 2) (Fin 2) ℝ) i j = g.1 i j := rfl

/-- On the finite chart the Möbius action is the projective label of the chart data. -/
theorem smul_coe_eq_label (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : ℝ) :
    g.toGL • (τ : OnePoint ℝ) = (mobiusChartData g).projectiveLabel τ := by
  rw [OnePoint.smul_some_eq_ite]
  unfold NevanlinnaMatrixData.projectiveLabel mobiusChartData
  simp only [toGL_entry]
  by_cases hden : g.1 1 0 * τ + g.1 1 1 = 0
  · simp [hden]
  · simp only [hden, if_false]
    rw [OnePoint.coe_eq_coe]
    rw [neg_neg]

/-- No point of the projective line is annihilated by both rows. -/
theorem row_ne_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {σ : ℝ}
    (hden : g.1 1 0 * σ + g.1 1 1 = 0) :
    g.1 0 0 * σ + g.1 0 1 ≠ 0 := by
  intro hnum
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h1 : (g.1 0 0 * σ + g.1 0 1) * g.1 1 1 - (g.1 1 0 * σ + g.1 1 1) * g.1 0 1 =
      σ * (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0) := by ring
  rw [hnum, hden] at h1
  simp only [zero_mul, sub_zero] at h1
  have hσ : σ * (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0) = 0 := by linarith
  rw [hdet] at hσ
  rw [mul_one] at hσ
  subst hσ
  rw [mul_zero, zero_add] at hden hnum
  rw [hden, hnum] at hdet
  simp at hdet

/-- Cocompact convergence of the Möbius quotient when the lower-left entry does not vanish. -/
theorem tendsto_mobius_cocompact_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hg : g.1 1 0 ≠ 0) :
    Tendsto (fun τ : ℝ => g.toGL • (τ : OnePoint ℝ)) (cocompact ℝ)
      (𝓝 ((g.1 0 0 / g.1 1 0 : ℝ) : OnePoint ℝ)) := by
  have hinv : Tendsto (fun τ : ℝ => τ⁻¹) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    exact ⟨tendsto_inv_atBot_zero, tendsto_inv_atTop_zero⟩
  have hnum : Tendsto (fun τ : ℝ => g.1 0 0 + g.1 0 1 * τ⁻¹) (cocompact ℝ)
      (𝓝 (g.1 0 0)) := by
    have := (hinv.const_mul (g.1 0 1)).const_add (g.1 0 0)
    simpa using this
  have hden : Tendsto (fun τ : ℝ => g.1 1 0 + g.1 1 1 * τ⁻¹) (cocompact ℝ)
      (𝓝 (g.1 1 0)) := by
    have := (hinv.const_mul (g.1 1 1)).const_add (g.1 1 0)
    simpa using this
  have hratio : Tendsto (fun τ : ℝ =>
      (g.1 0 0 + g.1 0 1 * τ⁻¹) / (g.1 1 0 + g.1 1 1 * τ⁻¹)) (cocompact ℝ)
      (𝓝 (g.1 0 0 / g.1 1 0)) := hnum.div hden hg
  have hne0 : ∀ᶠ τ : ℝ in cocompact ℝ, τ ≠ 0 := by
    have hmem : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ cocompact ℝ := by
      rw [mem_cocompact]
      exact ⟨{0}, isCompact_singleton, le_rfl⟩
    filter_upwards [hmem] with τ hτ
    exact hτ
  have hdenne : ∀ᶠ τ : ℝ in cocompact ℝ, g.1 1 0 + g.1 1 1 * τ⁻¹ ≠ 0 :=
    hden.eventually_ne hg
  have hcoe := (OnePoint.continuous_coe.tendsto _).comp hratio
  refine hcoe.congr' ?_
  filter_upwards [hne0, hdenne] with τ hτ hdτ
  have hbig : g.1 1 0 * τ + g.1 1 1 ≠ 0 := by
    intro hzero
    apply hdτ
    field_simp
    linear_combination hzero
  rw [Function.comp_apply, OnePoint.smul_some_eq_ite]
  simp only [toGL_entry, hbig, if_false]
  rw [OnePoint.coe_eq_coe]
  field_simp

/-- Cocompact escape of the affine action when the lower-left entry vanishes. -/
theorem tendsto_mobius_cocompact_zero (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hg : g.1 1 0 = 0) :
    Tendsto (fun τ : ℝ => g.toGL • (τ : OnePoint ℝ)) (cocompact ℝ)
      (𝓝 (∞ : OnePoint ℝ)) := by
  have hdet := g.2
  rw [Matrix.det_fin_two, hg] at hdet
  have h11 : g.1 1 1 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have h00 : g.1 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hk : g.1 0 0 / g.1 1 1 ≠ 0 := div_ne_zero h00 h11
  have haffine : Tendsto (fun τ : ℝ =>
      g.1 0 0 / g.1 1 1 * τ + g.1 0 1 / g.1 1 1) (cocompact ℝ) (cocompact ℝ) := by
    have hhomeo := ((Homeomorph.mulLeft₀ (g.1 0 0 / g.1 1 1) hk).trans
      (Homeomorph.addRight (g.1 0 1 / g.1 1 1))).isClosedEmbedding.tendsto_cocompact
    refine hhomeo.congr ?_
    intro τ
    rfl
  have hcoeInf : Tendsto ((↑) : ℝ → OnePoint ℝ) (cocompact ℝ) (𝓝 (∞ : OnePoint ℝ)) := by
    show Filter.map _ (cocompact ℝ) ≤ _
    rw [OnePoint.nhds_infty_eq, ← Filter.coclosedCompact_eq_cocompact]
    exact le_sup_left
  have hcomp := hcoeInf.comp haffine
  refine hcomp.congr' ?_
  filter_upwards with τ
  have hbig : g.1 1 0 * τ + g.1 1 1 ≠ 0 := by
    rw [hg, zero_mul, zero_add]
    exact h11
  rw [Function.comp_apply, OnePoint.smul_some_eq_ite]
  simp only [toGL_entry, hbig, if_false]
  rw [OnePoint.coe_eq_coe, hg, zero_mul, zero_add]
  field_simp

/-- **The Möbius action on the projective line is continuous.** -/
theorem continuous_smul_onePoint (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Continuous (fun t : OnePoint ℝ => g.toGL • t) := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact]
    by_cases hg : g.1 1 0 = 0
    · have hval : g.toGL • (∞ : OnePoint ℝ) = ∞ := by
        rw [OnePoint.smul_infty_eq_ite]
        simp [toGL_entry, hg]
      rw [hval]
      exact tendsto_mobius_cocompact_zero g hg
    · have hval : g.toGL • (∞ : OnePoint ℝ) =
          ((g.1 0 0 / g.1 1 0 : ℝ) : OnePoint ℝ) := by
        rw [OnePoint.smul_infty_eq_ite]
        simp [toGL_entry, hg]
      rw [hval]
      exact tendsto_mobius_cocompact_ne g hg
  · have hlabel := (mobiusChartData g).continuous_projectiveLabel
      (by fun_prop) (by fun_prop)
    refine hlabel.congr ?_
    intro τ
    exact (smul_coe_eq_label g τ).symm

end NevanlinnaNormalization

end

end GaloisForLFunctions.HTGeometry
