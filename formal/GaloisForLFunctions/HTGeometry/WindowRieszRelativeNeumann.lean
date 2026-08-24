import GaloisForLFunctions.HTGeometry.BoundedResolventNeumann

/-!
# Relative Neumann criterion for a window Riesz gap

The strict relative estimate `‖F₀⁻¹(F₁-F₀)‖ < 1` keeps the entire linear homotopy
between an invertible reference and its target invertible.  Conversely, the scalar family
`F(z)=z` has inverse norm one on the unit circle but remains singular at the enclosed origin.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
  [CompleteSpace 𝔸]

/-- Relative defect `F₀⁻¹(F₁-F₀)` from the window homotopy criterion. -/
def relativeFredholmDefect (F₀ : 𝔸ˣ) (F₁ : 𝔸) : 𝔸 :=
  (↑(F₀⁻¹) : 𝔸) * (F₁ - (F₀ : 𝔸))

/-- Linear homotopy between an invertible reference and a target. -/
def relativeFredholmHomotopy (F₀ : 𝔸ˣ) (F₁ : 𝔸) (t : ℝ) : 𝔸 :=
  (F₀ : 𝔸) + (t : ℂ) • (F₁ - (F₀ : 𝔸))

omit [CompleteSpace 𝔸] in
theorem relativeFredholmHomotopy_factor (F₀ : 𝔸ˣ) (F₁ : 𝔸) (t : ℝ) :
    relativeFredholmHomotopy F₀ F₁ t =
      (F₀ : 𝔸) * (1 + (t : ℂ) • relativeFredholmDefect F₀ F₁) := by
  rw [relativeFredholmHomotopy, relativeFredholmDefect, mul_add, mul_one,
    mul_smul_comm, ← mul_assoc]
  simp

omit [CompleteSpace 𝔸] in
theorem norm_smul_relativeFredholmDefect_lt_one
    (F₀ : 𝔸ˣ) (F₁ : 𝔸) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hdefect : ‖relativeFredholmDefect F₀ F₁‖ < 1) :
    ‖(t : ℂ) • relativeFredholmDefect F₀ F₁‖ < 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht₀]
  calc
    t * ‖relativeFredholmDefect F₀ F₁‖ ≤
        1 * ‖relativeFredholmDefect F₀ F₁‖ := by gcongr
    _ < 1 := by simpa using hdefect

/-- The strict relative `<1` estimate keeps every point of the linear homotopy invertible. -/
theorem isUnit_relativeFredholmHomotopy
    (F₀ : 𝔸ˣ) (F₁ : 𝔸) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hdefect : ‖relativeFredholmDefect F₀ F₁‖ < 1) :
    IsUnit (relativeFredholmHomotopy F₀ F₁ t) := by
  have hsmall := norm_smul_relativeFredholmDefect_lt_one F₀ F₁ ht₀ ht₁ hdefect
  have hfactor : IsUnit
      (1 + (t : ℂ) • relativeFredholmDefect F₀ F₁) := by
    have h := (Units.oneSub (-(t : ℂ) • relativeFredholmDefect F₀ F₁) (by
      simpa using hsmall)).isUnit
    simpa [sub_neg_eq_add] using h
  rw [relativeFredholmHomotopy_factor]
  exact F₀.isUnit.mul hfactor

/-- Pointwise boundary form of the relative homotopy theorem. -/
theorem relativeFredholmHomotopy_isUnit_on
    {Z : Type*} (boundary : Set Z) (F₀ : Z → 𝔸ˣ) (F₁ : Z → 𝔸)
    (hdefect : ∀ z ∈ boundary, ‖relativeFredholmDefect (F₀ z) (F₁ z)‖ < 1) :
    ∀ z ∈ boundary, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      IsUnit (relativeFredholmHomotopy (F₀ z) (F₁ z) t) := by
  intro z hz t ht₀ ht₁
  exact isUnit_relativeFredholmHomotopy (F₀ z) (F₁ z) ht₀ ht₁
    (hdefect z hz)

/-- The scalar family `F(z)=z` has unit inverse norm on the unit circle. -/
theorem scalarIdentityFamily_isUnit_and_norm_inv_eq_one
    {z : ℂ} (hz : ‖z‖ = 1) : IsUnit z ∧ ‖z⁻¹‖ = 1 := by
  have hne : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    norm_num at hz
  exact ⟨isUnit_iff_ne_zero.mpr hne, by simp [norm_inv, hz]⟩

/-- Finite (indeed unit) boundary resolvent norm does not force interior invertibility. -/
theorem exists_scalarFamily_boundary_resolvent_bounded_but_interior_singular :
    ∃ F : ℂ → ℂ,
      (∀ z, ‖z‖ = 1 → IsUnit (F z) ∧ ‖(F z)⁻¹‖ = 1) ∧
        ¬ IsUnit (F 0) := by
  refine ⟨id, ?_, ?_⟩
  · intro z hz
    exact scalarIdentityFamily_isUnit_and_norm_inv_eq_one hz
  · exact not_isUnit_zero

end

end GaloisForLFunctions.HTGeometry
