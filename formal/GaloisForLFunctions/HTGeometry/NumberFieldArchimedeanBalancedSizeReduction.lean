import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanDeterminantProfile

/-!
# Determinant-profile-balanced archimedean size reduction

Unit balancing and mixed unipotent size reduction already produce multiplicative bounds relative to
coordinate means and a place-only profile.  Taking logarithms identifies that place profile with
the orbit-invariant centered local determinant.  Thus the reduced Jacobi weights lie in a uniform
additive tube around coordinate constants plus the determinant profile, while both real and complex
upper-unipotent entries are uniformly bounded.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Logarithmic Jacobi weights are uniformly close to coordinate constants plus the centered
determinant profile. -/
def NumberFieldArchimedeanJacobiData.IsDetBalanced
    {m : ℕ} {A : numberFieldArchimedeanPositiveForms K (m + 1)}
    (J : NumberFieldArchimedeanJacobiData A) (R : ℝ) : Prop :=
  ∃ a : Fin (m + 1) → ℝ, ∀ i w,
    |Real.log (numberFieldArchimedeanJacobiWeight J i w) -
      (a i + numberFieldCenteredPlaceProfileAverage
        (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)| ≤ R

/-- Multiplicative exponential bounds imply the corresponding additive logarithmic bound. -/
theorem abs_log_sub_le_of_exp_mul_le
    {x s C : ℝ} (hx : 0 < x)
    (hlow : Real.exp (-C) * Real.exp s ≤ x)
    (hupp : x ≤ Real.exp C * Real.exp s) :
    |Real.log x - s| ≤ C := by
  have hlo : -C + s ≤ Real.log x := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hlow
    rw [← Real.exp_add, Real.log_exp] at h
    exact h
  have hhi : Real.log x ≤ C + s := by
    have h := Real.log_le_log hx hupp
    rw [← Real.exp_add, Real.log_exp] at h
    exact h
  rw [abs_le]
  constructor <;> linarith

/-- Unit balancing followed by mixed unipotent size reduction produces Jacobi data that are
uniformly determinant-profile-balanced and have uniformly bounded real/complex upper factors. -/
theorem exists_numberFieldArchimedean_balancedSizeReductionRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
        ∃ hu : ∏ i, u i = 1,
          let A₁ := (numberFieldUnitSpecialLinear u hu) • A
          ∃ g₂ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K),
            ∃ J₂ : NumberFieldArchimedeanJacobiData (g₂ • A₁),
              (∀ w i j, i < j → |J₂.realU w i j| ≤ C) ∧
              (∀ w i j, i < j → ‖J₂.complexU w i j‖ ≤ C) ∧
              J₂.IsDetBalanced (2 * (m + 1 : ℝ) * R) := by
  obtain ⟨R, C, hR, hC, hreduce⟩ :=
    exists_numberFieldArchimedeanSiegelReductionRadius K
  refine ⟨R, C, hR, hC, ?_⟩
  intro m A
  obtain ⟨J, u, hu, g₂, J₂, hreal, hcomplex, hbounds⟩ := hreduce m A
  refine ⟨u, hu, g₂, J₂, hreal, hcomplex, ?_⟩
  let A₁ := (numberFieldUnitSpecialLinear u hu) • A
  let J₁ : NumberFieldArchimedeanJacobiData A₁ :=
    numberFieldArchimedeanJacobiUnitConj A J u hu
  let a : Fin (m + 1) → ℝ := fun i =>
    numberFieldWeightedPlaceMean
      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))
  refine ⟨a, ?_⟩
  intro i w
  have hcenter :
      numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₂ j v)) w =
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w := by
    calc
      _ = numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₁ j v)) w :=
        numberFieldCenteredJacobiProfile_smul J₁ g₂ J₂ w
      _ = _ := numberFieldCenteredJacobiProfile_smul J
        (numberFieldUnitSpecialLinear u hu) J₁ w
  have hb := hbounds i w
  have hlog := abs_log_sub_le_of_exp_mul_le
    (numberFieldArchimedeanJacobiWeight_pos J₂ i w)
    (s := a i + numberFieldCenteredPlaceProfileAverage
      (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)
    (C := 2 * (m + 1 : ℝ) * R)
    (by simpa [a, Real.exp_add] using hb.1)
    (by simpa [a, Real.exp_add] using hb.2)
  rw [hcenter]
  exact hlog

end

end GaloisForLFunctions.HTGeometry
