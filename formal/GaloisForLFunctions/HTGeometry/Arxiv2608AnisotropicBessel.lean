import GaloisForLFunctions.RHTower.BesselJZeroODE

/-!
# Anisotropic Bessel propagation from arXiv:2608.18478

This module formalizes the parameter identities and the isotropic `J₀` radial mode behind equations
(7)--(13) and (29)--(46) of Escobar--Linares--Plácido-Flores.  The physical interval `-1 < λ < 1`
is part of the parameter type, so every theorem is closed and carries no analytic side hypothesis.

The branch rule has a useful invariant form: the selected Bessel order is exactly `-σ`.  Hence the
radial prefactor and the small-argument Bessel power cancel for either sign of the anisotropy.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Physical anisotropy range used in arXiv:2608.18478. -/
abbrev EscobarAnisotropy := Set.Ioo (-1 : ℝ) 1

/-- Positive radial coordinate, used to absorb the regular-singular endpoint condition. -/
abbrev PositiveRadius := Set.Ioi (0 : ℝ)

/-- Equation (10): radial conjugation exponent. -/
def escobarSigma (lam : EscobarAnisotropy) : ℝ :=
  (lam : ℝ) / (2 * ((lam : ℝ) - 1))

/-- Equation (8): nonnegative effective Bessel order in the axisymmetric sector. -/
def escobarAxisymmetricOrder (lam : EscobarAnisotropy) : ℝ :=
  |(lam : ℝ)| / (2 * (1 - (lam : ℝ)))

/-- Equation (11): signed order of the branch compatible with a bright axis. -/
def escobarBranchOrder (lam : EscobarAnisotropy) : ℝ :=
  if 0 ≤ (lam : ℝ) then escobarAxisymmetricOrder lam else -escobarAxisymmetricOrder lam

/-- Equation (30), recorded as a squared dispersion law to avoid an artificial square-root choice. -/
def escobarBetaSq (lam : EscobarAnisotropy) (Ω η : ℝ) : ℝ :=
  Ω ^ 2 - (1 - (lam : ℝ)) * η ^ 2

/-- The physical anisotropy never changes the sign of the radial kinetic coefficient. -/
theorem escobar_one_sub_anisotropy_pos (lam : EscobarAnisotropy) :
    0 < 1 - (lam : ℝ) := by
  exact sub_pos.mpr lam.property.2

/-- Effective axisymmetric order is nonnegative. -/
theorem escobarAxisymmetricOrder_nonneg (lam : EscobarAnisotropy) :
    0 ≤ escobarAxisymmetricOrder lam := by
  exact div_nonneg (abs_nonneg _)
    (mul_nonneg (by norm_num) (escobar_one_sub_anisotropy_pos lam).le)

/-- The paper's sign-dependent branch is uniformly the order `-σ`. -/
theorem escobarBranchOrder_eq_neg_sigma (lam : EscobarAnisotropy) :
    escobarBranchOrder lam = -escobarSigma lam := by
  have hden : 1 - (lam : ℝ) ≠ 0 := ne_of_gt (escobar_one_sub_anisotropy_pos lam)
  have hden' : (lam : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt lam.property.2)
  rw [escobarBranchOrder]
  split_ifs with hnonneg
  · rw [escobarAxisymmetricOrder, abs_of_nonneg hnonneg, escobarSigma]
    field_simp [hden, hden']
    ring
  · have hneg : (lam : ℝ) < 0 := lt_of_not_ge hnonneg
    rw [escobarAxisymmetricOrder, abs_of_neg hneg, escobarSigma]
    field_simp [hden, hden']
    ring

/-- Equations (35)--(36): selected small-axis exponent vanishes for every physical `λ`. -/
theorem escobar_branch_exponent_eq_zero (lam : EscobarAnisotropy) :
    escobarSigma lam + escobarBranchOrder lam = 0 := by
  rw [escobarBranchOrder_eq_neg_sigma]
  ring

/-- Equation (45): the two presentations of the inverse-Hankel input weight agree. -/
theorem escobar_input_weight_exponent_eq (lam : EscobarAnisotropy) :
    1 - escobarSigma lam = escobarSigma lam + 1 / (1 - (lam : ℝ)) := by
  have hden : 1 - (lam : ℝ) ≠ 0 := ne_of_gt (escobar_one_sub_anisotropy_pos lam)
  have hden' : (lam : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt lam.property.2)
  rw [escobarSigma]
  field_simp [hden, hden']
  ring

/-- Equation (30): dispersion reconstruction after moving the radial term to the left. -/
theorem escobarBetaSq_add_radial (lam : EscobarAnisotropy) (Ω η : ℝ) :
    escobarBetaSq lam Ω η + (1 - (lam : ℝ)) * η ^ 2 = Ω ^ 2 := by
  simp [escobarBetaSq]

/-- Isotropic point of the physical anisotropy interval. -/
def escobarZeroAnisotropy : EscobarAnisotropy := ⟨0, by norm_num⟩

@[simp] theorem escobarSigma_zero : escobarSigma escobarZeroAnisotropy = 0 := by
  norm_num [escobarSigma, escobarZeroAnisotropy]

@[simp] theorem escobarAxisymmetricOrder_zero :
    escobarAxisymmetricOrder escobarZeroAnisotropy = 0 := by
  norm_num [escobarAxisymmetricOrder, escobarZeroAnisotropy]

@[simp] theorem escobarBranchOrder_zero : escobarBranchOrder escobarZeroAnisotropy = 0 := by
  norm_num [escobarBranchOrder, escobarAxisymmetricOrder, escobarZeroAnisotropy]

@[simp] theorem escobarBetaSq_zero (Ω η : ℝ) :
    escobarBetaSq escobarZeroAnisotropy Ω η = Ω ^ 2 - η ^ 2 := by
  simp [escobarBetaSq, escobarZeroAnisotropy]

/-! ## Certified isotropic radial mode -/

/-- The paper's regular radial mode at `λ = 0`. -/
def escobarIsotropicRadialMode (η r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ0 (η * r)

/-- First radial derivative of the isotropic mode. -/
def escobarIsotropicRadialModeDeriv (η r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ0Deriv (η * r) * η

/-- Second radial derivative of the isotropic mode. -/
def escobarIsotropicRadialModeSecond (η r : ℝ) : ℝ :=
  η ^ 2 * GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r)

theorem hasDerivAt_escobarIsotropicRadialMode (η r : ℝ) :
    HasDerivAt (escobarIsotropicRadialMode η)
      (escobarIsotropicRadialModeDeriv η r) r := by
  have hinner : HasDerivAt (fun x : ℝ => η * x) η r := by
    simpa using (hasDerivAt_id r).const_mul η
  have h := (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0 (η * r)).comp r hinner
  exact h

theorem hasDerivAt_escobarIsotropicRadialModeDeriv (η r : ℝ) :
    HasDerivAt (escobarIsotropicRadialModeDeriv η)
      (escobarIsotropicRadialModeSecond η r) r := by
  have hinner : HasDerivAt (fun x : ℝ => η * x) η r := by
    simpa using (hasDerivAt_id r).const_mul η
  have h := (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0Deriv (η * r)).comp r
    hinner
  have h' := h.mul_const η
  have hval : GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r) * η * η =
      escobarIsotropicRadialModeSecond η r := by
    rw [escobarIsotropicRadialModeSecond]
    ring
  rw [hval] at h'
  exact h'

/-- Radial separated-equation residual from equation (29), with `β²` kept as one variable. -/
def escobarRadialResidual
    (lam : ℝ) (Ω betaSq r value first second : ℝ) : ℝ :=
  (1 - lam) * second + first / r + (Ω ^ 2 - betaSq) * value

/-- At `λ = 0`, corpus `J₀` is an exact, certified separated radial mode for every frequency and
radial spectral parameter.  The zero-frequency case is included, not assumed away. -/
theorem escobarIsotropicRadialMode_residual_zero
    (Ω η : ℝ) (r : PositiveRadius) :
    escobarRadialResidual 0 Ω (escobarBetaSq escobarZeroAnisotropy Ω η) r
      (escobarIsotropicRadialMode η r)
      (escobarIsotropicRadialModeDeriv η r)
      (escobarIsotropicRadialModeSecond η r) = 0 := by
  rcases r with ⟨r, hr⟩
  by_cases hη : η = 0
  · subst η
    simp [escobarRadialResidual, escobarIsotropicRadialMode,
      escobarIsotropicRadialModeDeriv, escobarIsotropicRadialModeSecond]
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hx : η * r ≠ 0 := mul_ne_zero hη hr0
    have hode := GaloisForLFunctions.RHTower.besselJ0_ode hx
    simp only [escobarRadialResidual, escobarBetaSq_zero,
      escobarIsotropicRadialMode, escobarIsotropicRadialModeDeriv,
      escobarIsotropicRadialModeSecond]
    calc
      (1 - 0) * (η ^ 2 * GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r)) +
            GaloisForLFunctions.RHTower.besselJ0Deriv (η * r) * η / r +
            (Ω ^ 2 - (Ω ^ 2 - η ^ 2)) * GaloisForLFunctions.RHTower.besselJ0 (η * r) =
          η ^ 2 * (GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r) +
            GaloisForLFunctions.RHTower.besselJ0Deriv (η * r) / (η * r) +
            GaloisForLFunctions.RHTower.besselJ0 (η * r)) := by
              field_simp [hη, hr0]
              ring
      _ = 0 := by rw [hode, mul_zero]

end GaloisForLFunctions.HTGeometry
