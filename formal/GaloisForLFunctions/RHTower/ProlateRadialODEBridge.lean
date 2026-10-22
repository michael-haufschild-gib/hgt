import GaloisForLFunctions.RHTower.ProlateSeparationEnergy
import GaloisForLFunctions.RHTower.CCM.CCMRadialProlateDefect

/-!
# From the angular prolate action to the exterior radial equation

The canonical band representative is an entire real-line function.  Once Slepian commutation has
propagated its prolate eigen-equation globally, the same equation on `x > 1` is exactly the radial
prolate equation used by the Dunster/Volterra comparison layer.  This module records that sign and
normalization conversion without an asymptotic premise.
-/

noncomputable section

namespace RHTower

open Set

/-- The separation ratio in the radial convention.  The corpus's angular action has eigenvalue
`chi`, whereas the radial normal form writes that parameter as `-s c²`. -/
def radialSeparationRatio (c chi : ℝ) : ℝ := -chi / c ^ (2 : ℕ)

/-- A global eigenfunction of the angular prolate action satisfies the exterior radial prolate
equation with `s = -chi/c²`. -/
theorem radialProlate_ode_of_prolateSLAction_eq
    {c chi : ℝ} (hc : c ≠ 0) {Phi : ℝ → ℝ}
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    ∀ x : ℝ,
      (x ^ (2 : ℕ) - 1) * deriv (deriv Phi) x + 2 * x * deriv Phi x
          - (radialSeparationRatio c chi * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * Phi x = 0 := by
  intro x
  have hx := heig x
  simp only [prolateSLAction, radialSeparationRatio] at hx ⊢
  field_simp [hc] at hx ⊢
  nlinarith

/-- The singular radial endpoint fixes the derivative of every smooth prolate solution. -/
theorem two_mul_deriv_one_eq_of_prolateSLAction_eq
    {c chi : ℝ} {Phi : ℝ → ℝ}
    (heig : prolateSLAction c Phi 1 = chi * Phi 1) :
    2 * deriv Phi 1 = -(chi + c ^ (2 : ℕ)) * Phi 1 := by
  simp only [prolateSLAction] at heig
  norm_num at heig ⊢
  nlinarith

/-- Endpoint relation in the radial sign convention `chi = -s c²`. -/
theorem two_mul_deriv_one_eq_radial
    {c chi : ℝ} (hc : c ≠ 0) {Phi : ℝ → ℝ}
    (heig : prolateSLAction c Phi 1 = chi * Phi 1) :
    2 * deriv Phi 1 =
      (radialSeparationRatio c chi * c ^ (2 : ℕ) - c ^ (2 : ℕ)) * Phi 1 := by
  rw [two_mul_deriv_one_eq_of_prolateSLAction_eq heig]
  dsimp [radialSeparationRatio]
  field_simp [hc]
  ring

/-- Every live signed finite-Fourier mode supplies an exact smooth even global solution of the
radial prolate equation at bandwidth `2πa²`.  No Dunster approximation or asymptotic hypothesis is
used here. -/
theorem exists_global_even_radialProlate_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Phi : ℝ → ℝ) (chi s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
        Phi ≠ 0 ∧ Function.Even Phi ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ (2 : ℕ)) Phi x =
            evenProlateSignedValue a n ^ (2 : ℕ) * Phi x) ∧
        (∀ x : ℝ,
          prolateSLAction (2 * Real.pi * a ^ (2 : ℕ)) Phi x = chi * Phi x) ∧
        s = radialSeparationRatio (2 * Real.pi * a ^ (2 : ℕ)) chi ∧
        0 ≤ s ∧
        2 * deriv Phi 1 =
          (s * (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ) - (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ)) * Phi 1 ∧
        (∀ x : ℝ,
          (x ^ (2 : ℕ) - 1) * deriv (deriv Phi) x + 2 * x * deriv Phi x
            - (s * (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ)
                - (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ) * x ^ (2 : ℕ)) * Phi x = 0) := by
  obtain ⟨Phi, chi, hsm, hne, heven, hband, heig⟩ :=
    exists_joint_even_prolate_band_eigen_of_signedMode ha n hvalue
  let c : ℝ := 2 * Real.pi * a ^ (2 : ℕ)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hchi : chi ≤ 0 :=
    GaloisForLFunctions.RHTower.prolateSeparation_nonpos_of_global_joint
      (pow_ne_zero 2 hvalue) hsm hne hband heig
  refine ⟨Phi, chi, radialSeparationRatio c chi, hsm, hne, heven, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simpa [c] using hband
  · simpa [c] using heig
  · exact div_nonneg (neg_nonneg.mpr hchi) (sq_nonneg c)
  · simpa [c] using two_mul_deriv_one_eq_radial hc (heig 1)
  · simpa [c] using radialProlate_ode_of_prolateSLAction_eq hc heig

end RHTower

end
