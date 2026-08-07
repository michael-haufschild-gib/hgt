import GaloisForLFunctions.RHTower.ProlateSeparationEnergy
import GaloisForLFunctions.RHTower.CCMRadialProlateDefect

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
def radialSeparationRatio (c chi : ℝ) : ℝ := -chi / c ^ 2

/-- A global eigenfunction of the angular prolate action satisfies the exterior radial prolate
equation with `s = -chi/c²`. -/
theorem radialProlate_ode_of_prolateSLAction_eq
    {c chi : ℝ} (hc : c ≠ 0) {Phi : ℝ → ℝ}
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    ∀ x : ℝ,
      (x ^ 2 - 1) * deriv (deriv Phi) x + 2 * x * deriv Phi x
          - (radialSeparationRatio c chi * c ^ 2 - c ^ 2 * x ^ 2) * Phi x = 0 := by
  intro x
  have hx := heig x
  simp only [prolateSLAction, radialSeparationRatio] at hx ⊢
  field_simp [hc] at hx ⊢
  nlinarith

/-- Every live signed finite-Fourier mode supplies an exact smooth even global solution of the
radial prolate equation at bandwidth `2πa²`.  No Dunster approximation or asymptotic hypothesis is
used here. -/
theorem exists_global_even_radialProlate_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Phi : ℝ → ℝ) (chi s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
        Phi ≠ 0 ∧ Function.Even Phi ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ 2) Phi x =
            evenProlateSignedValue a n ^ 2 * Phi x) ∧
        (∀ x : ℝ,
          prolateSLAction (2 * Real.pi * a ^ 2) Phi x = chi * Phi x) ∧
        s = radialSeparationRatio (2 * Real.pi * a ^ 2) chi ∧
        0 ≤ s ∧
        (∀ x : ℝ,
          (x ^ 2 - 1) * deriv (deriv Phi) x + 2 * x * deriv Phi x
            - (s * (2 * Real.pi * a ^ 2) ^ 2
                - (2 * Real.pi * a ^ 2) ^ 2 * x ^ 2) * Phi x = 0) := by
  obtain ⟨Phi, chi, hsm, hne, heven, hband, heig⟩ :=
    exists_joint_even_prolate_band_eigen_of_signedMode ha n hvalue
  let c : ℝ := 2 * Real.pi * a ^ 2
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hchi : chi ≤ 0 :=
    GaloisForLFunctions.RHTower.prolateSeparation_nonpos_of_global_joint
      (pow_ne_zero 2 hvalue) hsm hne hband heig
  refine ⟨Phi, chi, radialSeparationRatio c chi, hsm, hne, heven, ?_, ?_, rfl, ?_, ?_⟩
  · simpa [c] using hband
  · simpa [c] using heig
  · exact div_nonneg (neg_nonneg.mpr hchi) (sq_nonneg c)
  · simpa [c] using radialProlate_ode_of_prolateSLAction_eq hc heig

end RHTower

end
