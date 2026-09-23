import GaloisForLFunctions.RHTower.ProlateRadialODEBridge

/-!
# Exact Hermite-scale equation for genuine prolate modes

For a bandwidth `c > 0`, the central profile is `u(ξ) = Phi(ξ/√c)`.  This module applies the
existing algebraic prolate-to-Hermite scaling identity to an actual global prolate eigenfunction.
The resulting defect is exact and carries its full `1/c` factor; no convergence premise is used.
-/

noncomputable section

namespace RHTower

/-- Central Hermite rescaling of a prolate profile. -/
def prolateHermiteRescale (c : ℝ) (Phi : ℝ → ℝ) (xi : ℝ) : ℝ :=
  Phi (xi / Real.sqrt c)

/-- Rescaling back by `√c` recovers the original profile exactly. -/
theorem prolateHermiteRescale_sqrtScale {c : ℝ} (hc : 0 < c) (Phi : ℝ → ℝ) :
    (fun y : ℝ => prolateHermiteRescale c Phi (Real.sqrt c * y)) = Phi := by
  funext y
  dsimp [prolateHermiteRescale]
  rw [mul_div_cancel_left₀ y (Real.sqrt_ne_zero'.mpr hc)]

/-- The rescaling preserves evenness. -/
theorem even_prolateHermiteRescale {c : ℝ} {Phi : ℝ → ℝ}
    (hPhi : Function.Even Phi) : Function.Even (prolateHermiteRescale c Phi) := by
  intro x
  dsimp [prolateHermiteRescale]
  rw [neg_div, hPhi]

/-- The rescaling preserves global smoothness. -/
theorem contDiff_prolateHermiteRescale {c : ℝ} {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prolateHermiteRescale c Phi) := by
  unfold prolateHermiteRescale
  exact hPhi.comp (by fun_prop)

/-- Exact Hermite defect of a genuine global prolate eigenfunction. -/
theorem prolateHermiteRescale_eigen_defect
    {c chi : ℝ} (hc : 0 < c) {Phi : ℝ → ℝ}
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) (xi : ℝ) :
    hermiteSLAction (prolateHermiteRescale c Phi) xi
        - chi / c * prolateHermiteRescale c Phi xi =
      (xi ^ (2 : ℕ) * deriv (deriv (prolateHermiteRescale c Phi)) xi
          + 2 * xi * deriv (prolateHermiteRescale c Phi) xi) / c := by
  apply prolate_eigen_hermite_defect hc
  rw [prolateHermiteRescale_sqrtScale hc Phi]
  exact heig (xi / Real.sqrt c)

/-- Radial form: the limiting oscillator eigenvalue is `-chi/c = c·s`. -/
theorem prolateHermiteRescale_radial_defect
    {c chi : ℝ} (hc : 0 < c) {Phi : ℝ → ℝ}
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) (xi : ℝ) :
    hermiteSLAction (prolateHermiteRescale c Phi) xi
        + (c * radialSeparationRatio c chi) * prolateHermiteRescale c Phi xi =
      (xi ^ (2 : ℕ) * deriv (deriv (prolateHermiteRescale c Phi)) xi
          + 2 * xi * deriv (prolateHermiteRescale c Phi) xi) / c := by
  have h := prolateHermiteRescale_eigen_defect hc heig xi
  have hc0 : c ≠ 0 := hc.ne'
  dsimp [radialSeparationRatio]
  field_simp [hc0] at h ⊢
  linarith

/-- Every live signed finite-Fourier mode admits a genuine smooth even Hermite-scale profile with
the exact radial oscillator defect and a nonnegative radial separation ratio. -/
theorem exists_even_prolateHermiteRescale_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Phi u : ℝ → ℝ) (chi s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
        Phi ≠ 0 ∧ Function.Even Phi ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ (2 : ℕ)) Phi x =
            evenProlateSignedValue a n ^ (2 : ℕ) * Phi x) ∧
        (∀ x : ℝ,
          prolateSLAction (2 * Real.pi * a ^ (2 : ℕ)) Phi x = chi * Phi x) ∧
        s = radialSeparationRatio (2 * Real.pi * a ^ (2 : ℕ)) chi ∧
        0 ≤ s ∧
        u = prolateHermiteRescale (2 * Real.pi * a ^ (2 : ℕ)) Phi ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧ Function.Even u ∧
        (∀ xi : ℝ,
          hermiteSLAction u xi + (2 * Real.pi * a ^ (2 : ℕ)) * s * u xi =
            (xi ^ (2 : ℕ) * deriv (deriv u) xi + 2 * xi * deriv u xi)
              / (2 * Real.pi * a ^ (2 : ℕ))) := by
  obtain ⟨Phi, chi, s, hsm, hne, heven, hband, heig, hs, hs0, _hend, _hradial⟩ :=
    exists_global_even_radialProlate_of_signedMode ha n hvalue
  let c : ℝ := 2 * Real.pi * a ^ (2 : ℕ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨Phi, prolateHermiteRescale c Phi, chi, s, hsm, hne, heven, ?_, ?_, ?_, hs0,
    rfl, contDiff_prolateHermiteRescale hsm, even_prolateHermiteRescale heven, ?_⟩
  · simpa [c] using hband
  · simpa [c] using heig
  · simpa [c] using hs
  · intro xi
    have hdef := prolateHermiteRescale_radial_defect hc (by simpa [c] using heig) xi
    rw [← hs] at hdef
    simpa [c] using hdef

end RHTower

end
