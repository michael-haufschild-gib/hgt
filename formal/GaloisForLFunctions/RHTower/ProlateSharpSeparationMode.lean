import GaloisForLFunctions.RHTower.ProlateGaussianSharpRayleigh
import GaloisForLFunctions.RHTower.ProlateLowSeparationMode

/-!
# A prolate mode whose oscillator separation constant is below one

The threshold-parametric variational principle turns any Gaussian Rayleigh bound into an actual
joint band/prolate eigenfunction above that threshold.  Fed with the sharp Gaussian estimate
`⟨L_c v, v⟩ > −c‖v‖²` it produces, at every positive bandwidth, an even joint mode with

`−η < c` ,   i.e.   `s = −η/c² < 1/c` ,   i.e.   `c·s < 1` .

The scale `c·s` is the separation constant of the Hermite-rescaled profile, so this is the statement
that some mode sits at the bottom of the oscillator ladder, uniformly in the bandwidth.  The earlier
threshold `c²/2` only gave `s < 1/2`, which is a statement about the turning point and carries no
information at the Hermite scale.
-/

open Real MeasureTheory Set

namespace RHTower

/-- **A mode with bounded oscillator separation constant.**  At every positive bandwidth some even
joint band/prolate eigenfunction has `c · s < 1`. -/
theorem exists_even_joint_prolate_eigen_bandwidth_separation_lt_one {c : ℝ} (hc : 0 < c) :
    ∃ (lam eta : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
      c * radialSeparationRatio c eta < 1 := by
  obtain ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, hprolate, heta⟩ :=
    exists_even_joint_prolate_eigen_gt_of_rayleigh_gt (K := c) hc
      (prolate_gaussian_rayleigh_gt_neg_bandwidth hc)
  refine ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, hprolate, ?_⟩
  have hcne : c ≠ 0 := ne_of_gt hc
  have hid : c * radialSeparationRatio c eta = -eta / c := by
    rw [radialSeparationRatio]
    field_simp
  rw [hid, div_lt_one hc]
  linarith

end RHTower
