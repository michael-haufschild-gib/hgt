import GaloisForLFunctions.RHTower.ProlateBandSymmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import GaloisForLFunctions.RHTower.ProlateSeparationSimplicity

/-!
# Prolate modes at distinct eigenvalues are orthogonal on the aperture

The prolate Sturm–Liouville action is symmetric over `[−1,1]` with no boundary condition, so two
eigenfunctions with distinct eigenvalues pair to zero:

`η₁∫ΦΨ = ∫Ψ·(P_cΦ) = ∫Φ·(P_cΨ) = η₂∫ΦΨ` .

This is the orthogonality that lets a family of joint modes be used in the counting argument for the
differential ordering.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- **Orthogonality at distinct prolate eigenvalues.** -/
theorem integral_mul_eq_zero_of_distinct_prolate_eigen {c eta1 eta2 : ℝ} {Phi Psi : ℝ → ℝ}
    (h1sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (h2sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (h1 : ∀ x : ℝ, prolateSLAction c Phi x = eta1 * Phi x)
    (h2 : ∀ x : ℝ, prolateSLAction c Psi x = eta2 * Psi x)
    (hne : eta1 ≠ eta2) :
    (∫ x in (-1 : ℝ)..1, Phi x * Psi x) = 0 := by
  have hf1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp h1sm).1
  have hf2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp h1sm).2).1
  have hf2c : Continuous (deriv (deriv Phi)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp h1sm).2).2).continuous
  have hg1 : Differentiable ℝ Psi := (contDiff_infty_iff_deriv.mp h2sm).1
  have hg2 : Differentiable ℝ (deriv Psi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp h2sm).2).1
  have hg2c : Continuous (deriv (deriv Psi)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp h2sm).2).2).continuous
  have hsym := prolateSLAction_band_symmetric hf1 hf2 hf2c hg1 hg2 hg2c c
  have hleft : (∫ y in (-1 : ℝ)..1, Psi y * prolateSLAction c Phi y)
      = eta1 * ∫ y in (-1 : ℝ)..1, Phi y * Psi y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [h1 y]
    ring
  have hright : (∫ y in (-1 : ℝ)..1, Phi y * prolateSLAction c Psi y)
      = eta2 * ∫ y in (-1 : ℝ)..1, Phi y * Psi y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [h2 y]
    ring
  rw [hleft, hright] at hsym
  have hsub : (eta1 - eta2) * (∫ y in (-1 : ℝ)..1, Phi y * Psi y) = 0 := by
    linarith [hsym]
  rcases mul_eq_zero.1 hsub with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

/-- **Non-proportional even joint modes are orthogonal.**  A separation value determines the band
eigenvalue and the eigenline, so two even joint modes that are not multiples of one another must
have distinct separation values — and then the symmetry of the prolate action separates them. -/
theorem integral_mul_eq_zero_of_not_proportional
    {c lam1 lam2 chi1 chi2 : ℝ} {Phi Psi : ℝ → ℝ}
    (h1sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (h2sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (h1ne : Phi ≠ 0) (h2ne : Psi ≠ 0)
    (h1ev : Function.Even Phi) (h2ev : Function.Even Psi)
    (hlam1 : lam1 ≠ 0) (hlam2 : lam2 ≠ 0)
    (h1b : ∀ x : ℝ, bandTransform c Phi x = lam1 * Phi x)
    (h2b : ∀ x : ℝ, bandTransform c Psi x = lam2 * Psi x)
    (h1p : ∀ x : ℝ, prolateSLAction c Phi x = chi1 * Phi x)
    (h2p : ∀ x : ℝ, prolateSLAction c Psi x = chi2 * Psi x)
    (hnp : ¬ ∃ mu : ℝ, Phi = fun x => mu * Psi x) :
    (∫ x in (-1 : ℝ)..1, Phi x * Psi x) = 0 := by
  have hchi : chi1 ≠ chi2 := by
    intro h
    subst h
    obtain ⟨-, mu, hmu⟩ := eq_const_mul_of_same_even_joint_prolate_eigen
      h1sm h2sm h1ne h2ne h1ev h2ev hlam1 hlam2 h1b h2b h1p h2p
    exact hnp ⟨mu, hmu⟩
  exact integral_mul_eq_zero_of_distinct_prolate_eigen h1sm h2sm h1p h2p hchi

end RHTower
