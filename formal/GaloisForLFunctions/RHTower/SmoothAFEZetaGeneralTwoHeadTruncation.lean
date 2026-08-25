import GaloisForLFunctions.RHTower.SmoothAFETruncation
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralDualTruncation

/-!
# Two-head finite Gaussian approximate functional equation

Both exact contour edges are replaced by finite Dirichlet polynomials, with
the direct arbitrary-power tail and the reflected `p`-series tail displayed
separately.
-/

noncomputable section

namespace RHTower

open Complex

/-- The exact general-point Gaussian AFE with both Dirichlet edges truncated. -/
theorem exists_riemannZeta_sub_two_smoothAFE_heads_le
    {A : ℝ} (hA : 0 < A) {s : ℂ} {x : ℝ} (hx : 0 < x)
    (hs : s ≠ 1) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hsA : 1 < s.re + A) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ Ld Lu : ℕ, 1 ≤ Ld → 1 ≤ Lu →
      ‖riemannZeta s -
          ((∑ n ∈ Finset.range Ld,
              (((n + 1 : ℕ) : ℂ)) ^ (-s) *
                smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) -
            (∑ n ∈ Finset.range Lu,
              smoothAFEZetaDualCoefficientGeneral s x n) -
            smoothAFEZetaShiftedPoleResidue s x)‖ ≤
        C * x ^ A *
            (((Ld : ℝ)) ^ (1 - (s.re + A)) / (s.re + A - 1)) +
          K * (((Lu : ℝ)) ^ (s.re - 1) / (1 - s.re)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannZeta_sub_smoothAFE_head_le hA
  obtain ⟨K, hK0, hK⟩ :=
    exists_smoothAFEZetaDualMellinGeneral_sub_head_le hx h0 h1
  refine ⟨C, K, hC0, hK0, fun Ld Lu hLd hLu => ?_⟩
  let D : ℂ := ∑ n ∈ Finset.range Ld,
    (((n + 1 : ℕ) : ℂ)) ^ (-s) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)
  let M : ℂ := smoothAFEZetaDualMellinGeneral s x
  let H : ℂ := ∑ n ∈ Finset.range Lu,
    smoothAFEZetaDualCoefficientGeneral s x n
  let R : ℂ := smoothAFEZetaShiftedPoleResidue s x
  have hdirect : ‖riemannZeta s - (D - M - R)‖ ≤
      C * x ^ A *
        (((Ld : ℝ)) ^ (1 - (s.re + A)) / (s.re + A - 1)) := by
    simpa only [D, M, R] using
      hC s x Ld hx hs h0 (by linarith) hsA hLd
  have hdual : ‖M - H‖ ≤
      K * (((Lu : ℝ)) ^ (s.re - 1) / (1 - s.re)) := by
    simpa only [M, H] using hK Lu hLu
  have hdecomp : riemannZeta s - (D - H - R) =
      (riemannZeta s - (D - M - R)) - (M - H) := by ring
  change ‖riemannZeta s - (D - H - R)‖ ≤ _
  rw [hdecomp]
  exact (norm_sub_le _ _).trans (add_le_add hdirect hdual)

end RHTower
