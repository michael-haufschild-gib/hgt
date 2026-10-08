import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticParityMellin
import GaloisForLFunctions.RHTower.WeilDilationRigidity

/-!
# The literal polynomial Mellin identity

The reflected scale contains the alternating Dirichlet series. Both
convergence and the identity are proved for the actual full-positive source.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- The three-scale source profile has its actual, absolutely convergent transform. -/
theorem sourceTwoPointGaussianProfile_mellin {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (sourceTwoPointGaussianProfile lam c) (s / 2) ∧
      mellin (sourceTwoPointGaussianProfile lam c) (s / 2) =
        Gammaℝ s * ((1 + (c : ℂ) ^ 2 / 2 - c * (4 : ℂ) ^ (-(s / 2))) *
          sourceZetaSquare hW s - ((c : ℂ) / 2) *
          ((1 / 4 : ℝ) : ℂ) ^ (-(s / 2)) * sourceAlternatingZetaSquare lam s) := by
  let A : ℂ := 1 + (c : ℂ) ^ 2 / 2
  have hH := mellinConvergent_sourceGaussianProfile hW hs
  have hAlt := mellinConvergent_sourceAlternatingGaussianProfile hW hs
  have h1 : MellinConvergent (fun t => A • sourceGaussianProfile lam t) (s / 2) :=
    hH.const_smul A
  have h2 : MellinConvergent (fun t => ((c : ℂ) / 2) •
      sourceAlternatingGaussianProfile lam ((1 / 4 : ℝ) * t)) (s / 2) :=
    ((MellinConvergent.comp_mul_left (by norm_num : (0 : ℝ) < 1 / 4)).2 hAlt).const_smul _
  have h3 : MellinConvergent (fun t => (c : ℂ) •
      sourceGaussianProfile lam (4 * t)) (s / 2) :=
    ((MellinConvergent.comp_mul_left (by norm_num : (0 : ℝ) < 4)).2 hH).const_smul _
  have h12 : MellinConvergent (fun t => A • sourceGaussianProfile lam t -
      ((c : ℂ) / 2) • sourceAlternatingGaussianProfile lam ((1 / 4 : ℝ) * t)) (s / 2) := by
    unfold MellinConvergent at h1 h2 ⊢
    simp_rw [smul_sub]
    exact h1.sub h2
  have hfun : sourceTwoPointGaussianProfile lam c = fun t =>
      (A • sourceGaussianProfile lam t -
        ((c : ℂ) / 2) • sourceAlternatingGaussianProfile lam ((1 / 4 : ℝ) * t)) -
        (c : ℂ) • sourceGaussianProfile lam (4 * t) := by
    funext t
    rw [sourceTwoPointGaussianProfile, show t / 4 = (1 / 4 : ℝ) * t by ring]
    rfl
  rw [hfun]
  constructor
  · unfold MellinConvergent at h12 h3 ⊢
    simp_rw [smul_sub]
    simpa only [smul_sub, Pi.sub_def] using h12.sub h3
  · rw [mellin_sub_of_convergent h12 h3, mellin_sub_of_convergent h1 h2,
      mellin_const_smul, mellin_const_smul, mellin_const_smul,
      mellin_comp_mul_left (sourceAlternatingGaussianProfile lam) (s / 2)
        (by norm_num : (0 : ℝ) < 1 / 4),
      mellin_comp_mul_left (sourceGaussianProfile lam) (s / 2)
        (by norm_num : (0 : ℝ) < 4),
      mellin_sourceGaussianProfile hW hs, mellin_sourceAlternatingGaussianProfile hW hs]
    simp only [smul_eq_mul, Complex.ofReal_ofNat, A]
    ring

/-- On the real axis the actual transform is a real quadratic family. -/
theorem re_mellin_sourceTwoPointGaussianProfile_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (mellin (sourceTwoPointGaussianProfile lam c) ((σ : ℂ) / 2)).re =
      (1 + c ^ 2 / 2 - c * (4 : ℝ) ^ (-(σ / 2))) *
        (mellin (sourceGaussianProfile lam) ((σ : ℂ) / 2)).re -
      (c / 2) * (1 / 4 : ℝ) ^ (-(σ / 2)) *
        (Gammaℝ (σ : ℂ) * sourceAlternatingZetaSquare lam (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := hσ
  rw [(sourceTwoPointGaussianProfile_mellin hW c hs).2,
    mellin_sourceGaussianProfile hW hs]
  have he : -((σ : ℂ) / 2) = ((-(σ / 2) : ℝ) : ℂ) := by push_cast; rfl
  have hd : (4 : ℂ) ^ (-((σ : ℂ) / 2)) =
      (((4 : ℝ) ^ (-(σ / 2)) : ℝ) : ℂ) := by
    rw [he]
    exact (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4) _).symm
  have hh : ((1 / 4 : ℝ) : ℂ) ^ (-((σ : ℂ) / 2)) =
      (((1 / 4 : ℝ) ^ (-(σ / 2)) : ℝ) : ℂ) := by
    rw [he]
    exact (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 1 / 4) _).symm
  rw [hd, hh]
  have hc : Gammaℝ (σ : ℂ) *
      ((1 + (c : ℂ) ^ 2 / 2 - c * (((4 : ℝ) ^ (-(σ / 2)) : ℝ) : ℂ)) *
          sourceZetaSquare hW (σ : ℂ) - ((c : ℂ) / 2) *
          (((1 / 4 : ℝ) ^ (-(σ / 2)) : ℝ) : ℂ) * sourceAlternatingZetaSquare lam (σ : ℂ)) =
      ((1 + c ^ 2 / 2 - c * (4 : ℝ) ^ (-(σ / 2)) : ℝ) : ℂ) *
          (Gammaℝ (σ : ℂ) * sourceZetaSquare hW (σ : ℂ)) -
        (((c / 2) * (1 / 4 : ℝ) ^ (-(σ / 2)) : ℝ) : ℂ) *
          (Gammaℝ (σ : ℂ) * sourceAlternatingZetaSquare lam (σ : ℂ)) := by
    push_cast
    ring
  rw [hc]
  simp only [Complex.sub_re, Complex.re_ofReal_mul]

end RHTower.WeilSingularArithmetic
