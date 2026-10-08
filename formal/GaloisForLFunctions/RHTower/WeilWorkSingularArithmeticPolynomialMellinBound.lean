import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialMellin
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialTail
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellinBound

/-!
# Uniform upper bound for the actual weighted Mellin integral

Absolute convergence, the signed small-parameter estimate, and the
absolute tail bound are all supplied by the full-positive arithmetic source.
-/

open Complex

noncomputable section

namespace RHTower.WeilSingularArithmetic

theorem exists_re_mellin_sourceTwoPointGaussianProfile_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → σ < 3 / 2 →
      (mellin (sourceTwoPointGaussianProfile lam c) ((σ : ℂ) / 2)).re ≤ B :=
  exists_re_mellin_le_of_profile_bounds (sourceTwoPointGaussianProfile lam c)
    (fun _ hσ _ => (sourceTwoPointGaussianProfile_mellin hW c (by simpa using hσ)).1)
    (exists_re_sourceTwoPointGaussianProfile_le hW c)
    (exists_norm_sourceTwoPointGaussianProfile_le hW c)

end RHTower.WeilSingularArithmetic
