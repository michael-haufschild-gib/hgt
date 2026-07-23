import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderFiniteTail
import GaloisForLFunctions.HTGeometry.GammaFactorialJetConnectionTensorLaw

/-!
# Gamma factorial finite-tail/covariant-residue universality

The even finite-tail coefficient of the Gamma factorial microscope and the intrinsic covariant
top-residue frame were obtained from different constructions.  Their exact factorial laws identify
them: the analytic tail at order `2r+2` is the negative norm of the grade-`2r+1` covariant residue
at the initial Gamma pole.
-/

namespace GaloisForLFunctions

noncomputable section

open Complex Filter Topology

/-- **Finite-tail/covariant-residue law.**  After removal of the reciprocal principal jet, the
even Gamma factorial tail converges to the negative norm of the adjacent intrinsic jet-grade
residue. -/
theorem tendsto_gammaFactorialScaledPolygamma_even_finiteTail_eq_neg_covariantResidueNorm
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
      ((gammaFactorialScaledPolygamma (2 * r + 2) n x -
          (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
        reciprocalGammaFactorialScale n ^ (2 * r + 3)))) atTop
      (𝓝 (-(‖gammaPoleCovariantTopResidueValue 0 (2 * r + 1)
          (Fin.last (2 * r + 1))‖ : ℂ))) := by
  have h := tendsto_gammaFactorialScaledPolygamma_even_finiteTail r hx
  convert h using 1
  rw [norm_gammaPoleCovariantTopResidueValue_eq_factorial_pow_mul_factorial]
  simp

end

end GaloisForLFunctions
