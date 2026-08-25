import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDetectorEnergyDecomposition
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectMollifiedMeanSquare

/-!
# Positive direct-head energy bound

The exact arbitrary-window Dirichlet mean-value estimate is converted to the positive upper form
consumed by Cauchy--Schwarz cross-term estimates.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Positive upper form of the exact direct mollified detector mean value. -/
theorem integral_normSq_smoothAFEZetaDisplacedMollifiedDirectHead_le
    (lam d x : ℝ) (L M : ℕ) (a b : ℝ) :
    (∫ t in a..b,
      ‖smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t‖ ^ 2) ≤
      ((b - a) + 8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M))) *
        ∑ r : Fin (L * M),
          ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖ ^ 2 := by
  let A : ℝ := ∑ r : Fin (L * M),
    ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖ ^ 2
  have hmean := smoothAFEZetaDisplacedDirectMollified_meanValue_window
    lam d x L M a b
  have heq :
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t‖ ^ 2) =
      ∫ t in a..b,
        ‖Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-t) *
            Sieve.levinsonLinearMollifier M t‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    unfold smoothAFEZetaDisplacedMollifiedDirectHead
    change ‖Sieve.dirPoly (L * M)
      (smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M) (-t)‖ ^ 2 = _
    rw [← smoothAFEZetaDisplacedDirectHead_mul_levinsonLinearMollifier]
  rw [heq]
  change |(∫ t in a..b,
      ‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-t) *
          Sieve.levinsonLinearMollifier M t‖ ^ 2) - (b - a) * A| ≤
    8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M)) * A at hmean
  have hsub :
      (∫ t in a..b,
        ‖Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-t) *
            Sieve.levinsonLinearMollifier M t‖ ^ 2) - (b - a) * A ≤
        8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M)) * A :=
    (le_abs_self _).trans hmean
  change (∫ t in a..b,
      ‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-t) *
          Sieve.levinsonLinearMollifier M t‖ ^ 2) ≤
    ((b - a) + 8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M))) * A
  linarith

end

end RHTower
