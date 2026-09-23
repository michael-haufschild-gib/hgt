import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedLinearMollifier
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTNegativeWindow

/-!
# Direct displaced detector mollified mean square

The direct finite AFE head and the linear mollifier have the same negative frequency.  Their
product is one exact Dirichlet convolution polynomial, so the arbitrary-window mean-value theorem
applies directly and leaves only its coefficient energy to evaluate.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

/-- Convolution coefficient of the direct displaced detector head with the
linear Levinson mollifier. -/
def smoothAFEZetaDisplacedDirectMollifiedCoeff
    (lam d x : ℝ) (L M : ℕ) : Fin (L * M) → ℂ :=
  Sieve.dirConv L M
    (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
    (levinsonLinearMollifierFinCoeff M)

/-- Exact direct-head multiplication into one negative-frequency polynomial. -/
theorem smoothAFEZetaDisplacedDirectHead_mul_levinsonLinearMollifier
    (lam d x tau : ℝ) (L M : ℕ) :
    Sieve.dirPoly L
        (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-tau) *
      Sieve.levinsonLinearMollifier M tau =
        Sieve.dirPoly (L * M)
          (smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M) (-tau) := by
  rw [← sieveDirPoly_levinsonLinearMollifierFinCoeff_neg M tau]
  exact Sieve.dirPoly_mul_eq_dirPoly L M
    (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
    (levinsonLinearMollifierFinCoeff M) (-tau)

/-- Exact mean-square theorem for the direct mollified detector head. -/
theorem smoothAFEZetaDisplacedDirectMollified_meanValue_window
    (lam d x : ℝ) (L M : ℕ) (T₁ T₂ : ℝ) :
    |(∫ tau in T₁..T₂,
        ‖Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-tau) *
            Sieve.levinsonLinearMollifier M tau‖ ^ (2 : ℕ)) -
        (T₂ - T₁) *
          ∑ r : Fin (L * M),
            ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖ ^ (2 : ℕ)|
      ≤ 8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M)) *
          ∑ r : Fin (L * M),
            ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖ ^ (2 : ℕ) := by
  have hpoint : ∀ tau : ℝ,
      ‖Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-tau) *
            Sieve.levinsonLinearMollifier M tau‖ ^ (2 : ℕ) =
        ‖Sieve.dirPoly (L * M)
            (smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M) (-tau)‖ ^ (2 : ℕ) := by
    intro tau
    rw [smoothAFEZetaDisplacedDirectHead_mul_levinsonLinearMollifier]
  rw [intervalIntegral.integral_congr (fun tau _ => hpoint tau)]
  simpa only [Nat.cast_mul] using
    Sieve.dirichlet_meanValue_window_neg (L * M)
      (smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M) T₁ T₂

end RHTower
