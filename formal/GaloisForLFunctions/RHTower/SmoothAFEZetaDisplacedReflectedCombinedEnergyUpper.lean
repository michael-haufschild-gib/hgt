import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedCombinedFreezingMeanSquare

/-!
# Positive upper form for frozen combined reflected energy

Converts the exact complex twisted mean-value estimate for the frozen combined reflected head
into a real nonnegative energy bound while retaining its exact gcd-reduced diagonal.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Error envelope in the frozen combined reflected mean value. -/
def smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError
    (lam : ℝ) (q : ℂ) (L M : ℕ) : ℝ :=
  (4 * (L : ℝ) *
      (|lam| * ‖q‖ + (1 + |lam| * Real.log L)) ^ (2 : ℕ) *
      ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
    (2 * Real.sqrt M) * (2 * Real.sqrt M)

/-- Exact gcd-reduced diagonal for the frozen combined reflected head. -/
def smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal
    (lam d : ℝ) (q : ℂ) (L M : ℕ) : ℂ :=
  Sieve.mollifiedTwistedDiagonalIcc
    (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
    (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
    (Sieve.levinsonLinearMollifierCoeff M)
    (Sieve.levinsonLinearMollifierCoeff M) L M 0

/-- Positive upper form of the exact frozen combined reflected mean value. -/
theorem integral_smoothAFEZetaDisplacedReflectedCombined_mollified_normSq_le
    {lam d : ℝ} (hd : 0 ≤ d) (q : ℂ) (L M : ℕ) (hM : 1 < M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
      (‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖) ^ (2 : ℕ)) ≤
      ‖((b - a : ℝ) : ℂ) *
        smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ +
      smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam q L M := by
  let f : ℝ → ℝ := fun t =>
    (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ (2 : ℕ)
  have hmean :=
    integral_smoothAFEZetaDisplacedReflectedCombined_mollified_normSq_Icc_error
      (lam := lam) hd q L M hM a (b - a)
  rw [show a + (b - a) = b by ring] at hmean
  change ‖(∫ t in a..b, (((f t : ℝ) : ℂ))) -
      ((b - a : ℝ) : ℂ) *
        smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ ≤
    smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam q L M at hmean
  have hnorm : ‖∫ t in a..b, (((f t : ℝ) : ℂ))‖ =
      ∫ t in a..b, f t :=
    norm_intervalIntegral_ofReal_eq hab (fun t ht => sq_nonneg _)
  change (∫ t in a..b, f t) ≤ _
  rw [← hnorm]
  calc
    ‖∫ t in a..b, (((f t : ℝ) : ℂ))‖ =
        ‖((∫ t in a..b, (((f t : ℝ) : ℂ))) -
            ((b - a : ℝ) : ℂ) *
              smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M) +
          ((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ := by
              congr 1
              ring
    _ ≤ ‖(∫ t in a..b, (((f t : ℝ) : ℂ))) -
            ((b - a : ℝ) : ℂ) *
              smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ +
          ‖((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ :=
      norm_add_le _ _
    _ ≤ smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam q L M +
          ‖((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ := by
      gcongr
    _ = _ := by ring

end RHTower
