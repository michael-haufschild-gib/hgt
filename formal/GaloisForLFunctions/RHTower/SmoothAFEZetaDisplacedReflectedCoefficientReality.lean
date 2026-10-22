import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirichletMeanValueBridge
import GaloisForLFunctions.RHTower.Sieve.CDPolyConjugateReflection
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifier

/-!
# Reality of the reflected displaced AFE coefficients

The reflected finite Dirichlet head of the displaced approximate functional equation has
coefficients `(n + 1)^(-1/2 - d)` and, with the detector factor, `(n + 1)^(-1/2 - d) (1 + λ log(n + 1))`,
for real `d` and `λ`. These coefficients are real, so the corresponding Dirichlet polynomials have
norm even in the height. This lets the positive-frequency `Sieve.dirPoly` be replaced by the
`cdpoly` convention without changing norms; the same holds for the Levinson linear mollifier.

## Main results

- `star_smoothAFEZetaDisplacedReflectedBaseCoeff`: the base coefficient is fixed by complex conjugation.
- `star_smoothAFEZetaDisplacedReflectedDetectorCoeff`: the detector coefficient is fixed by complex
  conjugation.
- `norm_sieveDirPoly_reflectedBase_eq_cdpoly`, `norm_sieveDirPoly_reflectedDetector_eq_cdpoly`:
  `‖∑_{n < L} a_n (n + 1)^(iτ)‖` equals the norm of the `cdpoly` with shifted coefficients on
  `[1, L]` at height `τ`.
- `norm_levinsonLinearMollifier_neg`: `‖M(-τ)‖ = ‖M(τ)‖` for the Levinson linear mollifier.

## Hypotheses

Unconditional.
-/

noncomputable section

namespace RHTower

open Complex
open GaloisForLFunctions.HTGeometry

/-- For real `d`, the reflected base coefficient `(n + 1)^(-1/2 - d)` is real. -/
@[simp] theorem star_smoothAFEZetaDisplacedReflectedBaseCoeff
    (d : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (smoothAFEZetaDisplacedReflectedBaseCoeff d n) =
      smoothAFEZetaDisplacedReflectedBaseCoeff d n := by
  rw [smoothAFEZetaDisplacedReflectedBaseCoeff]
  have hexp : displacedLinePt d 0 - 1 = (((-1 / 2 - d : ℝ) : ℂ)) := by
    unfold displacedLinePt
    push_cast
    ring
  have hbase : (n : ℂ) + 1 = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by norm_num
  rw [hexp, hbase]
  have hpow := Complex.ofReal_cpow
    (x := ((n + 1 : ℕ) : ℝ)) (by positivity) (-1 / 2 - d)
  rw [← hpow]
  simp

/-- For real `λ, d`, the reflected detector coefficient `(n + 1)^(-1/2 - d) (1 + λ log(n + 1))` is real. -/
@[simp] theorem star_smoothAFEZetaDisplacedReflectedDetectorCoeff
    (lam d : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) =
      smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n := by
  rw [smoothAFEZetaDisplacedReflectedDetectorCoeff, map_mul,
    star_smoothAFEZetaDisplacedReflectedBaseCoeff]
  have hbase : (n : ℂ) + 1 = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by norm_num
  rw [hbase]
  have hlog := Complex.ofReal_log
    (x := ((n + 1 : ℕ) : ℝ)) (by positivity)
  rw [← hlog]
  simp

/-- With the real reflected base coefficients, the positive-frequency Dirichlet polynomial
`Sieve.dirPoly` at height `τ` has the same norm as the `cdpoly` on `[1, L]` at height `τ`. -/
theorem norm_sieveDirPoly_reflectedBase_eq_cdpoly
    (d tau : ℝ) (L : ℕ) :
    ‖Sieve.dirPoly L
        (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau‖ =
      ‖cdpoly
        (natPredCoeff (smoothAFEZetaDisplacedReflectedBaseCoeff d))
        (Finset.Icc 1 L) 0 tau‖ := by
  rw [← cdpoly_natPredCoeff_Icc_zero_neg_eq_sieveDirPoly]
  exact Sieve.norm_cdpoly_neg_eq_of_star_coeff _ _ _ _ (by
    intro n hn
    simp [natPredCoeff])

/-- With the real reflected detector coefficients, the positive-frequency Dirichlet polynomial
`Sieve.dirPoly` at height `τ` has the same norm as the `cdpoly` on `[1, L]` at height `τ`. -/
theorem norm_sieveDirPoly_reflectedDetector_eq_cdpoly
    (lam d tau : ℝ) (L : ℕ) :
    ‖Sieve.dirPoly L
        (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau‖ =
      ‖cdpoly
        (natPredCoeff (smoothAFEZetaDisplacedReflectedDetectorCoeff lam d))
        (Finset.Icc 1 L) 0 tau‖ := by
  rw [← cdpoly_natPredCoeff_Icc_zero_neg_eq_sieveDirPoly]
  exact Sieve.norm_cdpoly_neg_eq_of_star_coeff _ _ _ _ (by
    intro n hn
    simp [natPredCoeff])

/-- The Levinson linear mollifier has real coefficients, so its norm is even in the height:
`‖M(-τ)‖ = ‖M(τ)‖`. -/
theorem norm_levinsonLinearMollifier_neg (M : ℕ) (tau : ℝ) :
    ‖Sieve.levinsonLinearMollifier M (-tau)‖ =
      ‖Sieve.levinsonLinearMollifier M tau‖ := by
  rw [Sieve.levinsonLinearMollifier]
  exact Sieve.norm_cdpoly_neg_eq_of_star_coeff _ _ _ _ (by
    intro n hn
    exact Sieve.star_levinsonLinearMollifierCoeff M n)

end RHTower
