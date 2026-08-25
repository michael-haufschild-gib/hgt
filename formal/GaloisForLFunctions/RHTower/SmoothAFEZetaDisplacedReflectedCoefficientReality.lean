import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirichletMeanValueBridge
import GaloisForLFunctions.RHTower.Sieve.CDPolyConjugateReflection
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifier

noncomputable section

namespace RHTower

open Complex
open GaloisForLFunctions.HTGeometry

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

theorem norm_levinsonLinearMollifier_neg (M : ℕ) (tau : ℝ) :
    ‖Sieve.levinsonLinearMollifier M (-tau)‖ =
      ‖Sieve.levinsonLinearMollifier M tau‖ := by
  rw [Sieve.levinsonLinearMollifier]
  exact Sieve.norm_cdpoly_neg_eq_of_star_coeff _ _ _ _ (by
    intro n hn
    exact Sieve.star_levinsonLinearMollifierCoeff M n)

end RHTower
