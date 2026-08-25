import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedCoefficientReality
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedMeanValue

/-!
# Reflected displaced AFE heads: mollified mean squares

The base and differentiated reflected AFE heads are placed into the corpus's exact twisted
Dirichlet-polynomial mean value.  Coefficient envelopes are proved from their literal displaced
coefficients, and the resulting complex correlations are identified with squared norms.  The main
term remains the exact gcd-reduced diagonal; no coarse diagonal replacement is made.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

/-- Positive-natural base coefficient of the reflected AFE head. -/
def smoothAFEZetaDisplacedReflectedBaseNatCoeff (d : ℝ) : ℕ → ℂ :=
  natPredCoeff (smoothAFEZetaDisplacedReflectedBaseCoeff d)

/-- Positive-natural detector coefficient of the reflected AFE head. -/
def smoothAFEZetaDisplacedReflectedDetectorNatCoeff (lam d : ℝ) : ℕ → ℂ :=
  natPredCoeff (smoothAFEZetaDisplacedReflectedDetectorCoeff lam d)

theorem norm_smoothAFEZetaDisplacedReflectedBaseNatCoeff_le_one
    {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    ‖smoothAFEZetaDisplacedReflectedBaseNatCoeff d n‖ ≤ 1 := by
  rw [smoothAFEZetaDisplacedReflectedBaseNatCoeff, natPredCoeff,
    smoothAFEZetaDisplacedReflectedBaseCoeff]
  have hindex : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    norm_cast
    omega
  rw [hindex]
  have hexp : displacedLinePt d 0 - 1 = (((-1 / 2 - d : ℝ) : ℂ)) := by
    unfold displacedLinePt
    push_cast
    ring
  rw [hexp]
  have hpow := Complex.ofReal_cpow (x := (n : ℝ))
    (by exact_mod_cast (show 0 ≤ n by omega)) (-1 / 2 - d)
  have hncast : (n : ℂ) = (((n : ℝ) : ℂ)) := by norm_num
  rw [hncast, ← hpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

theorem norm_smoothAFEZetaDisplacedReflectedDetectorNatCoeff_le
    {lam d : ℝ} (hd : 0 ≤ d) {L n : ℕ}
    (hn : n ∈ Finset.Icc 1 L) :
    ‖smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d n‖ ≤
      1 + |lam| * Real.log L := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnL : n ≤ L := (Finset.mem_Icc.mp hn).2
  rw [smoothAFEZetaDisplacedReflectedDetectorNatCoeff, natPredCoeff,
    smoothAFEZetaDisplacedReflectedDetectorCoeff,
    smoothAFEZetaDisplacedReflectedBaseCoeff]
  have hindex : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    norm_cast
    omega
  rw [hindex]
  have hbase := norm_smoothAFEZetaDisplacedReflectedBaseNatCoeff_le_one
    hd hn1
  rw [smoothAFEZetaDisplacedReflectedBaseNatCoeff, natPredCoeff,
    smoothAFEZetaDisplacedReflectedBaseCoeff] at hbase
  rw [hindex] at hbase
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogle : Real.log (n : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnL)
  calc
    ‖(n : ℂ) ^ (displacedLinePt d 0 - 1) *
        (1 + (lam : ℂ) * Complex.log (n : ℂ))‖ ≤
      ‖(n : ℂ) ^ (displacedLinePt d 0 - 1)‖ *
        (1 + |lam| * Real.log n) := by
          have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
            rw [show (n : ℂ) = (((n : ℝ) : ℂ)) by norm_num]
            exact (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ n)).symm
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          calc
            ‖1 + (lam : ℂ) * Complex.log (n : ℂ)‖ ≤
                ‖(1 : ℂ)‖ + ‖(lam : ℂ) * Complex.log (n : ℂ)‖ :=
              norm_add_le _ _
            _ = 1 + |lam| * Real.log n := by
              rw [hlog, norm_mul]
              simp only [norm_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hlog0]
    _ ≤ 1 * (1 + |lam| * Real.log n) := by
      gcongr
    _ ≤ 1 + |lam| * Real.log L := by
      simp only [one_mul]
      gcongr

/-- A two-factor complex correlation is the real cast of its product norm square. -/
theorem correlation_eq_ofReal_norm_mul_sq (z w : ℂ) :
    (z * (starRingEnd ℂ) z) * (w * (starRingEnd ℂ) w) =
      ((((‖z‖ * ‖w‖) ^ 2 : ℝ) : ℂ)) := by
  have mul_starRingEnd_eq_norm_sq (v : ℂ) :
      v * (starRingEnd ℂ) v = (((‖v‖ ^ 2 : ℝ) : ℂ)) := by
    rw [starRingEnd_apply]
    apply Complex.ext
    · simp [Complex.sq_norm, Complex.normSq_apply]
    · simp [Complex.sq_norm, Complex.normSq_apply]
      ring
  rw [mul_starRingEnd_eq_norm_sq, mul_starRingEnd_eq_norm_sq]
  push_cast
  ring

/-- Exact gcd-reduced mollified mean value for the reflected base AFE head. -/
theorem integral_smoothAFEZetaDisplacedReflectedBase_mollified_cdpoly_Icc_error
    {d : ℝ} (hd : 0 ≤ d) (L M : ℕ) (hM : 1 < M) (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          (cdpoly (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
              (Finset.Icc 1 L) 0 t *
            (starRingEnd ℂ) (cdpoly
              (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
              (Finset.Icc 1 L) 0 t)) *
            (Sieve.levinsonLinearMollifier M t *
              (starRingEnd ℂ) (Sieve.levinsonLinearMollifier M t))) -
        (U : ℂ) * Sieve.mollifiedTwistedDiagonalIcc
          (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
          (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
          (Sieve.levinsonLinearMollifierCoeff M)
          (Sieve.levinsonLinearMollifierCoeff M) L M 0‖
      ≤ (4 * (L : ℝ) * 1 * ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
          (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  apply Sieve.integral_levinsonLinearMollified_cdpoly_Icc_error
    (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
    (smoothAFEZetaDisplacedReflectedBaseNatCoeff d) L M 0 hM (by positivity)
  intro m hm n hn
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [twistedCoeff]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one,
    norm_mul, starRingEnd_apply, norm_star]
  calc
    ‖smoothAFEZetaDisplacedReflectedBaseNatCoeff d m‖ *
          ‖smoothAFEZetaDisplacedReflectedBaseNatCoeff d n‖ ≤ 1 * 1 :=
      mul_le_mul
        (norm_smoothAFEZetaDisplacedReflectedBaseNatCoeff_le_one hd hm1)
        (norm_smoothAFEZetaDisplacedReflectedBaseNatCoeff_le_one hd hn1)
        (norm_nonneg _) (by positivity)
    _ = 1 := by norm_num

/-- Exact gcd-reduced mollified mean value for the reflected detector AFE head. -/
theorem integral_smoothAFEZetaDisplacedReflectedDetector_mollified_cdpoly_Icc_error
    {lam d : ℝ} (hd : 0 ≤ d) (L M : ℕ) (hM : 1 < M)
    (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          (cdpoly (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
              (Finset.Icc 1 L) 0 t *
            (starRingEnd ℂ) (cdpoly
              (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
              (Finset.Icc 1 L) 0 t)) *
            (Sieve.levinsonLinearMollifier M t *
              (starRingEnd ℂ) (Sieve.levinsonLinearMollifier M t))) -
        (U : ℂ) * Sieve.mollifiedTwistedDiagonalIcc
          (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
          (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
          (Sieve.levinsonLinearMollifierCoeff M)
          (Sieve.levinsonLinearMollifierCoeff M) L M 0‖
      ≤ (4 * (L : ℝ) * (1 + |lam| * Real.log L) ^ 2 *
          ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
          (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  have hB0 : 0 ≤ 1 + |lam| * Real.log L := by positivity
  apply Sieve.integral_levinsonLinearMollified_cdpoly_Icc_error
    (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
    (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d) L M 0 hM
    (sq_nonneg _) 
  intro m hm n hn
  rw [twistedCoeff]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one,
    norm_mul, starRingEnd_apply, norm_star]
  calc
    ‖smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d m‖ *
          ‖smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d n‖ ≤
        (1 + |lam| * Real.log L) * (1 + |lam| * Real.log L) :=
      mul_le_mul
        (norm_smoothAFEZetaDisplacedReflectedDetectorNatCoeff_le hd hm)
        (norm_smoothAFEZetaDisplacedReflectedDetectorNatCoeff_le hd hn)
        (norm_nonneg _) hB0
    _ = (1 + |lam| * Real.log L) ^ 2 := by ring

/-- Literal reflected-base AFE-head energy with the exact gcd-reduced diagonal. -/
theorem integral_smoothAFEZetaDisplacedReflectedBase_mollified_normSq_Icc_error
    {d : ℝ} (hd : 0 ≤ d) (L M : ℕ) (hM : 1 < M) (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          ((((‖Sieve.dirPoly L
                  (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
                ‖Sieve.levinsonLinearMollifier M t‖) ^ 2 : ℝ) : ℂ))) -
        (U : ℂ) * Sieve.mollifiedTwistedDiagonalIcc
          (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
          (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
          (Sieve.levinsonLinearMollifierCoeff M)
          (Sieve.levinsonLinearMollifierCoeff M) L M 0‖
      ≤ (4 * (L : ℝ) * 1 * ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
          (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  have h := integral_smoothAFEZetaDisplacedReflectedBase_mollified_cdpoly_Icc_error
    hd L M hM T U
  have hcorr :
      (∫ t in T..(T + U),
          (cdpoly (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
              (Finset.Icc 1 L) 0 t *
            (starRingEnd ℂ) (cdpoly
              (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
              (Finset.Icc 1 L) 0 t)) *
            (Sieve.levinsonLinearMollifier M t *
              (starRingEnd ℂ) (Sieve.levinsonLinearMollifier M t))) =
        ∫ t in T..(T + U),
          ((((‖Sieve.dirPoly L
                  (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
                ‖Sieve.levinsonLinearMollifier M t‖) ^ 2 : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [correlation_eq_ofReal_norm_mul_sq,
      norm_sieveDirPoly_reflectedBase_eq_cdpoly]
    rfl
  rw [hcorr] at h
  exact h

/-- Literal reflected-detector AFE-head energy with the exact gcd-reduced diagonal. -/
theorem integral_smoothAFEZetaDisplacedReflectedDetector_mollified_normSq_Icc_error
    {lam d : ℝ} (hd : 0 ≤ d) (L M : ℕ) (hM : 1 < M) (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          ((((‖Sieve.dirPoly L
                  (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) t‖ *
                ‖Sieve.levinsonLinearMollifier M t‖) ^ 2 : ℝ) : ℂ))) -
        (U : ℂ) * Sieve.mollifiedTwistedDiagonalIcc
          (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
          (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
          (Sieve.levinsonLinearMollifierCoeff M)
          (Sieve.levinsonLinearMollifierCoeff M) L M 0‖
      ≤ (4 * (L : ℝ) * (1 + |lam| * Real.log L) ^ 2 *
          ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
          (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  have h := integral_smoothAFEZetaDisplacedReflectedDetector_mollified_cdpoly_Icc_error
    (lam := lam) hd L M hM T U
  have hcorr :
      (∫ t in T..(T + U),
          (cdpoly (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
              (Finset.Icc 1 L) 0 t *
            (starRingEnd ℂ) (cdpoly
              (smoothAFEZetaDisplacedReflectedDetectorNatCoeff lam d)
              (Finset.Icc 1 L) 0 t)) *
            (Sieve.levinsonLinearMollifier M t *
              (starRingEnd ℂ) (Sieve.levinsonLinearMollifier M t))) =
        ∫ t in T..(T + U),
          ((((‖Sieve.dirPoly L
                  (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) t‖ *
                ‖Sieve.levinsonLinearMollifier M t‖) ^ 2 : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [correlation_eq_ofReal_norm_mul_sq,
      norm_sieveDirPoly_reflectedDetector_eq_cdpoly]
    rfl
  rw [hcorr] at h
  exact h

end RHTower
