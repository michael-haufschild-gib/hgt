import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedMollifiedMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiDisplacedLogDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedLinearMollifier

/-!
# Combined reflected displaced detector mean square

The two reflected heads of the differentiated smooth AFE are merged exactly through the frozen
logarithmic chi slope.  Arbitrary complex frozen slopes are transferred to the positive-height
twisted mean-value convention by conjugating coefficients.  Resulting main term remains exact
gcd-reduced diagonal; no coefficientwise or diagonal simplification is used.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

/-- Reflected detector coefficient after freezing the logarithmic chi slope. -/
def smoothAFEZetaDisplacedReflectedCombinedCoeff
    (lam d : ℝ) (q : ℂ) (n : ℕ) : ℂ :=
  (lam : ℂ) * q * smoothAFEZetaDisplacedReflectedBaseCoeff d n +
    smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n

/-- Positive-natural conjugate coefficient used by the positive-frequency mean value. -/
def smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff
    (lam d : ℝ) (q : ℂ) (n : ℕ) : ℂ :=
  (starRingEnd ℂ)
    (natPredCoeff (smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q) n)

/-- Dirichlet-polynomial linearity for the frozen reflected detector. -/
theorem sieveDirPoly_smoothAFEZetaDisplacedReflectedCombinedCoeff
    (lam d : ℝ) (q : ℂ) (L : ℕ) (tau : ℝ) :
    Sieve.dirPoly L
        (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) tau =
      (lam : ℂ) * q *
          Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau +
        Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau := by
  rw [Sieve.dirPoly, Sieve.dirPoly, Sieve.dirPoly]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [smoothAFEZetaDisplacedReflectedCombinedCoeff]
  ring

/-- The two reflected detector heads regroup exactly through `chi'/chi`; no estimate or phase
discarding occurs. -/
theorem smoothAFEZetaDisplacedReflectedDetectorPair_eq_combined
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam tau : ℝ) (L M : ℕ) :
    (lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau *
            Sieve.levinsonLinearMollifier M tau) +
        zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau *
            Sieve.levinsonLinearMollifier M tau) =
      zetaChi (displacedLinePt d tau) *
        (Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
              (logDeriv zetaChi (displacedLinePt d tau)) n) tau *
          Sieve.levinsonLinearMollifier M tau) := by
  obtain ⟨h0, h1⟩ := displacedLinePt_mem_openStrip hd hdhalf tau
  have hchi := zetaChi_ne_zero_of_mem_openStrip h0 h1
  rw [sieveDirPoly_smoothAFEZetaDisplacedReflectedCombinedCoeff]
  rw [logDeriv]
  simp only [Pi.div_apply]
  field_simp [hchi]

/-- Exact finite mollified detector normal form with the two reflected heads merged into one
coefficient-faithful polynomial. -/
theorem smoothAFEZetaDisplacedFiniteClassicalDetector_mul_levinsonLinearMollifier_eq_combined
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam x tau : ℝ) (L M : ℕ) :
    smoothAFEZetaDisplacedFiniteClassicalDetector lam d x tau L *
        Sieve.levinsonLinearMollifier M tau =
      Sieve.dirPoly (L * M)
          (Sieve.dirConv L M
            (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
            (levinsonLinearMollifierFinCoeff M)) (-tau) +
        zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
                (logDeriv zetaChi (displacedLinePt d tau)) n) tau *
            Sieve.levinsonLinearMollifier M tau) -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x *
          Sieve.levinsonLinearMollifier M tau +
        (lam : ℂ) * I *
          smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau *
            Sieve.levinsonLinearMollifier M tau := by
  rw [smoothAFEZetaDisplacedFiniteClassicalDetector_mul_levinsonLinearMollifier]
  have hpair := smoothAFEZetaDisplacedReflectedDetectorPair_eq_combined
    hd hdhalf lam tau L M
  calc
    _ = Sieve.dirPoly (L * M)
          (Sieve.dirConv L M
            (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
            (levinsonLinearMollifierFinCoeff M)) (-tau) +
        ((lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
            (Sieve.dirPoly L
                (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau *
              Sieve.levinsonLinearMollifier M tau) +
          zetaChi (displacedLinePt d tau) *
            (Sieve.dirPoly L
                (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau *
              Sieve.levinsonLinearMollifier M tau)) -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x *
          Sieve.levinsonLinearMollifier M tau +
        (lam : ℂ) * I *
          smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau *
            Sieve.levinsonLinearMollifier M tau := by ring
    _ = _ := by rw [hpair]

/-- Arbitrary complex coefficients are transferred from positive-frequency `dirPoly` to a
positive-height `cdpoly` by conjugating the positive-natural coefficient family. -/
theorem norm_sieveDirPoly_eq_cdpoly_conjNatPred
    (L : ℕ) (a : ℕ → ℂ) (tau : ℝ) :
    ‖Sieve.dirPoly L (fun n => a n) tau‖ =
      ‖cdpoly (fun n => (starRingEnd ℂ) (natPredCoeff a n))
        (Finset.Icc 1 L) 0 tau‖ := by
  rw [← cdpoly_natPredCoeff_Icc_zero_neg_eq_sieveDirPoly]
  have hstar := Sieve.star_cdpoly
    (fun n => (starRingEnd ℂ) (natPredCoeff a n))
    (Finset.Icc 1 L) 0 tau
  have hcoeff :
      (fun n => (starRingEnd ℂ)
        ((starRingEnd ℂ) (natPredCoeff a n))) = natPredCoeff a := by
    funext n
    simp
  rw [hcoeff] at hstar
  rw [← hstar]
  exact Complex.norm_conj _

/-- Uniform envelope for the frozen reflected coefficient. -/
theorem norm_smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff_le
    {lam d : ℝ} (hd : 0 ≤ d) {q : ℂ} {L n : ℕ}
    (hn : n ∈ Finset.Icc 1 L) :
    ‖smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q n‖ ≤
      |lam| * ‖q‖ + (1 + |lam| * Real.log L) := by
  rw [smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff,
    starRingEnd_apply, norm_star, natPredCoeff,
    smoothAFEZetaDisplacedReflectedCombinedCoeff]
  have hbase := norm_smoothAFEZetaDisplacedReflectedBaseNatCoeff_le_one
    hd (Finset.mem_Icc.mp hn).1
  have hdet := norm_smoothAFEZetaDisplacedReflectedDetectorNatCoeff_le
    (lam := lam) hd hn
  rw [smoothAFEZetaDisplacedReflectedBaseNatCoeff, natPredCoeff] at hbase
  rw [smoothAFEZetaDisplacedReflectedDetectorNatCoeff, natPredCoeff] at hdet
  calc
    ‖(lam : ℂ) * q * smoothAFEZetaDisplacedReflectedBaseCoeff d (n - 1) +
        smoothAFEZetaDisplacedReflectedDetectorCoeff lam d (n - 1)‖ ≤
      ‖(lam : ℂ) * q * smoothAFEZetaDisplacedReflectedBaseCoeff d (n - 1)‖ +
        ‖smoothAFEZetaDisplacedReflectedDetectorCoeff lam d (n - 1)‖ :=
      norm_add_le _ _
    _ ≤ |lam| * ‖q‖ * 1 + (1 + |lam| * Real.log L) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
    _ = |lam| * ‖q‖ + (1 + |lam| * Real.log L) := by ring

/-- Explicit logarithmic envelope after freezing at an actual displaced-line ordinate. -/
theorem norm_smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff_logDeriv_le
    {lam d tau : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4) (htau : 4 ≤ tau)
    {L n : ℕ} (hn : n ∈ Finset.Icc 1 L) :
    ‖smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d
        (logDeriv zetaChi (displacedLinePt d tau)) n‖ ≤
      |lam| *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant + |Real.log Real.pi|)) +
        (1 + |lam| * Real.log L) := by
  refine (norm_smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff_le
    hd.le hn).trans ?_
  have hq := norm_logDeriv_zetaChi_displacedLinePt_le_log hd hdquarter htau
  gcongr

/-- Exact gcd-reduced mean square for a frozen logarithmic chi slope. -/
theorem integral_smoothAFEZetaDisplacedReflectedCombined_mollified_cdpoly_Icc_error
    {lam d : ℝ} (hd : 0 ≤ d) (q : ℂ) (L M : ℕ) (hM : 1 < M)
    (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          (cdpoly
              (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
              (Finset.Icc 1 L) 0 t *
            (starRingEnd ℂ) (cdpoly
              (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
              (Finset.Icc 1 L) 0 t)) *
            (Sieve.levinsonLinearMollifier M t *
              (starRingEnd ℂ) (Sieve.levinsonLinearMollifier M t))) -
        (U : ℂ) * Sieve.mollifiedTwistedDiagonalIcc
          (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
          (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
          (Sieve.levinsonLinearMollifierCoeff M)
          (Sieve.levinsonLinearMollifierCoeff M) L M 0‖ ≤
      (4 * (L : ℝ) *
          (|lam| * ‖q‖ + (1 + |lam| * Real.log L)) ^ 2 *
          ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
        (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  let B : ℝ := |lam| * ‖q‖ + (1 + |lam| * Real.log L)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  apply Sieve.integral_levinsonLinearMollified_cdpoly_Icc_error
    (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
    (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
    L M 0 hM (sq_nonneg B)
  intro m hm n hn
  rw [twistedCoeff]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one,
    norm_mul, starRingEnd_apply, norm_star]
  calc
    ‖smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q m‖ *
        ‖smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q n‖ ≤
      B * B :=
        mul_le_mul
          (norm_smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff_le hd hm)
          (norm_smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff_le hd hn)
          (norm_nonneg _) hB0
    _ = B ^ 2 := by ring

/-- Literal frozen reflected-head mollified energy with exact gcd-reduced diagonal. -/
theorem integral_smoothAFEZetaDisplacedReflectedCombined_mollified_normSq_Icc_error
    {lam d : ℝ} (hd : 0 ≤ d) (q : ℂ) (L M : ℕ) (hM : 1 < M)
    (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          ((((‖Sieve.dirPoly L
                  (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
                ‖Sieve.levinsonLinearMollifier M t‖) ^ 2 : ℝ) : ℂ))) -
        (U : ℂ) * Sieve.mollifiedTwistedDiagonalIcc
          (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
          (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
          (Sieve.levinsonLinearMollifierCoeff M)
          (Sieve.levinsonLinearMollifierCoeff M) L M 0‖ ≤
      (4 * (L : ℝ) *
          (|lam| * ‖q‖ + (1 + |lam| * Real.log L)) ^ 2 *
          ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
        (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  have h :=
    integral_smoothAFEZetaDisplacedReflectedCombined_mollified_cdpoly_Icc_error
      (lam := lam) hd q L M hM T U
  have hcorr :
      (∫ t in T..(T + U),
          (cdpoly
              (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
              (Finset.Icc 1 L) 0 t *
            (starRingEnd ℂ) (cdpoly
              (smoothAFEZetaDisplacedReflectedCombinedConjNatCoeff lam d q)
              (Finset.Icc 1 L) 0 t)) *
            (Sieve.levinsonLinearMollifier M t *
              (starRingEnd ℂ) (Sieve.levinsonLinearMollifier M t))) =
        ∫ t in T..(T + U),
          ((((‖Sieve.dirPoly L
                  (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
                ‖Sieve.levinsonLinearMollifier M t‖) ^ 2 : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [correlation_eq_ofReal_norm_mul_sq,
      norm_sieveDirPoly_eq_cdpoly_conjNatPred]
    rfl
  rw [hcorr] at h
  exact h

end RHTower
