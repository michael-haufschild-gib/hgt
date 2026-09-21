import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField

/-! Schwarz covariance of the exact original-time Hawking source coefficient. -/

open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section

private theorem positiveCpow_conj {u : ℝ} (hu : 0 < u) (s : ℂ) :
    (starRingEnd ℂ) (power s u) = power ((starRingEnd ℂ) s) u := by
  have harg_eq : (u : ℂ).arg = 0 := by
    simp [Complex.arg, hu.le]
  have harg : (u : ℂ).arg ≠ Real.pi := by
    rw [harg_eq]
    positivity
  change (starRingEnd ℂ) ((u : ℂ) ^ s) = (u : ℂ) ^ ((starRingEnd ℂ) s)
  simpa only [Complex.conj_ofReal] using (Complex.cpow_conj (u : ℂ) s harg).symm

private theorem sourceAmplitude_conj (s w a T : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (sourceAmplitude s w a T t) =
      sourceAmplitude ((starRingEnd ℂ) s) ((starRingEnd ℂ) w)
        ((starRingEnd ℂ) a) ((starRingEnd ℂ) T) t := by
  have hpower : (starRingEnd ℂ) (power (2 * s) (1 + radialUnit t)) =
      power ((starRingEnd ℂ) (2 * s)) (1 + radialUnit t) := by
    simpa [power, map_mul, map_ofNat] using
      positiveCpow_conj (radialUnit_add_one_pos t) (2 * s)
  unfold sourceAmplitude
  rw [map_mul, map_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    hpower, map_mul, map_ofNat, map_pow]

private theorem timeOnset_conj (v : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (timeOnset v u) = timeOnset ((starRingEnd ℂ) v) u := by
  unfold timeOnset
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

private theorem timeOnsetFirst_conj (v : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (timeOnsetFirst v u) = timeOnsetFirst ((starRingEnd ℂ) v) u := by
  unfold timeOnsetFirst
  rw [map_mul, map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

private theorem amplitudeRate_conj (s w u : ℂ) :
    (starRingEnd ℂ) (amplitudeRate s w u) =
      amplitudeRate ((starRingEnd ℂ) s) ((starRingEnd ℂ) w) ((starRingEnd ℂ) u) := by
  unfold amplitudeRate
  rw [map_add, map_mul, map_mul, map_ofNat, map_sub, map_one]

private theorem liftFirstPolynomial_conj (s w u : ℂ) :
    (starRingEnd ℂ) (liftFirstPolynomial s w u) =
      liftFirstPolynomial ((starRingEnd ℂ) s) ((starRingEnd ℂ) w) ((starRingEnd ℂ) u) := by
  unfold liftFirstPolynomial
  rw [map_add, map_mul, map_pow, map_mul, map_mul, map_ofNat, map_pow,
    map_sub, map_pow, map_one, amplitudeRate_conj]

private theorem liftSecondPolynomial_conj (s w u : ℂ) :
    (starRingEnd ℂ) (liftSecondPolynomial s w u) =
      liftSecondPolynomial ((starRingEnd ℂ) s) ((starRingEnd ℂ) w) ((starRingEnd ℂ) u) := by
  unfold liftSecondPolynomial
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    amplitudeRate_conj]

private theorem radialLiftFirst_conj (s w a T : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (radialLiftFirst s w a T t) =
      radialLiftFirst ((starRingEnd ℂ) s) ((starRingEnd ℂ) w)
        ((starRingEnd ℂ) a) ((starRingEnd ℂ) T) t := by
  have hscalar : (starRingEnd ℂ) (-s * (s - 1) / 4) =
      -(starRingEnd ℂ) s * ((starRingEnd ℂ) s - 1) / 4 := by
    rw [map_div₀, map_mul, map_neg, map_sub, map_one, map_ofNat]
  unfold radialLiftFirst
  rw [map_mul, hscalar, map_mul, sourceAmplitude_conj,
    liftFirstPolynomial_conj, Complex.conj_ofReal]

/-- The exact residual polynomial of the gradient-absorbed source is Schwarz covariant. -/
theorem reducedPolynomial_conj (s w u : ℂ) :
    (starRingEnd ℂ) (reducedPolynomial s w u) =
      reducedPolynomial ((starRingEnd ℂ) s) ((starRingEnd ℂ) w) ((starRingEnd ℂ) u) := by
  unfold reducedPolynomial
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one,
    liftSecondPolynomial_conj]

/-- The exact reduced radial coefficient is Schwarz covariant. -/
theorem reducedCoefficient_conj (s w a T : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (reducedCoefficient s w a T t) =
      reducedCoefficient ((starRingEnd ℂ) s) ((starRingEnd ℂ) w)
        ((starRingEnd ℂ) a) ((starRingEnd ℂ) T) t := by
  unfold reducedCoefficient
  rw [map_mul, sourceAmplitude_conj, reducedPolynomial_conj, Complex.conj_ofReal]

/-- The complete original-time residual source, with its onset derivative retained, is Schwarz covariant. -/
theorem timeReducedCoefficient_conj (s a : ℂ) (tau t : ℝ) :
    (starRingEnd ℂ) (timeReducedCoefficient s a tau t) =
      timeReducedCoefficient ((starRingEnd ℂ) s) ((starRingEnd ℂ) a) tau t := by
  unfold timeReducedCoefficient
  simp only [map_add, map_mul, map_zero, map_one, map_ofNat,
    reducedCoefficient_conj, timeOnset_conj, radialLiftFirst_conj, timeOnsetFirst_conj]

end
end RHTower.D4BMJointSource
