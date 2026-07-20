import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet
import GaloisForLFunctions.HilbertMetric.SpectralBandwidthFano

/-!
# Slater--Pluecker log-partition connector

For an orthonormal finite feature frame, degree scaling turns the canonical Pluecker-volume
partition into the moment-generating function of the total selected degree.  This module proves
the literal differential connector: its first logarithmic derivative is the Slater spectral
mean, while its second logarithmic derivative is the Slater compression variance.  Consequently
the spectral-bandwidth Fano law is an exact theorem about the canonical Pluecker partition, not
only about an abstract compression formula.
-/

open Filter
open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {n : ℕ} {κ : Type*} [Fintype κ]

/-- Compression of a diagonal spectral observable to a finite coordinate frame. -/
def slaterSpectralCompressionMatrix (evaluation : Fin n → κ → ℝ)
    (energy : κ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, energy k * evaluation i k * evaluation j k

/-- Compression of the square of a diagonal spectral observable. -/
def slaterSpectralSecondMomentMatrix (evaluation : Fin n → κ → ℝ)
    (energy : κ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, energy k ^ 2 * evaluation i k * evaluation j k

/-- Exponentially degree-scaled feature Gram path. -/
def exponentialFeatureGram (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ∑ k, Real.exp (s * (degree k : ℝ)) * evaluation i k * evaluation j k

/-- First entrywise derivative of the exponential feature Gram path. -/
def exponentialFeatureGramFirst (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ∑ k, (degree k : ℝ) * Real.exp (s * (degree k : ℝ)) *
      evaluation i k * evaluation j k

/-- Second entrywise derivative of the exponential feature Gram path. -/
def exponentialFeatureGramSecond (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ∑ k, (degree k : ℝ) ^ 2 * Real.exp (s * (degree k : ℝ)) *
      evaluation i k * evaluation j k

/-- The exponential Gram path is the existing square-root-scaled feature Gram path. -/
theorem exponentialFeatureGram_eq_scaledFeatureGram
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ) (s : ℝ) :
    exponentialFeatureGram evaluation degree s =
      standardFeatureGram
        (scaledFeatureRows evaluation (fun _ => 1) degree (Real.exp (s / 2))) := by
  ext i j
  unfold exponentialFeatureGram standardFeatureGram scaledFeatureRows
  simp only [Matrix.of_apply, Real.sqrt_one, one_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hscale :
      Real.exp (s / 2) ^ degree k * Real.exp (s / 2) ^ degree k =
        Real.exp (s * (degree k : ℝ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [← hscale]
  ring

/-- Cauchy--Binet identifies the determinant of the exponential Gram path with the canonical
Pluecker degree partition at exponential parameter. -/
theorem det_exponentialFeatureGram_eq_canonicalFeatureVolume
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ) (s : ℝ) :
    (exponentialFeatureGram evaluation degree s).det =
      canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s) := by
  rw [exponentialFeatureGram_eq_scaledFeatureGram]
  rw [det_scaledFeatureGram_eq_canonicalFeatureVolume
    evaluation (fun _ => 1) degree (fun _ => by norm_num)]
  apply congrArg (canonicalFeatureVolume evaluation (fun _ => 1) degree)
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Literal first entrywise derivative of the exponential Gram path. -/
theorem hasDerivAt_exponentialFeatureGram
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s => exponentialFeatureGram evaluation degree s i j)
      (exponentialFeatureGramFirst evaluation degree t i j) t := by
  unfold exponentialFeatureGram exponentialFeatureGramFirst
  simp only [Matrix.of_apply]
  apply HasDerivAt.fun_sum
  intro k _
  have hlinear : HasDerivAt (fun s => s * (degree k : ℝ)) (degree k : ℝ) t := by
    simpa using (hasDerivAt_id t).mul_const (degree k : ℝ)
  have hexp : HasDerivAt (fun s => Real.exp (s * (degree k : ℝ)))
      (Real.exp (t * (degree k : ℝ)) * (degree k : ℝ)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (t * (degree k : ℝ))).comp t hlinear
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    hexp.mul_const (evaluation i k * evaluation j k)

/-- Literal second entrywise derivative of the exponential Gram path. -/
theorem hasDerivAt_exponentialFeatureGramFirst
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s => exponentialFeatureGramFirst evaluation degree s i j)
      (exponentialFeatureGramSecond evaluation degree t i j) t := by
  unfold exponentialFeatureGramFirst exponentialFeatureGramSecond
  simp only [Matrix.of_apply]
  apply HasDerivAt.fun_sum
  intro k _
  have hlinear : HasDerivAt (fun s => s * (degree k : ℝ)) (degree k : ℝ) t := by
    simpa using (hasDerivAt_id t).mul_const (degree k : ℝ)
  have hexp : HasDerivAt (fun s => Real.exp (s * (degree k : ℝ)))
      (Real.exp (t * (degree k : ℝ)) * (degree k : ℝ)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (t * (degree k : ℝ))).comp t hlinear
  simpa only [mul_assoc, mul_comm, mul_left_comm, pow_two] using
    (hexp.const_mul (degree k : ℝ)).mul_const
      (evaluation i k * evaluation j k)

/-- An orthonormal frame starts the exponential Gram path at the identity matrix. -/
theorem exponentialFeatureGram_zero
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation) :
    exponentialFeatureGram evaluation degree 0 = 1 := by
  ext i j
  simpa [exponentialFeatureGram] using hframe i j

/-- The first exponential Gram jet at zero is the compressed degree observable. -/
theorem exponentialFeatureGramFirst_zero
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ) :
    exponentialFeatureGramFirst evaluation degree 0 =
      slaterSpectralCompressionMatrix evaluation (fun k => (degree k : ℝ)) := by
  ext i j
  simp [exponentialFeatureGramFirst, slaterSpectralCompressionMatrix]

/-- The second exponential Gram jet at zero is the compressed squared-degree observable. -/
theorem exponentialFeatureGramSecond_zero
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ) :
    exponentialFeatureGramSecond evaluation degree 0 =
      slaterSpectralSecondMomentMatrix evaluation (fun k => (degree k : ℝ)) := by
  ext i j
  simp [exponentialFeatureGramSecond, slaterSpectralSecondMomentMatrix]

/-- The trace of the spectral compression is the additive Slater mean. -/
theorem trace_slaterSpectralCompressionMatrix
    (evaluation : Fin n → κ → ℝ) (energy : κ → ℝ) :
    Matrix.trace (slaterSpectralCompressionMatrix evaluation energy) =
      slaterSpectralMean evaluation energy := by
  unfold Matrix.trace slaterSpectralCompressionMatrix slaterSpectralMean
    orbitalSpectralMean
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The trace of the compressed second moment is the sum of orbital second moments. -/
theorem trace_slaterSpectralSecondMomentMatrix
    (evaluation : Fin n → κ → ℝ) (energy : κ → ℝ) :
    Matrix.trace (slaterSpectralSecondMomentMatrix evaluation energy) =
      ∑ i, orbitalSpectralSecondMoment evaluation energy i := by
  unfold Matrix.trace slaterSpectralSecondMomentMatrix orbitalSpectralSecondMoment
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The trace of the squared spectral compression is its squared Hilbert--Schmidt energy. -/
theorem trace_sq_slaterSpectralCompressionMatrix
    (evaluation : Fin n → κ → ℝ) (energy : κ → ℝ) :
    Matrix.trace
        (slaterSpectralCompressionMatrix evaluation energy *
          slaterSpectralCompressionMatrix evaluation energy) =
      slaterCompressedSpectralEnergy evaluation energy := by
  unfold Matrix.trace slaterSpectralCompressionMatrix slaterCompressedSpectralEnergy
  change
    (∑ i, ∑ j,
      (∑ k, energy k * evaluation i k * evaluation j k) *
        ∑ k, energy k * evaluation j k * evaluation i k) =
      ∑ i, ∑ j, (∑ k, energy k * evaluation i k * evaluation j k) ^ 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsymm :
      (∑ k, energy k * evaluation j k * evaluation i k) =
        ∑ k, energy k * evaluation i k * evaluation j k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsymm]
  ring

/-- At an orthonormal base point, Gram log-curvature is exactly the Slater spectral variance. -/
theorem gramLogCurvatureJet_one_eq_slaterSpectralVariance
    (evaluation : Fin n → κ → ℝ) (energy : κ → ℝ) :
    gramLogCurvatureJet (1 : Matrix (Fin n) (Fin n) ℝ)
        (slaterSpectralCompressionMatrix evaluation energy)
        (slaterSpectralSecondMomentMatrix evaluation energy) =
      slaterSpectralVariance evaluation energy := by
  unfold gramLogCurvatureJet slaterSpectralVariance
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub]
  rw [trace_slaterSpectralSecondMomentMatrix,
    trace_sq_slaterSpectralCompressionMatrix]

/-- **First Slater--Pluecker connector.**  The first log derivative of the canonical Pluecker
degree partition is the additive Slater spectral mean. -/
theorem canonicalFeatureVolume_logDerivative_eq_slaterSpectralMean
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation) :
    deriv (fun s => Real.log
      (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s))) 0 =
      slaterSpectralMean evaluation (fun k => (degree k : ℝ)) := by
  let A := exponentialFeatureGram evaluation degree
  let A₁ := exponentialFeatureGramFirst evaluation degree
  have hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t := by
    intro t i j
    exact hasDerivAt_exponentialFeatureGram evaluation degree t i j
  have hA0 : A 0 = 1 := exponentialFeatureGram_zero evaluation degree hframe
  have hA₁0 : A₁ 0 =
      slaterSpectralCompressionMatrix evaluation (fun k => (degree k : ℝ)) :=
    exponentialFeatureGramFirst_zero evaluation degree
  have hdet0 : (A 0).det ≠ 0 := by rw [hA0]; simp
  have hlog := (hasDerivAt_matrixDet A (A₁ 0) 0 (hA 0)).log hdet0
  have hlogValue :
      deriv (fun s => Real.log (A s).det) 0 =
        Matrix.trace ((A 0)⁻¹ * A₁ 0) := by
    rw [hlog.deriv, detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet0]
    field_simp [hdet0]
  rw [hA0, hA₁0] at hlogValue
  simp only [inv_one, Matrix.one_mul] at hlogValue
  rw [trace_slaterSpectralCompressionMatrix] at hlogValue
  calc
    deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s))) 0 =
        deriv (fun s => Real.log (A s).det) 0 := by
      apply congrArg (fun f : ℝ → ℝ => deriv f 0)
      funext s
      rw [det_exponentialFeatureGram_eq_canonicalFeatureVolume]
    _ = slaterSpectralMean evaluation (fun k => (degree k : ℝ)) := hlogValue

/-- **Second Slater--Pluecker connector.**  The second log derivative of the canonical Pluecker
degree partition is exactly the additive Slater compression variance. -/
theorem canonicalFeatureVolume_logSecondDerivative_eq_slaterSpectralVariance
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation) :
    deriv (deriv (fun s => Real.log
      (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s)))) 0 =
      slaterSpectralVariance evaluation (fun k => (degree k : ℝ)) := by
  let A := exponentialFeatureGram evaluation degree
  let A₁ := exponentialFeatureGramFirst evaluation degree
  let A₂ := exponentialFeatureGramSecond evaluation degree
  have hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t := by
    intro t i j
    exact hasDerivAt_exponentialFeatureGram evaluation degree t i j
  have hA₁ : ∀ t i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t := by
    intro t i j
    exact hasDerivAt_exponentialFeatureGramFirst evaluation degree t i j
  have hA0 : A 0 = 1 := exponentialFeatureGram_zero evaluation degree hframe
  have hA₁0 : A₁ 0 =
      slaterSpectralCompressionMatrix evaluation (fun k => (degree k : ℝ)) :=
    exponentialFeatureGramFirst_zero evaluation degree
  have hA₂0 : A₂ 0 =
      slaterSpectralSecondMomentMatrix evaluation (fun k => (degree k : ℝ)) :=
    exponentialFeatureGramSecond_zero evaluation degree
  have hdet0 : (A 0).det ≠ 0 := by rw [hA0]; simp
  have hdetDeriv := hasDerivAt_matrixDet A (A₁ 0) 0 (hA 0)
  have hdet : ∀ᶠ t in nhds (0 : ℝ), (A t).det ≠ 0 :=
    (hdetDeriv.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hdet0
  have hcurvature :=
    logDet_secondDerivative_eq_gramLogCurvatureJet A A₁ A₂ 0 hA hA₁ hdet
  rw [hA0, hA₁0, hA₂0,
    gramLogCurvatureJet_one_eq_slaterSpectralVariance] at hcurvature
  calc
    deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s)))) 0 =
        deriv (deriv (fun s => Real.log (A s).det)) 0 := by
      apply congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0)
      funext s
      rw [det_exponentialFeatureGram_eq_canonicalFeatureVolume]
    _ = slaterSpectralVariance evaluation (fun k => (degree k : ℝ)) := hcurvature

/-- The log-partition mean-minus-curvature is exactly the Slater Fano margin. -/
theorem canonicalFeatureVolume_logFanoMargin_eq_slaterSpectralFanoMargin
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s)))) 0 =
      slaterSpectralFanoMargin evaluation (fun k => (degree k : ℝ)) := by
  rw [canonicalFeatureVolume_logDerivative_eq_slaterSpectralMean evaluation degree hframe,
    canonicalFeatureVolume_logSecondDerivative_eq_slaterSpectralVariance
      evaluation degree hframe]
  rfl

/-- **Pluecker three-defect law.**  The canonical determinantal degree partition has an exact
spectral-band floor plus endpoint leakage, centering energy, and occupied coherence. -/
theorem canonicalFeatureVolume_logFanoMargin_three_defect
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation) (lower upper : ℝ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s)))) 0 =
      (n : ℝ) * (lower - (upper - lower - 1) ^ 2 / 4) +
        slaterSpectralSecantDefect evaluation (fun k => (degree k : ℝ)) lower upper +
        slaterSpectralCenteringDefect evaluation (fun k => (degree k : ℝ)) lower upper +
        slaterSpectralCoherenceDefect evaluation (fun k => (degree k : ℝ)) := by
  rw [canonicalFeatureVolume_logFanoMargin_eq_slaterSpectralFanoMargin
    evaluation degree hframe]
  simpa using slaterSpectralFanoMargin_three_defect
    evaluation (fun k => (degree k : ℝ)) lower upper

/-- The universal spectral-bandwidth lower bound, stated directly for the canonical Pluecker
log-partition. -/
theorem canonicalFeatureVolume_logFanoMargin_lower_bound
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ (degree k : ℝ))
    (hupper : ∀ k, (degree k : ℝ) ≤ upper) :
    (n : ℝ) * (lower - (upper - lower - 1) ^ 2 / 4) ≤
      deriv (fun s => Real.log
          (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s))) 0 -
        deriv (deriv (fun s => Real.log
          (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s)))) 0 := by
  rw [canonicalFeatureVolume_logFanoMargin_eq_slaterSpectralFanoMargin
    evaluation degree hframe]
  simpa using slaterSpectralFanoMargin_lower_bound evaluation
    (fun k => (degree k : ℝ)) hframe lower upper hlower hupper

/-- Every canonical Pluecker degree law supported in positive degrees at most four is
Fano-underdispersed in the exact second-order log-partition sense. -/
theorem positiveQuarticDegree_canonicalFeatureVolume_logFanoMargin_nonnegative
    [LinearOrder κ] (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation)
    (hpositive : ∀ k, 1 ≤ degree k) (hquartic : ∀ k, degree k ≤ 4) :
    0 ≤ deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume evaluation (fun _ => 1) degree (Real.exp s)))) 0 := by
  rw [canonicalFeatureVolume_logFanoMargin_eq_slaterSpectralFanoMargin
    evaluation degree hframe]
  exact positiveQuarticDegree_slaterSpectralFanoMargin_nonnegative
    evaluation degree hframe hpositive hquartic

end

end GaloisForLFunctions.HilbertMetric
