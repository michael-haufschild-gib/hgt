import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet
import GaloisForLFunctions.HilbertMetric.GaussianFock
import GaloisForLFunctions.HilbertMetric.QuasiFreeFillingFano
import GaloisForLFunctions.HilbertMetric.QuasiFreeRankVarianceDiscriminant
import GaloisForLFunctions.HilbertMetric.SpectralBandwidthFano

/-!
# Slater--Pluecker log-partition connector

For an orthonormal finite feature frame, degree scaling turns the canonical Pluecker-volume
partition into the moment-generating function of the total selected degree.  This module proves
the literal differential connector: its first logarithmic derivative is the Slater spectral
mean, while its second logarithmic derivative is the Slater compression variance.  Consequently
the spectral-bandwidth Fano law is an exact theorem about the canonical Pluecker partition, not
only about an abstract compression formula.  For a fully occupied square Gram frame over any
real or complex Hilbert space, the entire partition collapses to one exponential of total degree,
so its logarithm is globally affine and its compression variance vanishes exactly.  In nonzero
rank, equality in the universal spectral-band floor is rigid: the band has width one and every
occupied energy lies at its lower endpoint.
-/

open Filter
open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {n : ℕ} {κ : Type*} [Fintype κ]

/-- Mathlib orthonormal Hilbert families satisfy the coordinate-frame interface after passage to
the canonical finite orthonormal coordinates.  This discharges the separate coordinate
certificate required by the Slater spectral API. -/
theorem orthonormalCoordinates_isOrthonormalCoordinateFrame
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : Fin n → E) (hx : Orthonormal ℝ x) :
    IsOrthonormalCoordinateFrame (orthonormalCoordinates x) := by
  intro i j
  change coordinateDot (orthonormalCoordinates x) i j =
    if i = j then 1 else 0
  rw [coordinateDot_orthonormalCoordinates]
  exact (orthonormal_iff_ite.mp hx) i j

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
    simpa using! (hasDerivAt_id t).mul_const (degree k : ℝ)
  have hexp : HasDerivAt (fun s => Real.exp (s * (degree k : ℝ)))
      (Real.exp (t * (degree k : ℝ)) * (degree k : ℝ)) t := by
    simpa only [Function.comp_apply] using!
      (Real.hasDerivAt_exp (t * (degree k : ℝ))).comp t hlinear
  simpa only [mul_assoc, mul_comm, mul_left_comm] using!
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
    simpa using! (hasDerivAt_id t).mul_const (degree k : ℝ)
  have hexp : HasDerivAt (fun s => Real.exp (s * (degree k : ℝ)))
      (Real.exp (t * (degree k : ℝ)) * (degree k : ℝ)) t := by
    simpa only [Function.comp_apply] using!
      (Real.hasDerivAt_exp (t * (degree k : ℝ))).comp t hlinear
  simpa only [mul_assoc, mul_comm, mul_left_comm, pow_two] using!
    (hexp.const_mul (degree k : ℝ)).mul_const
      (evaluation i k * evaluation j k)

/-- An orthonormal frame starts the exponential Gram path at the identity matrix. -/
theorem exponentialFeatureGram_zero
    (evaluation : Fin n → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame evaluation) :
    exponentialFeatureGram evaluation degree 0 = 1 := by
  ext i j
  simpa [exponentialFeatureGram] using! hframe i j

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

/-! ## Full-occupancy Gram-coordinate consequences -/

/-- The real part of the Gram matrix of a finite family over any real or complex Hilbert space,
viewed as a square real coordinate matrix. -/
def orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) : Fin n → Fin n → ℝ :=
  fun i j => RCLike.re (inner 𝕜 (x i) (x j))

@[simp] theorem orthonormalRealGramCoordinates_apply
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (i j : Fin n) :
    orthonormalRealGramCoordinates 𝕜 x i j = if i = j then 1 else 0 := by
  unfold orthonormalRealGramCoordinates
  rw [(orthonormal_iff_ite.mp hx) i j]
  split <;> simp

/-- The Gram coordinates of every finite orthonormal family discharge the abstract coordinate-frame
interface, without requiring a finite-dimensional ambient Hilbert space. -/
theorem orthonormalRealGramCoordinates_isOrthonormalCoordinateFrame
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) :
    IsOrthonormalCoordinateFrame (orthonormalRealGramCoordinates 𝕜 x) := by
  intro i j
  simp only [orthonormalRealGramCoordinates_apply 𝕜 x hx]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Full occupancy makes the exponential Gram path diagonal for every finite orthonormal family. -/
theorem exponentialFeatureGram_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (degree : Fin n → ℕ) (s : ℝ) :
    exponentialFeatureGram (orthonormalRealGramCoordinates 𝕜 x) degree s =
      Matrix.diagonal (fun k => Real.exp (s * (degree k : ℝ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [exponentialFeatureGram, hx]
  · simp [exponentialFeatureGram, hx, hij]

/-- **Exact full-occupancy Pluecker partition.**  The canonical feature volume of a square Gram
frame is one exponential carrying the total degree. -/
theorem orthonormalRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (degree : Fin n → ℕ) (s : ℝ) :
    canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
        degree (Real.exp s) =
      Real.exp (s * ∑ k, (degree k : ℝ)) := by
  rw [← det_exponentialFeatureGram_eq_canonicalFeatureVolume]
  rw [exponentialFeatureGram_orthonormalRealGramCoordinates 𝕜 x hx,
    Matrix.det_diagonal]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The full-occupancy Pluecker log-partition is globally affine, not merely flat to second order
at the origin. -/
theorem orthonormalRealGram_log_canonicalFeatureVolume_exp_eq
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (degree : Fin n → ℕ) (s : ℝ) :
    Real.log (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
        degree (Real.exp s)) = s * ∑ k, (degree k : ℝ) := by
  rw [orthonormalRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree 𝕜 x hx,
    Real.log_exp]

/-- **Full-occupancy log-jet classification.**  Every iterated logarithmic derivative of the
canonical feature volume is determined: order zero is the affine log-partition, order one is the
total degree, and every higher order vanishes, at every scaling parameter. -/
theorem orthonormalRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (degree : Fin n → ℕ) (order : ℕ) (s : ℝ) :
    iteratedDeriv order (fun t => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp t))) s =
      if order = 0 then s * ∑ k, (degree k : ℝ)
      else if order = 1 then ∑ k, (degree k : ℝ) else 0 := by
  have hfun :
      (fun t => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp t))) =
        fun t => t * ∑ k, (degree k : ℝ) := by
    funext t
    exact orthonormalRealGram_log_canonicalFeatureVolume_exp_eq 𝕜 x hx degree t
  rw [hfun]
  simp [iteratedDeriv_mul_const_field, iteratedDeriv_fun_id]

/-- Full occupancy makes the additive Slater mean equal the total assigned orbital energy. -/
theorem slaterSpectralMean_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (energy : Fin n → ℝ) :
    slaterSpectralMean (orthonormalRealGramCoordinates 𝕜 x) energy = ∑ k, energy k := by
  simp [slaterSpectralMean, orbitalSpectralMean, hx]

/-- Full occupancy has no residual spectral fluctuation for any orthonormal family or energy
assignment. -/
theorem slaterSpectralVariance_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (energy : Fin n → ℝ) :
    slaterSpectralVariance (orthonormalRealGramCoordinates 𝕜 x) energy = 0 := by
  simp [slaterSpectralVariance, orbitalSpectralSecondMoment,
    slaterCompressedSpectralEnergy, hx]

/-- Full occupancy identifies the Slater mean-minus-variance margin with total assigned energy,
without any spectral-band hypothesis. -/
theorem slaterSpectralFanoMargin_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (energy : Fin n → ℝ) :
    slaterSpectralFanoMargin (orthonormalRealGramCoordinates 𝕜 x) energy =
      ∑ k, energy k := by
  rw [slaterSpectralFanoMargin,
    slaterSpectralMean_orthonormalRealGramCoordinates 𝕜 x hx,
    slaterSpectralVariance_orthonormalRealGramCoordinates 𝕜 x hx]
  simp

/-- Arbitrary diagonal occupations of a square orthonormal Gram frame have spectral mean equal
to the occupation-weighted sum of orbital energies. -/
theorem quasiFreeSpectralMean_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy occupation : Fin n → ℝ) :
    quasiFreeSpectralMean (orthonormalRealGramCoordinates 𝕜 x) energy occupation =
      ∑ i, occupation i * energy i := by
  simp [quasiFreeSpectralMean, orbitalSpectralMean, hx]

/-- The quasi-free compression energy of a square orthonormal Gram frame is diagonal: each mode
contributes the square of its occupied energy. -/
theorem quasiFreeCompressedSpectralEnergy_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy occupation : Fin n → ℝ) :
    quasiFreeCompressedSpectralEnergy
        (orthonormalRealGramCoordinates 𝕜 x) energy occupation =
      ∑ i, occupation i ^ 2 * energy i ^ 2 := by
  simp [quasiFreeCompressedSpectralEnergy, hx, pow_two]

/-- **Independent-mode quasi-free variance law.**  In square orthonormal Gram coordinates every
off-diagonal compression term vanishes, leaving the sum of Bernoulli-mode variances. -/
theorem quasiFreeSpectralVariance_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy occupation : Fin n → ℝ) :
    quasiFreeSpectralVariance
        (orthonormalRealGramCoordinates 𝕜 x) energy occupation =
      ∑ i, occupation i * (1 - occupation i) * energy i ^ 2 := by
  rw [quasiFreeSpectralVariance,
    quasiFreeCompressedSpectralEnergy_orthonormalRealGramCoordinates
      𝕜 x hx energy occupation]
  simp only [orbitalSpectralSecondMoment]
  simp [hx]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Independent-mode quasi-free Fano law.**  The exact mean-minus-variance margin of a square
orthonormal Gram frame is the sum of its one-mode margins, with no band or filling hypothesis. -/
theorem quasiFreeSpectralFanoMargin_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy occupation : Fin n → ℝ) :
    quasiFreeSpectralFanoMargin
        (orthonormalRealGramCoordinates 𝕜 x) energy occupation =
      ∑ i, occupation i *
        (energy i - (1 - occupation i) * energy i ^ 2) := by
  rw [quasiFreeSpectralFanoMargin,
    quasiFreeSpectralMean_orthonormalRealGramCoordinates
      𝕜 x hx energy occupation,
    quasiFreeSpectralVariance_orthonormalRealGramCoordinates
      𝕜 x hx energy occupation]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Orthonormal rank--variance defect law.**  In square orthonormal Gram coordinates, the
quasi-free rank discriminant is exactly support rank times endpoint leakage plus the ordered
pairwise dispersion of occupied orbital energies.  The off-diagonal compression-coherence defect
vanishes identically. -/
theorem quasiFreeSpectralRankVarianceDiscriminant_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy occupation : Fin n → ℝ) (lower upper : ℝ) :
    quasiFreeSpectralRankVarianceDiscriminant
        (orthonormalRealGramCoordinates 𝕜 x) energy occupation lower upper =
      (n : ℝ) * ∑ i, occupation i * (energy i - lower) * (upper - energy i) +
        (∑ i, ∑ j,
          (occupation i * energy i - occupation j * energy j) ^ 2) / 2 := by
  have hsecant :
      quasiFreeSpectralSecantDefect
          (orthonormalRealGramCoordinates 𝕜 x) energy occupation lower upper =
        ∑ i, occupation i * (energy i - lower) * (upper - energy i) := by
    unfold quasiFreeSpectralSecantDefect
    apply Finset.sum_congr rfl
    intro i _hi
    simp [orbitalSpectralMean, orbitalSpectralSecondMoment, hx]
    ring
  have hpair :
      quasiFreeSpectralPairwiseMeanDefect
          (orthonormalRealGramCoordinates 𝕜 x) energy occupation =
        (∑ i, ∑ j,
          (occupation i * energy i - occupation j * energy j) ^ 2) / 2 := by
    simp [quasiFreeSpectralPairwiseMeanDefect, orbitalSpectralMean, hx]
  have hcoherence :
      quasiFreeSpectralCoherenceDefect
          (orthonormalRealGramCoordinates 𝕜 x) energy occupation = 0 := by
    simp [quasiFreeSpectralCoherenceDefect, hx]
  rw [quasiFreeSpectralRankVarianceDiscriminant_three_defect]
  rw [hsecant, hpair, hcoherence]
  simp

private theorem slaterSpectralSecantDefect_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy : Fin n → ℝ) (lower upper : ℝ) :
    slaterSpectralSecantDefect (orthonormalRealGramCoordinates 𝕜 x) energy lower upper =
      ∑ k, (energy k - lower) * (upper - energy k) := by
  simp only [slaterSpectralSecantDefect]
  apply Finset.sum_congr rfl
  intro i _
  simp [orbitalSpectralMean, orbitalSpectralSecondMoment, hx]
  ring

private theorem slaterSpectralCenteringDefect_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy : Fin n → ℝ) (lower upper : ℝ) :
    slaterSpectralCenteringDefect (orthonormalRealGramCoordinates 𝕜 x) energy lower upper =
      ∑ k, (energy k - (lower + upper - 1) / 2) ^ 2 := by
  simp [slaterSpectralCenteringDefect, orbitalSpectralMean, hx]

private theorem slaterSpectralCoherenceDefect_orthonormalRealGramCoordinates
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (energy : Fin n → ℝ) :
    slaterSpectralCoherenceDefect (orthonormalRealGramCoordinates 𝕜 x) energy = 0 := by
  simp [slaterSpectralCoherenceDefect, hx]

/-- **Full-occupancy spectral-floor rigidity.**  In positive rank and inside a prescribed spectral
band, a fully occupied orthonormal frame attains the universal Slater Fano floor exactly when the
band has width one and every occupied energy is its lower endpoint. -/
theorem slaterSpectralFanoMargin_orthonormalRealGramCoordinates_eq_lower_bound_iff
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (energy : Fin n → ℝ) (lower upper : ℝ) (hn : 0 < n)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    slaterSpectralFanoMargin (orthonormalRealGramCoordinates 𝕜 x) energy =
        (n : ℝ) * (lower - (upper - lower - 1) ^ 2 / 4) ↔
      upper = lower + 1 ∧ ∀ k, energy k = lower := by
  have hframe := orthonormalRealGramCoordinates_isOrthonormalCoordinateFrame 𝕜 x hx
  constructor
  · intro hmargin
    have hdefects :=
      (slaterSpectralFanoMargin_eq_lower_bound_iff
        (orthonormalRealGramCoordinates 𝕜 x) energy hframe lower upper hlower hupper).mp
        (by simpa using hmargin)
    rcases hdefects with ⟨hsecant, hcenter, _⟩
    rw [slaterSpectralSecantDefect_orthonormalRealGramCoordinates
      𝕜 x hx energy lower upper] at hsecant
    rw [slaterSpectralCenteringDefect_orthonormalRealGramCoordinates
      𝕜 x hx energy lower upper] at hcenter
    have hcenterEach (k : Fin n) :
        energy k = (lower + upper - 1) / 2 := by
      have hsquare :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i (_ : i ∈ Finset.univ) =>
            sq_nonneg (energy i - (lower + upper - 1) / 2))).mp
          hcenter k (Finset.mem_univ k)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    let i0 : Fin n := ⟨0, hn⟩
    have hsecantTerm : (energy i0 - lower) * (upper - energy i0) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsecant i0 (Finset.mem_univ i0)
      intro k _
      exact mul_nonneg (sub_nonneg.mpr (hlower k)) (sub_nonneg.mpr (hupper k))
    have hlowerUpper : lower ≤ upper := le_trans (hlower i0) (hupper i0)
    have hwidth : upper = lower + 1 := by
      rw [hcenterEach i0] at hsecantTerm
      nlinarith
    refine ⟨hwidth, ?_⟩
    intro k
    have hk := hcenterEach k
    rw [hwidth] at hk
    linarith
  · rintro ⟨hwidth, henergy⟩
    have hdefects :
        slaterSpectralSecantDefect (orthonormalRealGramCoordinates 𝕜 x)
            energy lower upper = 0 ∧
          slaterSpectralCenteringDefect (orthonormalRealGramCoordinates 𝕜 x)
            energy lower upper = 0 ∧
          slaterSpectralCoherenceDefect (orthonormalRealGramCoordinates 𝕜 x)
            energy = 0 := by
      constructor
      · rw [slaterSpectralSecantDefect_orthonormalRealGramCoordinates
          𝕜 x hx energy lower upper]
        apply Finset.sum_eq_zero
        intro k _
        rw [henergy k, hwidth]
        ring
      constructor
      · rw [slaterSpectralCenteringDefect_orthonormalRealGramCoordinates
          𝕜 x hx energy lower upper]
        apply Finset.sum_eq_zero
        intro k _
        rw [henergy k, hwidth]
        ring
      · exact slaterSpectralCoherenceDefect_orthonormalRealGramCoordinates 𝕜 x hx energy
    simpa using
      (slaterSpectralFanoMargin_eq_lower_bound_iff
        (orthonormalRealGramCoordinates 𝕜 x) energy hframe lower upper hlower hupper).mpr
        hdefects

/-- **Exact full-occupancy Pluecker Fano law.**  The first log jet minus the second is exactly the
total degree.  In contrast to partial occupancy, no positivity or quartic bandwidth premise is
needed for the identity. -/
theorem orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (degree : Fin n → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s)))) 0 = ∑ k, (degree k : ℝ) := by
  rw [canonicalFeatureVolume_logFanoMargin_eq_slaterSpectralFanoMargin
    (orthonormalRealGramCoordinates 𝕜 x) degree
    (orthonormalRealGramCoordinates_isOrthonormalCoordinateFrame 𝕜 x hx)]
  exact slaterSpectralFanoMargin_orthonormalRealGramCoordinates 𝕜 x hx _

/-- Every natural-degree full-occupancy Pluecker partition is Fano-underdispersed, with no upper
degree bound and no positive-degree premise. -/
theorem orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_nonnegative
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (degree : Fin n → ℕ) :
    0 ≤ deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s)))) 0 := by
  rw [orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree 𝕜 x hx degree]
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **Full-occupancy Fano equality classification.**  The Pluecker log-Fano margin vanishes
exactly when every occupied natural orbital degree is zero.  Thus equality in unconditional
Fano underdispersion has no hidden geometric cancellation at full occupancy. -/
theorem orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_zero_iff
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (degree : Fin n → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s)))) 0 = 0 ↔
      ∀ k, degree k = 0 := by
  rw [orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree 𝕜 x hx degree]
  constructor
  · intro hzero k
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (fun j _ => Nat.cast_nonneg (degree j))).mp (by
        simpa using hzero)
    exact_mod_cast hall k (Finset.mem_univ k)
  · intro hdegree
    simp [hdegree]

/-- The full-occupancy Pluecker log-Fano margin is strictly positive exactly when at least one
occupied natural orbital has positive degree. -/
theorem orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_pos_iff
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (degree : Fin n → ℕ) :
    0 < deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s)))) 0 ↔
      ∃ k, 0 < degree k := by
  rw [orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree 𝕜 x hx degree]
  have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (degree k : ℝ) :=
    fun k _ => Nat.cast_nonneg (degree k)
  constructor
  · intro hpos
    obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg hnonneg).mp (by
      simpa using hpos)
    exact ⟨k, by exact_mod_cast hk⟩
  · rintro ⟨k, hk⟩
    apply (Finset.sum_pos_iff_of_nonneg hnonneg).mpr
    exact ⟨k, Finset.mem_univ k, by exact_mod_cast hk⟩

/-- The full-occupancy Pluecker log-partition attains the universal spectral-band floor exactly in
the width-one, uniform-lower-degree configuration. -/
theorem orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_lower_bound_iff
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x)
    (degree : Fin n → ℕ) (lower upper : ℝ) (hn : 0 < n)
    (hlower : ∀ k, lower ≤ (degree k : ℝ))
    (hupper : ∀ k, (degree k : ℝ) ≤ upper) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s)))) 0 =
        (n : ℝ) * (lower - (upper - lower - 1) ^ 2 / 4) ↔
      upper = lower + 1 ∧ ∀ k, (degree k : ℝ) = lower := by
  rw [canonicalFeatureVolume_logFanoMargin_eq_slaterSpectralFanoMargin
    (orthonormalRealGramCoordinates 𝕜 x) degree
    (orthonormalRealGramCoordinates_isOrthonormalCoordinateFrame 𝕜 x hx)]
  exact slaterSpectralFanoMargin_orthonormalRealGramCoordinates_eq_lower_bound_iff
    𝕜 x hx (fun k => (degree k : ℝ)) lower upper hn hlower hupper

/-- Exact first- and second-log-jet form of the full-occupancy partition law. -/
theorem orthonormalRealGram_canonicalFeatureVolume_logJets_exact
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : Fin n → E) (hx : Orthonormal 𝕜 x) (degree : Fin n → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s))) 0 = ∑ k, (degree k : ℝ) ∧
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalRealGramCoordinates 𝕜 x) (fun _ => 1)
          degree (Real.exp s)))) 0 = 0 := by
  constructor
  · simpa [iteratedDeriv_succ] using
      orthonormalRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq
        𝕜 x hx degree 1 0
  · simpa [iteratedDeriv_succ] using
      orthonormalRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq
        𝕜 x hx degree 2 0

/-! ## Canonical-coordinate Hilbert-space consequences -/

/-- **Hilbert Slater--Pluecker log-jet connector.**  For an orthonormal family in any finite-
dimensional real Hilbert space, canonical coordinates identify the first two logarithmic
derivatives of the Pluecker partition with the Slater mean and variance.  No coordinate-frame
certificate remains among the hypotheses. -/
theorem orthonormalHilbert_canonicalFeatureVolume_logJets
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : Fin n → E) (hx : Orthonormal ℝ x)
    (degree : Fin (Module.finrank ℝ E) → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalCoordinates x) (fun _ => 1)
          degree (Real.exp s))) 0 =
        slaterSpectralMean (orthonormalCoordinates x)
          (fun k => (degree k : ℝ)) ∧
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalCoordinates x) (fun _ => 1)
          degree (Real.exp s)))) 0 =
        slaterSpectralVariance (orthonormalCoordinates x)
          (fun k => (degree k : ℝ)) := by
  have hframe := orthonormalCoordinates_isOrthonormalCoordinateFrame x hx
  exact ⟨canonicalFeatureVolume_logDerivative_eq_slaterSpectralMean
      (orthonormalCoordinates x) degree hframe,
    canonicalFeatureVolume_logSecondDerivative_eq_slaterSpectralVariance
      (orthonormalCoordinates x) degree hframe⟩

/-- The exact Pluecker three-defect decomposition therefore holds for every finite-dimensional
Hilbert orthonormal family in canonical coordinates. -/
theorem orthonormalHilbert_canonicalFeatureVolume_logFanoMargin_three_defect
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : Fin n → E) (hx : Orthonormal ℝ x)
    (degree : Fin (Module.finrank ℝ E) → ℕ) (lower upper : ℝ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalCoordinates x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalCoordinates x) (fun _ => 1)
          degree (Real.exp s)))) 0 =
      (n : ℝ) * (lower - (upper - lower - 1) ^ 2 / 4) +
        slaterSpectralSecantDefect (orthonormalCoordinates x)
          (fun k => (degree k : ℝ)) lower upper +
        slaterSpectralCenteringDefect (orthonormalCoordinates x)
          (fun k => (degree k : ℝ)) lower upper +
        slaterSpectralCoherenceDefect (orthonormalCoordinates x)
          (fun k => (degree k : ℝ)) := by
  exact canonicalFeatureVolume_logFanoMargin_three_defect
    (orthonormalCoordinates x) degree
    (orthonormalCoordinates_isOrthonormalCoordinateFrame x hx) lower upper

/-- Every positive degree spectrum bounded by four gives a nonnegative Pluecker log-Fano margin
for an arbitrary finite-dimensional Hilbert orthonormal family. -/
theorem positiveQuarticDegree_orthonormalHilbert_canonicalFeatureVolume_logFanoMargin_nonnegative
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : Fin n → E) (hx : Orthonormal ℝ x)
    (degree : Fin (Module.finrank ℝ E) → ℕ)
    (hpositive : ∀ k, 1 ≤ degree k) (hquartic : ∀ k, degree k ≤ 4) :
    0 ≤ deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalCoordinates x) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (orthonormalCoordinates x) (fun _ => 1)
          degree (Real.exp s)))) 0 := by
  exact positiveQuarticDegree_canonicalFeatureVolume_logFanoMargin_nonnegative
    (orthonormalCoordinates x) degree
    (orthonormalCoordinates_isOrthonormalCoordinateFrame x hx)
    hpositive hquartic

end

end GaloisForLFunctions.HilbertMetric
