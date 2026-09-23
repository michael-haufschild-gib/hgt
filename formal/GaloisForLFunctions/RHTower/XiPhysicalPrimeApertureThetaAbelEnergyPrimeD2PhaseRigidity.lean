import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeCofinalScheduleInvariance
import GaloisForLFunctions.RHTower.PrimeArchFourthTracePurePrimeTail

/-!
# D2-to-physical-prime contour phase rigidity

D2 controls only the real part of a complex pure-prime defect.  This module classifies exactly
when such a scalar floor survives multiplication by a complex contour weight: the multiplier must
be a nonnegative real number, and a squared multiplier works exactly when its base has real phase.

The physical two-edge transform is entire, even, and Schwarz-real.  Those symmetries force real
phase exactly on the union of the coordinate axes; every D2 strip point maps strictly off both
axes.  Thus even/Schwarz symmetry alone cannot turn D2's scalar floor into pointwise positivity of
the physical squared contour integrand.  The strongest survivor is an exact global dictionary:
cofinal unboundedness below of the D2 defect is equivalent to an eventually strict negative
physical corrected-prime sample on every cofinal admissible contour schedule.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- A complex multiplier preserves the order induced by real part. -/
def ComplexRealPartMonotoneMultiplier (w : ℂ) : Prop :=
  ∀ u v : ℂ, u.re ≤ v.re → (w * u).re ≤ (w * v).re

theorem complexRealPartMonotoneMultiplier_iff (w : ℂ) :
    ComplexRealPartMonotoneMultiplier w ↔ w.im = 0 ∧ 0 ≤ w.re := by
  constructor
  · intro h
    have hI := h 0 I (by simp)
    have hnegI := h I 0 (by simp)
    have hre := h 0 1 (by norm_num)
    constructor
    · simp only [mul_zero, zero_re, mul_re, I_re, I_im, mul_one] at hI hnegI
      linarith
    · simpa using hre
  · rintro ⟨hwim, hwre⟩ u v huv
    simp only [mul_re, hwim, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left huv hwre

theorem complexRealPartMonotoneMultiplier_sq_iff (w : ℂ) :
    ComplexRealPartMonotoneMultiplier (w ^ (2 : ℕ)) ↔ w.im = 0 := by
  rw [complexRealPartMonotoneMultiplier_iff]
  constructor
  · rintro ⟨hsqim, hsqre⟩
    simp only [pow_two, mul_im, mul_re] at hsqim hsqre
    have hprod : w.re * w.im = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hre | him
    · rw [hre] at hsqre
      nlinarith [sq_nonneg w.im]
    · exact him
  · intro hwim
    constructor
    · simp [pow_two, mul_im, hwim]
    · simp only [pow_two, mul_re, hwim, mul_zero, sub_zero]
      simpa [pow_two] using sq_nonneg w.re

/-- Entire modes carrying the two symmetries of the physical energy transform. -/
def EvenSchwarzRealEntireMode (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    (∀ s, f (-s) = f s) ∧
    (∀ s, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s))

theorem evenSchwarzRealEntireMode_im_eq_zero_of_axis
    {f : ℂ → ℂ} (hf : EvenSchwarzRealEntireMode f)
    {z : ℂ} (hz : z.im = 0 ∨ z.re = 0) :
    (f z).im = 0 := by
  rcases hf with ⟨_hdiff, heven, hschwarz⟩
  have hconj := hschwarz z
  rcases hz with hreal | himag
  · have hzconj : (starRingEnd ℂ) z = z := by
      apply Complex.ext <;> simp [hreal]
    rw [hzconj] at hconj
    have him := congrArg Complex.im hconj
    simp at him
    linarith
  · have hzconj : (starRingEnd ℂ) z = -z := by
      apply Complex.ext <;> simp [himag]
    rw [hzconj, heven] at hconj
    have him := congrArg Complex.im hconj
    simp at him
    linarith

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_evenSchwarzRealEntireMode
    (L A c a : ℝ) :
    EvenSchwarzRealEntireMode
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) := by
  refine ⟨?_, xiPhysicalThetaAbelEnergyTwoEdgeTransform_neg L A c a,
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_conj L A c a⟩
  have hamp := xiPhysicalThetaAbelEntireModeAmplitude_differentiable L A c
  have hposamp : Differentiable ℂ (fun s : ℂ =>
      xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s)) :=
    hamp.comp (by fun_prop)
  have hnegamp : Differentiable ℂ (fun s : ℂ =>
      xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s))) :=
    hamp.comp (by fun_prop)
  have hposexp : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((a : ℂ) * (I * s))) := by fun_prop
  have hnegexp : Differentiable ℂ (fun s : ℂ =>
      Complex.exp (-(a : ℂ) * (I * s))) := by fun_prop
  unfold xiPhysicalThetaAbelEnergyTwoEdgeTransform
  exact (hposexp.mul hposamp).add (hnegexp.mul hnegamp)

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_im_eq_zero_of_axis
    (L A c a : ℝ) {z : ℂ} (hz : z.im = 0 ∨ z.re = 0) :
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z).im = 0 := by
  exact evenSchwarzRealEntireMode_im_eq_zero_of_axis
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform_evenSchwarzRealEntireMode L A c a) hz

theorem physicalTwoEdgeSquare_realPartMonotone_of_axis
    (L A c a : ℝ) {z : ℂ} (hz : z.im = 0 ∨ z.re = 0) :
    ComplexRealPartMonotoneMultiplier
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ)) := by
  rw [complexRealPartMonotoneMultiplier_sq_iff]
  exact xiPhysicalThetaAbelEnergyTwoEdgeTransform_im_eq_zero_of_axis L A c a hz

/-- A physical squared contour weight transports scalar real-part floors exactly at real phase. -/
theorem physicalTwoEdgeSquare_realPartMonotone_iff_realPhase
    (L A c a : ℝ) (z : ℂ) :
    ComplexRealPartMonotoneMultiplier
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ)) ↔
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z).im = 0 := by
  exact complexRealPartMonotoneMultiplier_sq_iff _

/-- Contour coordinate corresponding to a prime-flux point `s = 1/2 + i z`. -/
def primeFluxContourCoordinate (s : ℂ) : ℂ :=
  -I * (s - 1 / 2)

theorem half_add_I_mul_primeFluxContourCoordinate (s : ℂ) :
    1 / 2 + primeFluxContourCoordinate s * I = s := by
  rw [primeFluxContourCoordinate, mul_assoc, mul_comm (s - 1 / 2) I, ← mul_assoc]
  simp

theorem primeFluxContourCoordinate_re (s : ℂ) :
    (primeFluxContourCoordinate s).re = s.im := by
  simp [primeFluxContourCoordinate, Complex.mul_re]

theorem primeFluxContourCoordinate_im (s : ℂ) :
    (primeFluxContourCoordinate s).im = 1 / 2 - s.re := by
  simp [primeFluxContourCoordinate, Complex.mul_im]

theorem gaussianRat_primeFluxContourCoordinate_off_axes
    {q : ℚ × ℚ}
    (hre : 0 < (gaussianRatPoint q).re)
    (hhalf : (gaussianRatPoint q).re < 1 / 2)
    (hhigh : 233 / 20 < (gaussianRatPoint q).im) :
    (primeFluxContourCoordinate (gaussianRatPoint q)).re ≠ 0 ∧
      (primeFluxContourCoordinate (gaussianRatPoint q)).im ≠ 0 := by
  rw [primeFluxContourCoordinate_re, primeFluxContourCoordinate_im]
  constructor <;> linarith

/-- Evenness and Schwarz symmetry force real values on the axes but do not force them off-axis. -/
theorem exists_even_schwarzReal_entireMode_nonreal_at_off_axes
    {z : ℂ} (hre : z.re ≠ 0) (him : z.im ≠ 0) :
    ∃ f : ℂ → ℂ, EvenSchwarzRealEntireMode f ∧ (f z).im ≠ 0 := by
  refine ⟨fun s => s ^ (2 : ℕ), ⟨?_, ?_, ?_⟩, ?_⟩
  · fun_prop
  · intro s
    ring
  · intro s
    simp
  · simp only [pow_two, mul_im]
    rw [mul_comm z.im z.re, ← two_mul]
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero hre him)

/-- The coordinate axes are exactly the points where evenness and Schwarz symmetry force reality. -/
theorem all_evenSchwarzRealEntireMode_real_iff_axis (z : ℂ) :
    (∀ f : ℂ → ℂ, EvenSchwarzRealEntireMode f → (f z).im = 0) ↔
      z.im = 0 ∨ z.re = 0 := by
  constructor
  · intro hall
    by_contra haxis
    simp only [not_or] at haxis
    obtain ⟨f, hf, hnonreal⟩ :=
      exists_even_schwarzReal_entireMode_nonreal_at_off_axes haxis.2 haxis.1
    exact hnonreal (hall f hf)
  · intro haxis f hf
    exact evenSchwarzRealEntireMode_im_eq_zero_of_axis hf haxis

/-- Every D2 strip point is outside the symmetry-forced real locus for an even Schwarz-real
entire contour mode. -/
theorem gaussianRat_d2Point_evenSchwarzRealEntireMode_phase_not_forced
    {q : ℚ × ℚ}
    (hre : 0 < (gaussianRatPoint q).re)
    (hhalf : (gaussianRatPoint q).re < 1 / 2)
    (hhigh : 233 / 20 < (gaussianRatPoint q).im) :
    ¬ ∀ f : ℂ → ℂ, EvenSchwarzRealEntireMode f →
      (f (primeFluxContourCoordinate (gaussianRatPoint q))).im = 0 := by
  rw [all_evenSchwarzRealEntireMode_real_iff_axis]
  obtain ⟨hre0, him0⟩ :=
    gaussianRat_primeFluxContourCoordinate_off_axes hre hhalf hhigh
  exact not_or.mpr ⟨him0, hre0⟩

/-- Complex defect whose real part is D2's scalar pure-prime defect. -/
def primeArchLogHeightComplexDefect (s : ℂ) : ℂ :=
  2 * infinitePrimeFlux s - (Real.log s.im : ℂ)

theorem primeArchLogHeightComplexDefect_re (s : ℂ) :
    (primeArchLogHeightComplexDefect s).re = primeArchLogHeightDefect s := by
  simp [primeArchLogHeightComplexDefect, primeArchLogHeightDefect]

theorem weighted_primeArchLogHeightComplexDefect_floor
    {w s : ℂ} (hw : ComplexRealPartMonotoneMultiplier w)
    {K : ℝ} (hK : K ≤ primeArchLogHeightDefect s) :
    (w * (K : ℂ)).re ≤ (w * primeArchLogHeightComplexDefect s).re := by
  apply hw
  simpa [primeArchLogHeightComplexDefect_re] using hK

/-- Exact positive survivor: a D2 scalar floor transports through a physical squared contour
weight once the local transform phase is real. -/
theorem physicalTwoEdge_weighted_primeArchLogHeightComplexDefect_floor
    (L A c a : ℝ) {s : ℂ} {K : ℝ}
    (hphase :
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
        (primeFluxContourCoordinate s)).im = 0)
    (hK : K ≤ primeArchLogHeightDefect s) :
    let w := xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
      (primeFluxContourCoordinate s) ^ (2 : ℕ)
    (w * (K : ℂ)).re ≤ (w * primeArchLogHeightComplexDefect s).re := by
  dsimp only
  exact weighted_primeArchLogHeightComplexDefect_floor
    ((complexRealPartMonotoneMultiplier_sq_iff _).2 hphase) hK

/-- Cofinal unboundedness below of D2's scalar prime defect. -/
def PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow
    (R : ℝ) : Prop :=
  ∀ B : ℝ, ∃ q : ℚ × ℚ,
    0 < (gaussianRatPoint q).re ∧
    (gaussianRatPoint q).re < 1 / 2 ∧
    R < (gaussianRatPoint q).im ∧
    primeArchLogHeightDefect (gaussianRatPoint q) < B

theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow_iff_not_rh :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow
      (233 / 20) ↔ ¬RiemannHypothesis := by
  constructor
  · intro hunbounded hRH
    obtain ⟨L, hL⟩ :=
      (primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mpr
        hRH)
    obtain ⟨q, hqre, hqhalf, hqhigh, hqbad⟩ := hunbounded L
    exact (not_lt_of_ge (hL q hqre hqhalf hqhigh)) hqbad
  · intro hnot B
    exact exists_gaussianRat_primeArchLogHeightDefect_lt_of_not_rh hnot B

/-- Exact failure-witness dictionary between D2 and every physical corrected-prime schedule. -/
theorem d2CofinallyUnboundedBelow_iff_allPrimeCofinalSchedulesEventuallyNegativeWitness
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow
        (233 / 20) ↔
      ∀ S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule,
        S.EventuallyNegativeWitness L A c := by
  rw [primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow_iff_not_rh,
    all_primeCofinalSchedules_eventuallyNegativeWitness_iff_not_rh hL hA hc]

theorem unitD2CofinallyUnboundedBelow_iff_allPrimeCofinalSchedulesEventuallyNegativeWitness :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow
        (233 / 20) ↔
      ∀ S : XiPhysicalThetaAbelEnergyPrimeCofinalSchedule,
        S.EventuallyNegativeWitness 1 1 1 := by
  exact d2CofinallyUnboundedBelow_iff_allPrimeCofinalSchedulesEventuallyNegativeWitness
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
