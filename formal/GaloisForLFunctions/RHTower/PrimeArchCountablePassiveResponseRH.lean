import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.PrimeArchPassiveResponseRH
import GaloisForLFunctions.RHTower.CCM.CCMCompletedPrimeGammaAccretivityCriterion

open Filter Topology Set Metric

namespace RHTower

noncomputable section

/-!
# Countable dissipative finite-KMS cluster values imply RH

Finite KMS/Wightman systems have an automatic passive sign.  To transfer that sign to the
continued prime--archimedean source, full complex-valued thermodynamic convergence on the whole
upper strip is unnecessary.  Gaussian-rational density reduces the analytic test set to a
countable family, taking imaginary parts reduces each test to one real value, and closedness of
the passive half-line reduces convergence to cluster-value membership.
-/

/-- The response coordinate attached to a Gaussian-rational source point. -/
def gaussianRatPassiveResponsePoint (q : ℚ × ℚ) : ℂ :=
  (gaussianRatPoint q - 1 / 2) * (-Complex.I)

theorem gaussianRatPassiveResponsePoint_im (q : ℚ × ℚ) :
    (gaussianRatPassiveResponsePoint q).im =
      1 / 2 - (gaussianRatPoint q).re := by
  simp [gaussianRatPassiveResponsePoint, Complex.mul_im]

/-- The centered response coordinate and the original source coordinate give the same continued
prime--Gamma value; the imaginary response value is the negative real flux value. -/
theorem continuedPrimeArchSourceRelativeTrace_gaussianRatPassiveResponsePoint
    (q : ℚ × ℚ) :
    continuedPrimeArchSourceRelativeTrace (gaussianRatPassiveResponsePoint q) =
      -Complex.I * completedPrimeGammaFlux (gaussianRatPoint q) := by
  have hcoord :
      1 / 2 + gaussianRatPassiveResponsePoint q * Complex.I =
        gaussianRatPoint q := by
    rw [gaussianRatPassiveResponsePoint]
    have hnegII : (-Complex.I) * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I]
      norm_num
    calc
      1 / 2 + (gaussianRatPoint q - 1 / 2) * (-Complex.I) * Complex.I =
          1 / 2 + (gaussianRatPoint q - 1 / 2) *
            ((-Complex.I) * Complex.I) := by ring
      _ = gaussianRatPoint q := by rw [hnegII]; ring
  rw [continuedPrimeArchSourceRelativeTrace, completedPrimeGammaFlux, hcoord]

/-- Completed prime--Gamma accretivity above a variable positive frequency. -/
def CompletedPrimeGammaPositiveFrequencyAbove (R : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → R < s.im →
    riemannZeta s ≠ 0 → 0 ≤ (completedPrimeGammaFlux s).re

/-- Countable Gaussian-rational restriction of positive-frequency completed source accretivity. -/
def CompletedPrimeGammaGaussianRatPositiveFrequencyAbove (R : ℝ) : Prop :=
  ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 → R < (gaussianRatPoint q).im →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      0 ≤ (completedPrimeGammaFlux (gaussianRatPoint q)).re

/-- Continuity and Gaussian-rational density upgrade the countable source values above any fixed
frequency to the full positive-frequency completed source condition. -/
theorem completedPrimeGammaPositiveFrequencyAbove_of_gaussianRat
    (R : ℝ) (hrat : CompletedPrimeGammaGaussianRatPositiveFrequencyAbove R) :
    CompletedPrimeGammaPositiveFrequencyAbove R := by
  intro s hspos hshalf hsIm hzeta
  by_contra hnonneg
  have hneg : (completedPrimeGammaFlux s).re < 0 := lt_of_not_ge hnonneg
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.one_re] at hre
    linarith
  have hcont := continuousAt_completedPrimeGammaFlux hspos hs1 hzeta
  have hrePos : {w : ℂ | 0 < w.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos
  have hreHalf : {w : ℂ | w.re < 1 / 2} ∈ nhds s :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hshalf
  have himHigh : {w : ℂ | R < w.im} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hsIm
  have hzetaAn : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hzetaNe : {w : ℂ | riemannZeta w ≠ 0} ∈ nhds s :=
    hzetaAn.continuousAt.eventually_ne hzeta
  have hfre : ContinuousAt (fun w ↦ (completedPrimeGammaFlux w).re) s :=
    Complex.continuous_re.continuousAt.comp hcont
  have hfluxNeg : {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    hfre.tendsto (Iio_mem_nhds hneg)
  have hall : {w : ℂ | 0 < w.re} ∩ {w : ℂ | w.re < 1 / 2} ∩
      {w : ℂ | R < w.im} ∩ {w : ℂ | riemannZeta w ≠ 0} ∩
      {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    inter_mem (inter_mem (inter_mem (inter_mem hrePos hreHalf) himHigh) hzetaNe)
      hfluxNeg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨s, mem_ball_self hr⟩
  have hq := hball hqball
  have hqnonneg := hrat q hq.1.1.1.1 hq.1.1.1.2 hq.1.1.2 hq.1.2
  exact (not_lt_of_ge hqnonneg) hq.2

/-- RH supplies every Gaussian-rational positive-frequency restriction. -/
theorem completedPrimeGammaGaussianRatPositiveFrequencyAbove_of_riemannHypothesis
    (R : ℝ) (hRH : RiemannHypothesis) :
    CompletedPrimeGammaGaussianRatPositiveFrequencyAbove R := by
  have hfull : CompletedPrimeGammaLeftHalfAccretive :=
    completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis.mpr hRH
  intro q hqpos hqhalf _hqhigh hqzeta
  exact hfull (gaussianRatPoint q) hqpos hqhalf hqzeta

/-- Original-coordinate completed accretivity above `R` supplies the centered passive-response
condition above the same frequency. -/
theorem continuedPrimeArchPositiveFrequencyAbove_of_completedPrimeGamma
    (R : ℝ) (hacc : CompletedPrimeGammaPositiveFrequencyAbove R) :
    ContinuedPrimeArchPositiveFrequencyAbove R := by
  intro z hzIm hzHalf hzRe hzeta
  let s : ℂ := 1 / 2 + z * Complex.I
  have hsRe : s.re = 1 / 2 - z.im := by
    simp [s, Complex.mul_re]
    ring
  have hsIm : s.im = z.re := by simp [s, Complex.mul_im]
  have hspos : 0 < s.re := by rw [hsRe]; linarith
  have hshalf : s.re < 1 / 2 := by rw [hsRe]; linarith
  have haccS := hacc s hspos hshalf (by rw [hsIm]; exact hzRe)
    (by simpa only [s] using hzeta)
  rw [continuedPrimeArchSourceRelativeTrace]
  change (-Complex.I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0
  simp only [Complex.mul_im, Complex.I_re, zero_mul, Complex.neg_im,
    Complex.I_im, neg_mul, one_mul]
  dsimp only [completedPrimeGammaFlux] at haccS
  linarith

/-- At the exact quartet threshold, the countable positive-frequency source interface is RH. -/
theorem
    completedPrimeGammaGaussianRatPositiveFrequencyAbove_twoHundredEighteen_twentyFifths_iff_rh :
    CompletedPrimeGammaGaussianRatPositiveFrequencyAbove (218 / 25) ↔
      RiemannHypothesis := by
  constructor
  · intro hrat
    apply
      continuedPrimeArchPositiveFrequencyAbove_twoHundredEighteen_twentyFifths_iff_rh.mp
    exact continuedPrimeArchPositiveFrequencyAbove_of_completedPrimeGamma
      (218 / 25)
      (completedPrimeGammaPositiveFrequencyAbove_of_gaussianRat (218 / 25) hrat)
  · exact
      completedPrimeGammaGaussianRatPositiveFrequencyAbove_of_riemannHypothesis
        (218 / 25)

/-- **Countable dissipative cluster-value RH capstone.**  Fix one growing family of finite
KMS/Wightman systems.  It is enough that, at every Gaussian-rational point of the open left
half-strip with positive height above `218 / 25` and away from zeta zeros, the single imaginary
continued-source value belongs to the
closure of the corresponding finite response values.  Neither convergence of the real parts,
convergence at non-rational points, nor convergence of the complete response functions is needed.

The conclusion uses only finite-system passivity, closedness of `(-∞, 0]`, the exact coordinate
identity above, and the existing Gaussian-rational density theorem. -/
theorem riemannHypothesis_of_gaussianRat_positiveHigh_finiteKMSWightmanResponse_im_mem_closure
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hclosure : ∀ q : ℚ × ℚ,
      0 < (gaussianRatPoint q).re →
      (gaussianRatPoint q).re < 1 / 2 →
      218 / 25 < (gaussianRatPoint q).im →
      riemannZeta (gaussianRatPoint q) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace
          (gaussianRatPassiveResponsePoint q)).im ∈
        closure (Set.range (fun N ↦
          (HTGeometry.finiteTransitionPassiveResponse
            (HTGeometry.finiteKMSWightmanTransitionIntensity
              (β N) (energy N) (amplitude N)) (energy N)
              (gaussianRatPassiveResponsePoint q)).im))) :
    RiemannHypothesis := by
  apply continuedPrimeArchPositiveFrequencyAbove_twoHundredEighteen_twentyFifths_iff_rh.mp
  apply continuedPrimeArchPositiveFrequencyAbove_of_completedPrimeGamma
  apply completedPrimeGammaPositiveFrequencyAbove_of_gaussianRat
  intro q hqpos hqhalf hqhigh hqzeta
  have hzpos : 0 < (gaussianRatPassiveResponsePoint q).im := by
    rw [gaussianRatPassiveResponsePoint_im]
    linarith
  have hrange :
      Set.range (fun N ↦
          (HTGeometry.finiteTransitionPassiveResponse
            (HTGeometry.finiteKMSWightmanTransitionIntensity
              (β N) (energy N) (amplitude N)) (energy N)
              (gaussianRatPassiveResponsePoint q)).im) ⊆ Set.Iic 0 := by
    rintro _ ⟨N, rfl⟩
    exact HTGeometry.finiteKMSWightmanTransitionPassiveResponse_im_nonpos
      (β N) (energy N) (amplitude N) hzpos
  have hsourceNonpos :
      (continuedPrimeArchSourceRelativeTrace
          (gaussianRatPassiveResponsePoint q)).im ≤ 0 :=
    (closure_minimal hrange isClosed_Iic)
      (hclosure q hqpos hqhalf hqhigh hqzeta)
  have him :
      (-Complex.I * completedPrimeGammaFlux (gaussianRatPoint q)).im =
        -(completedPrimeGammaFlux (gaussianRatPoint q)).re := by
    simp [Complex.mul_im]
  rw [continuedPrimeArchSourceRelativeTrace_gaussianRatPassiveResponsePoint, him]
    at hsourceNonpos
  exact neg_nonpos.mp hsourceNonpos

end

end RHTower
