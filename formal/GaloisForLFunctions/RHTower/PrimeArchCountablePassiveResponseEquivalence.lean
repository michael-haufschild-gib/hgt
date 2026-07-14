import GaloisForLFunctions.HTGeometry.FiniteKMSPassivePalette
import GaloisForLFunctions.RHTower.PrimeArchCountablePassiveResponseRH

/-!
# Exact countable finite-KMS passive-response criterion for RH

The Gaussian-rational source condition needs only closure membership of one imaginary response
value at each test point.  The universal one-state KMS palette realizes every nonpositive value,
so this physical condition is not merely sufficient: it is exactly equivalent to the source
anti-Herglotz sign and hence to RH.  This also identifies the verification boundary honestly:
finite KMS passivity supplies the closed sign chamber, while the arithmetic source must supply
membership in that chamber.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Existence of one growing finite-KMS/Wightman family whose imaginary response cluster values
contain the continued source at every Gaussian-rational test point above `R`. -/
def PrimeArchGaussianRatFiniteKMSPassiveClosureAbove (R : ℝ) : Prop :=
  ∃ (d : ℕ → ℕ) (β : ℕ → ℝ)
      (energy : ∀ N, Fin (d N + 1) → ℝ)
      (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ),
    ∀ q : ℚ × ℚ,
      0 < (gaussianRatPoint q).re →
      (gaussianRatPoint q).re < 1 / 2 →
      R < (gaussianRatPoint q).im →
      riemannZeta (gaussianRatPoint q) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace
          (gaussianRatPassiveResponsePoint q)).im ∈
        closure (Set.range (fun N ↦
          (HTGeometry.finiteTransitionPassiveResponse
            (HTGeometry.finiteKMSWightmanTransitionIntensity
              (β N) (energy N) (amplitude N)) (energy N)
              (gaussianRatPassiveResponsePoint q)).im))

/-- The explicit countable passive-closure condition above the certified radius `218 / 25`. -/
def PrimeArchGaussianRatFiniteKMSPassiveClosure : Prop :=
  PrimeArchGaussianRatFiniteKMSPassiveClosureAbove (218 / 25)

/-- Under RH, the universal one-state KMS palette supplies the countable passive closure above
every real frequency threshold. -/
theorem primeArchGaussianRatFiniteKMSPassiveClosureAbove_of_riemannHypothesis
    (R : ℝ) (hRH : RiemannHypothesis) :
    PrimeArchGaussianRatFiniteKMSPassiveClosureAbove R := by
  refine ⟨fun _ => 0, fun _ => 0,
    fun N => HTGeometry.universalOneStateKMSEnergy N,
    fun N => HTGeometry.universalOneStateKMSAmplitude N, ?_⟩
  intro q hqpos hqhalf _hqhigh hqzeta
  have hacc :=
    (completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis.mpr hRH)
      (gaussianRatPoint q) hqpos hqhalf hqzeta
  have hacc' : 0 ≤
      (completedPrimeGammaFlux (gaussianRatPoint q)).re := by
    simpa only [completedPrimeGammaFlux] using hacc
  have hsource :
      (continuedPrimeArchSourceRelativeTrace
        (gaussianRatPassiveResponsePoint q)).im ≤ 0 := by
    rw [continuedPrimeArchSourceRelativeTrace_gaussianRatPassiveResponsePoint]
    have him :
        (-Complex.I * completedPrimeGammaFlux (gaussianRatPoint q)).im =
          -(completedPrimeGammaFlux (gaussianRatPoint q)).re := by
      simp [Complex.mul_im]
    rw [him]
    exact neg_nonpos.mpr hacc'
  have hzpos : 0 < (gaussianRatPassiveResponsePoint q).im := by
    rw [gaussianRatPassiveResponsePoint_im]
    linarith
  rw [HTGeometry.closure_range_universalOneStateKMSPassiveResponse_im hzpos]
  exact hsource

/-- The universal finite-KMS cluster condition is exactly the one-sided continued-source
passivity condition above the same frequency threshold.  No quartet estimate or RH assumption is
used in this carrier-identification theorem. -/
theorem primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_positiveFrequency
    (R : ℝ) :
    PrimeArchGaussianRatFiniteKMSPassiveClosureAbove R ↔
      ContinuedPrimeArchPositiveFrequencyAbove R := by
  constructor
  · rintro ⟨d, β, energy, amplitude, hclosure⟩
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
  · intro hhigh
    refine ⟨fun _ => 0, fun _ => 0,
      fun N => HTGeometry.universalOneStateKMSEnergy N,
      fun N => HTGeometry.universalOneStateKMSAmplitude N, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hzpos : 0 < (gaussianRatPassiveResponsePoint q).im := by
      rw [gaussianRatPassiveResponsePoint_im]
      linarith
    have hzhalf : (gaussianRatPassiveResponsePoint q).im < 1 / 2 := by
      rw [gaussianRatPassiveResponsePoint_im]
      linarith
    have hzre : (gaussianRatPassiveResponsePoint q).re =
        (gaussianRatPoint q).im := by
      simp [gaussianRatPassiveResponsePoint, Complex.mul_re]
    have hsource := hhigh (gaussianRatPassiveResponsePoint q) hzpos hzhalf
      (by rw [hzre]; exact hqhigh) (by
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
        simpa only [hcoord] using hqzeta)
    rw [HTGeometry.closure_range_universalOneStateKMSPassiveResponse_im hzpos]
    exact hsource

/-- **Exact variable-radius countable passive-response criterion.**  At every exact
quartet-admissible radius, membership of the Gaussian-rational continued source values in one
finite-KMS passive cluster family is equivalent to RH. -/
theorem primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_riemannHypothesis
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    PrimeArchGaussianRatFiniteKMSPassiveClosureAbove R ↔ RiemannHypothesis :=
  (primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_positiveFrequency R).trans
    (continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
      R hband)

/-- Under RH, the universal one-state KMS palette supplies the countable passive closure. -/
theorem primeArchGaussianRatFiniteKMSPassiveClosure_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchGaussianRatFiniteKMSPassiveClosure :=
  primeArchGaussianRatFiniteKMSPassiveClosureAbove_of_riemannHypothesis
    (218 / 25) hRH

/-- **Exact countable passive-response criterion.**  A single family of finite canonical KMS
systems whose imaginary cluster values contain the countable source tests exists exactly under
RH. -/
theorem primeArchGaussianRatFiniteKMSPassiveClosure_iff_riemannHypothesis :
    PrimeArchGaussianRatFiniteKMSPassiveClosure ↔ RiemannHypothesis :=
  primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_riemannHypothesis
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

end

end RHTower
