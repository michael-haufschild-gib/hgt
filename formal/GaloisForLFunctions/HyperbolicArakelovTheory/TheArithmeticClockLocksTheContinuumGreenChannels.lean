import GaloisForLFunctions.HyperbolicArakelovTheory.TheArithmeticMassClockOfThePrimeGreenKernel
import GaloisForLFunctions.HyperbolicArakelovTheory.TheContinuumGreenChannelsRecoverThePrimeSum
import GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledOrbitDensityMatchesTheArchimedeanConstants

/-!
# Arithmetic locking of the continuum Green channels

Fill the positive prime channels to the archimedean self-energy plus the
geometric constant supplied by the rational torus density. For each compact
packet, mass subtraction eventually gives its exact prime term. Coupling to
the hyperbolic Green damping then converges to Weil's full quadratic form.

The clock is independent of the packet. It uses the arithmetic ordering of
the prime capacities and the real translation representation of the ladders;
no torus-periodized kernel on the adelic quotient is asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open _root_.RHTower SpacingScaleHarmonicAnalysis SurfaceOfSpecZ

/-- Finite positive combination of continuum prime Green channels at prescribed mass. -/
def clockedPrimeChannel (S : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ᶠ p, clockWeight S p * continuumChannel p f

private theorem clockWeight_not_prime (S : ℝ) {p : ℕ} (hp : ¬p.Prime) :
    clockWeight S p = 0 := by
  simp only [clockWeight, primeCapacity, if_neg hp, div_zero]

theorem clockedPrimeChannel_nonneg (S : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : 0 ≤ clockedPrimeChannel S f := by
  apply finsum_nonneg
  intro p
  by_cases hp : p.Prime
  · exact mul_nonneg (clockWeight_nonneg S p) (continuumChannel_nonneg hp hf hfc)
  · rw [clockWeight_not_prime S hp, zero_mul]

private theorem clockedPrimeChannel_eq_sum {S : ℝ} {Q : ℕ}
    (hS : S ≤ cumulativeCapacity Q) (f : ℝ → ℝ) :
    clockedPrimeChannel S f = ∑ p ∈ Finset.range Q, clockWeight S p * continuumChannel p f := by
  apply finsum_eq_sum_of_support_subset
  intro p hp
  by_contra hmem
  have hQp : Q ≤ p := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  exact hp (by
    change clockWeight S p * continuumChannel p f = 0
    rw [clockWeight, filledCapacity_eq_zero hS hQp, zero_div, zero_mul])

/-- Beyond a compact packet's prime horizon, arithmetic locking is an exact identity. -/
theorem eventually_clockedPrimeChannel_sub_mass {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∀ᶠ S : ℝ in atTop,
      clockedPrimeChannel S f - S * (∫ u, f u ^ 2) = -primeSum f := by
  obtain ⟨N, hsum, htail⟩ := primeSum_eq_finite_channels hfc
  filter_upwards [eventually_ge_atTop (cumulativeCapacity (N + 1))] with S hS
  have hS0 := (cumulativeCapacity_nonneg (N + 1)).trans hS
  obtain ⟨Q₀, hQ₀⟩ :=
    (tendsto_cumulativeCapacity_atTop.eventually (eventually_ge_atTop S)).exists
  let Q := max Q₀ (N + 1)
  have hSQ : S ≤ cumulativeCapacity Q := hQ₀.trans (cumulativeCapacity_mono (le_max_left _ _))
  have hNQ : N + 1 ≤ Q := le_max_right _ _
  have hterm (p : ℕ) : clockWeight S p * continuumChannel p f =
      filledCapacity S p * (∫ u, f u ^ 2) - clockWeight S p * primeCorrelation p f := by
    by_cases hp : p.Prime
    · have hm := clockWeight_mul_capacity S p
      rw [primeCapacity, if_pos hp] at hm
      rw [continuumChannel, mul_sub, ← mul_assoc, hm]
    · have hw := clockWeight_not_prime S hp
      have hc : filledCapacity S p = 0 := by
        simpa only [hw, zero_mul] using (clockWeight_mul_capacity S p).symm
      rw [hw, hc, zero_mul, zero_mul, zero_mul, sub_zero]
  have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.range Q := by
    intro p hp
    have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact Finset.mem_range.mpr (lt_of_le_of_lt hpN (lt_of_lt_of_le (Nat.lt_succ_self N) hNQ))
  have hcorr : (∑ p ∈ Finset.range Q, clockWeight S p * primeCorrelation p f) = primeSum f := by
    calc
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, clockWeight S p * primeCorrelation p f := by
        symm
        apply Finset.sum_subset hsub
        intro p hp hpnot
        by_cases hpp : p.Prime
        · have hNp : N < p := by
            by_contra h
            exact hpnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.one_le, not_lt.mp h⟩, hpp⟩)
          rw [htail p hpp hNp, mul_zero]
        · rw [clockWeight_not_prime S hpp, zero_mul]
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, primeCorrelation p f := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpp := (Finset.mem_filter.mp hp).2
        have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        rw [clockWeight_eq_one hpp ((cumulativeCapacity_mono (Nat.succ_le_succ hpN)).trans hS), one_mul]
      _ = _ := hsum.symm
  rw [clockedPrimeChannel_eq_sum hSQ]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_filledCapacity,
    min_eq_left hSQ, min_eq_right hS0, sub_zero, hcorr]
  ring

/-- The finite scalar is determined by the regular rational-torus density and the cusp constant. -/
def geometricScalar : ℝ :=
  -4 * CoupledOrbit.regularMean - (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)

theorem geometricScalar_eq : geometricScalar = 2 * gammaHardyPhaseRate 0 :=
  ArchimedeanConstantBridge.two_mul_gammaHardyPhaseRate_zero_eq.symm

/-- A single clock for all packets, expressed entirely in the Green and geometric constants. -/
def arithmeticClock (r : ℝ) : ℝ := selfEnergy r + geometricScalar

theorem tendsto_arithmeticClock_atTop : Tendsto arithmeticClock (𝓝[<] 1) atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [tendsto_selfEnergy_atTop.eventually (eventually_ge_atTop (B - geometricScalar))]
    with r hr
  dsimp only [arithmeticClock]
  linarith only [hr]

/-- Pole compensation coupled to hyperbolic and arithmetic Green channels. -/
def coupledGreenEnergy (r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) - smoothGreenEnergy r f +
    clockedPrimeChannel (arithmeticClock r) f

/-- The same arithmetic clock recovers Weil's full form on every compact smooth packet. -/
theorem tendsto_coupledGreenEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun r => coupledGreenEnergy r f) (𝓝[<] 1) (𝓝 (weilQuad f)) := by
  have hgreen := tendsto_smoothGreenEnergy_sub_mass f hf hfc
  have hclock := tendsto_arithmeticClock_atTop.eventually
    (eventually_clockedPrimeChannel_sub_mass hfc)
  have hlimit : Tendsto (fun r =>
      -(smoothGreenEnergy r f - (∫ u, f u ^ 2) * selfEnergy r) +
        geometricScalar * (∫ u, f u ^ 2) - primeSum f +
          (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2))
      (𝓝[<] 1) (𝓝 (weilQuad f)) := by
    have hM : Tendsto (fun _ : ℝ => geometricScalar * (∫ u, f u ^ 2))
        (𝓝[<] 1) (𝓝 (geometricScalar * (∫ u, f u ^ 2))) := tendsto_const_nhds
    have hP : Tendsto (fun _ : ℝ => primeSum f)
        (𝓝[<] 1) (𝓝 (primeSum f)) := tendsto_const_nhds
    have hPole : Tendsto (fun _ : ℝ => 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)
        (𝓝[<] 1) (𝓝 (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)) := tendsto_const_nhds
    have he : levyEnergy f + geometricScalar * (∫ u, f u ^ 2) - primeSum f +
        (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) = weilQuad f := by
      rw [weilQuad_eq hf hfc, ← geometricScalar_eq]
      ring
    simpa only [neg_neg, he] using ((hgreen.neg.add hM).sub hP).add hPole
  apply hlimit.congr'
  filter_upwards [hclock] with r hr
  dsimp only [arithmeticClock] at hr
  dsimp only [coupledGreenEnergy, arithmeticClock]
  linear_combination -hr

#print axioms clockedPrimeChannel_nonneg
#print axioms eventually_clockedPrimeChannel_sub_mass
#print axioms tendsto_coupledGreenEnergy

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
