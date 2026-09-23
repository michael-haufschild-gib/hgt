import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureAdaptiveDivisorCensorship

/-!
# Physical FCRJ carrier as a Mertens-discrepancy coboundary

The moving physical prime-log flux is exactly one constant continuum window mass plus a
two-endpoint increment of cumulative Mertens discrepancy. After physical aperture centering, the
continuum term disappears and fusion energy becomes precisely the variance of that discrepancy
coboundary.

At fixed physical scale `X` and ratio width `c`, this converts the remaining carrier bound without
loss into a Selberg-type mean square for
`D(log X + c - u) - D(log X - u)`, with exact endpoint weight `log p / p` and exact clipping mean.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Cumulative physical prime-log mass of a finite packet. -/
def xiPhysicalPrimeLogCumulativeMass
    (P : Finset Nat.Primes) (t : ℝ) : ℝ :=
  ∑ p ∈ P, if Real.log (p : ℝ) ≤ t then
    physicalPrimeEndpointWeight p else 0

/-- Discrepancy from unit Lebesgue density in the log coordinate. -/
def xiPhysicalPrimeLogCumulativeMertensDiscrepancy
    (P : Finset Nat.Primes) (t : ℝ) : ℝ :=
  xiPhysicalPrimeLogCumulativeMass P t - t

/-- Two-endpoint discrepancy coboundary seen by the moving physical window. -/
def xiPhysicalPrimeLogMertensCoboundary
    (P : Finset Nat.Primes) (m k u : ℝ) : ℝ :=
  xiPhysicalPrimeLogCumulativeMertensDiscrepancy P (k - u) -
    xiPhysicalPrimeLogCumulativeMertensDiscrepancy P (m - u)

/-- Difference of cumulative physical prime-log masses is the exact moving-window flux. -/
theorem xiPhysicalPrimeLogCumulativeMass_sub_eq_windowFlux
    (P : Finset Nat.Primes) {m k : ℝ} (hmk : m ≤ k) (u : ℝ) :
    xiPhysicalPrimeLogCumulativeMass P (k - u) -
        xiPhysicalPrimeLogCumulativeMass P (m - u) =
      xiPhysicalPrimeLogWindowFlux P m k u := by
  rw [xiPhysicalPrimeLogCumulativeMass, xiPhysicalPrimeLogCumulativeMass,
    xiPhysicalPrimeLogWindowFlux_eq_sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : Real.log (p : ℝ) ≤ k - u
  · by_cases hm : Real.log (p : ℝ) ≤ m - u
    · simp [hk, hm, not_lt_of_ge hm]
    · have hmlt : m - u < Real.log (p : ℝ) := lt_of_not_ge hm
      simp [hk, hm, hmlt]
  · have hm : ¬ Real.log (p : ℝ) ≤ m - u := by
      intro hm
      apply hk
      linarith
    simp [hk, hm]

/-- Exact Mertens coboundary law for raw physical prime-log flux. -/
theorem xiPhysicalPrimeLogWindowFlux_eq_width_add_mertensCoboundary
    (P : Finset Nat.Primes) {m k : ℝ} (hmk : m ≤ k) (u : ℝ) :
    xiPhysicalPrimeLogWindowFlux P m k u =
      (k - m) + xiPhysicalPrimeLogMertensCoboundary P m k u := by
  rw [xiPhysicalPrimeLogMertensCoboundary,
    xiPhysicalPrimeLogCumulativeMertensDiscrepancy,
    xiPhysicalPrimeLogCumulativeMertensDiscrepancy,
    ← xiPhysicalPrimeLogCumulativeMass_sub_eq_windowFlux P hmk u]
  ring

/-- Scalar representative of coherently centered aperture carrier on `(0,A]`. -/
def xiPhysicalPrimeLogCenteredWindowFlux
    (P : Finset Nat.Primes) (A m k u : ℝ) : ℝ :=
  xiPhysicalPrimeLogWindowFlux P m k u -
    xiPhysicalPrimeLogApertureWeightedLengthMass P A m k / A

/-- Coherent centered flux is exactly centered Mertens coboundary. -/
theorem xiPhysicalPrimeLogCenteredWindowFlux_eq_centered_mertensCoboundary
    (P : Finset Nat.Primes) (A : ℝ) {m k : ℝ} (hmk : m ≤ k) (u : ℝ) :
    xiPhysicalPrimeLogCenteredWindowFlux P A m k u =
      xiPhysicalPrimeLogMertensCoboundary P m k u -
        (xiPhysicalPrimeLogApertureWeightedLengthMass P A m k / A - (k - m)) := by
  rw [xiPhysicalPrimeLogCenteredWindowFlux,
    xiPhysicalPrimeLogWindowFlux_eq_width_add_mertensCoboundary P hmk]
  ring

/-- Inside physical aperture, clipped prime interval membership is raw moving-window membership. -/
theorem mem_xiPhysicalPrimeLogApertureSet_iff_window
    (A m k : ℝ) (p : Nat.Primes) {u : ℝ} (hu : u ∈ Ioc 0 A) :
    u ∈ xiPhysicalPrimeLogApertureSet A m k p ↔
      m - u < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ k - u := by
  rw [xiPhysicalPrimeLogApertureSet, mem_Ioc,
    xiPhysicalPrimeLogApertureStart, xiPhysicalPrimeLogApertureEnd]
  constructor
  · intro h
    constructor
    · have := lt_of_le_of_lt (le_max_right 0 (m - Real.log (p : ℝ))) h.1
      linarith
    · have := h.2.trans (min_le_right A (k - Real.log (p : ℝ)))
      linarith
  · intro h
    exact ⟨max_lt hu.1 (by linarith), le_min hu.2 (by linarith)⟩

/-- Almost-everywhere scalar representative of one complex centered carrier. -/
theorem xiPhysicalPrimeLogComplexCenteredApertureCarrier_coeFn_eq
    (A m k : ℝ) (p : Nat.Primes) :
    ∀ᵐ u : ℝ ∂volume, u ∈ Ioc 0 A →
      (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p : ℝ → ℂ) u =
        (xiPhysicalPrimeLogWindowIndicator m k p u -
          xiPhysicalPrimeLogApertureLength A m k p / A : ℝ) := by
  filter_upwards [Lp.coeFn_sub
      (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
      (((xiPhysicalPrimeLogApertureLength A m k p / A : ℝ) : ℂ) •
        xiPhysicalLogComplexApertureIndicator A),
    Lp.coeFn_smul
      ((xiPhysicalPrimeLogApertureLength A m k p / A : ℝ) : ℂ)
      (xiPhysicalLogComplexApertureIndicator A),
    indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (s := xiPhysicalPrimeLogApertureSet A m k p) (hs := measurableSet_Ioc)
      (hμs := measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (s := xiPhysicalLogApertureSet A) (hs := measurableSet_Ioc)
      (hμs := measure_xiPhysicalLogApertureSet_ne_top A) (c := (1 : ℂ))]
      with u hsub hsmul hprime haperture
  intro hu
  have huA : u ∈ xiPhysicalLogApertureSet A := hu
  rw [xiPhysicalPrimeLogComplexCenteredApertureCarrier, hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [xiPhysicalPrimeLogComplexApertureIndicator, hprime,
    xiPhysicalLogComplexApertureIndicator, haperture,
    indicator_of_mem huA]
  by_cases hp : u ∈ xiPhysicalPrimeLogApertureSet A m k p
  · rw [indicator_of_mem hp, xiPhysicalPrimeLogWindowIndicator_eq_if,
      if_pos ((mem_xiPhysicalPrimeLogApertureSet_iff_window A m k p hu).mp hp)]
    norm_cast
    ring
  · rw [indicator_of_notMem hp, xiPhysicalPrimeLogWindowIndicator_eq_if,
      if_neg (mt (mem_xiPhysicalPrimeLogApertureSet_iff_window A m k p hu).mpr hp)]
    norm_cast
    ring

/-- Almost-everywhere scalar representative of complete complex aggregate carrier. -/
theorem xiPhysicalPrimeLogComplexAggregateApertureCarrier_coeFn_eq
    (P : Finset Nat.Primes) (A m k : ℝ) :
    ∀ᵐ u : ℝ ∂volume, u ∈ Ioc 0 A →
      (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k : ℝ → ℂ) u =
        (xiPhysicalPrimeLogCenteredWindowFlux P A m k u : ℂ) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [xiPhysicalPrimeLogComplexAggregateApertureCarrier,
        xiPhysicalPrimeLogCenteredWindowFlux, xiPhysicalPrimeLogWindowFlux,
        xiPhysicalPrimeLogApertureWeightedLengthMass]
  | @insert p P hp ih =>
      rw [xiPhysicalPrimeLogComplexAggregateApertureCarrier, Finset.sum_insert hp]
      filter_upwards [Lp.coeFn_add
          ((physicalPrimeEndpointWeight p : ℂ) •
            xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p)
          (∑ q ∈ P, (physicalPrimeEndpointWeight q : ℂ) •
            xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k q),
        Lp.coeFn_smul (physicalPrimeEndpointWeight p : ℂ)
          (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p),
        xiPhysicalPrimeLogComplexCenteredApertureCarrier_coeFn_eq A m k p,
        ih] with u hadd hsmul hpcoe hPcoe
      intro hu
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      change (physicalPrimeEndpointWeight p : ℂ) *
          (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p : ℝ → ℂ) u +
        (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k : ℝ → ℂ) u = _
      rw [hpcoe hu, hPcoe hu]
      simp [xiPhysicalPrimeLogCenteredWindowFlux,
        xiPhysicalPrimeLogWindowFlux,
        xiPhysicalPrimeLogApertureWeightedLengthMass, hp]
      ring

/-- Fusion energy is exact aperture variance of scalar centered prime-log flux. -/
theorem intervalIntegral_sq_xiPhysicalPrimeLogCenteredWindowFlux_eq_energy
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    (∫ u : ℝ in 0..A, xiPhysicalPrimeLogCenteredWindowFlux P A m k u ^ (2 : ℕ)) =
      xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  rw [← intervalIntegral_norm_sq_xiPhysicalPrimeLogComplexAggregateApertureCarrier
    P hA m k]
  apply intervalIntegral.integral_congr_ae
  filter_upwards
      [xiPhysicalPrimeLogComplexAggregateApertureCarrier_coeFn_eq P A m k]
      with u hcoe
  intro hu
  rw [Set.uIoc_of_le hA.le] at hu
  rw [hcoe hu]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  nlinarith [sq_abs (xiPhysicalPrimeLogCenteredWindowFlux P A m k u)]

/-- Exact FCRJ--Mertens bridge: carrier energy is centered variance of a two-endpoint cumulative
Mertens discrepancy coboundary. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_eq_mertensCoboundaryVariance
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    {m k : ℝ} (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k =
      ∫ u : ℝ in 0..A,
        (xiPhysicalPrimeLogMertensCoboundary P m k u -
          (xiPhysicalPrimeLogApertureWeightedLengthMass P A m k / A - (k - m))) ^ (2 : ℕ) := by
  rw [← intervalIntegral_sq_xiPhysicalPrimeLogCenteredWindowFlux_eq_energy P hA m k]
  apply intervalIntegral.integral_congr
  intro u hu
  change xiPhysicalPrimeLogCenteredWindowFlux P A m k u ^ (2 : ℕ) = _
  rw [xiPhysicalPrimeLogCenteredWindowFlux_eq_centered_mertensCoboundary P A hmk]

/-- Fixed-ratio specialization at physical scale `X`: only two-endpoint Mertens discrepancy
increment remains after exact continuum cancellation. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_logScale_eq_mertensCoboundaryVariance
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (X : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    xiPhysicalPrimeLogApertureFusionEnergy P A (Real.log X) (Real.log X + c) =
      ∫ u : ℝ in 0..A,
        (xiPhysicalPrimeLogMertensCoboundary P (Real.log X) (Real.log X + c) u -
          (xiPhysicalPrimeLogApertureWeightedLengthMass
              P A (Real.log X) (Real.log X + c) / A - c)) ^ (2 : ℕ) := by
  simpa only [add_sub_cancel_left] using
    xiPhysicalPrimeLogApertureFusionEnergy_eq_mertensCoboundaryVariance
      P hA (m := Real.log X) (k := Real.log X + c) (by linarith)

/-- Exact fixed-ratio burden equivalence: FCRJ carrier budget is precisely corresponding centered
Mertens-coboundary variance budget. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_logScale_le_iff
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (X : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (B : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A (Real.log X) (Real.log X + c) ≤ B ↔
      (∫ u : ℝ in 0..A,
        (xiPhysicalPrimeLogMertensCoboundary P (Real.log X) (Real.log X + c) u -
          (xiPhysicalPrimeLogApertureWeightedLengthMass
              P A (Real.log X) (Real.log X + c) / A - c)) ^ (2 : ℕ)) ≤ B := by
  rw [xiPhysicalPrimeLogApertureFusionEnergy_logScale_eq_mertensCoboundaryVariance
    P hA X hc]

end

end RHTower
