import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedCurvatureMeasure
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCompletedCoherentBarycenter

/-!
# First-moment landing of Suzuki signed curvature in the unit-Riesz source

The incoming CCM-UR/HG coherent source and the CCM-FU checkpoint source are not independent
arithmetic objects.  At the central boundary readout, the literal square-root-weighted
prime-minus-polar discrepancy is exactly the first moment of Suzuki's signed curvature cells,
plus one source-free archimedean renormalization.

Crucially, this landing occurs before the quadratic actual-head damping that makes the Route-O
matched lift absolutely summable.  Multiplication by the event label cancels the critical Mellin
half-density and recovers the square-root-weighted von Mangoldt mass.  Thus the cofinal growth
discarded by the matched O receiver survives in the UR/HG incoming channel as a signed first
moment.  No prime or archimedean estimate, PNT input, zero-location statement, or RH hypothesis is
used.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set
open GaloisForLFunctions.RHTower
open scoped Interval

/-- First event-label moment of Suzuki's signed prime--archimedean curvature cells. -/
def suzukiCheckpointWeightedSignedCurvaturePrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
    suzukiCheckpointSignedCurvatureCell (k - 1)

/-- Source-free difference between the unit-Riesz `2/3` polar profile and the right-endpoint
first moment of Suzuki's smooth curvature.  The isolated `k = 2` term matches the strict central
event cutoff. -/
def suzukiCheckpointWeightedArchRenormalization (N : ℕ) : ℝ :=
  (2 / 3 : ℝ) * (N + 2 : ℕ) * Real.sqrt (N + 2 : ℕ) -
    ArithmeticFunction.vonMangoldt 2 * Real.sqrt 2 -
    ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t)

/-- At central incoming time, the strict causal prefix consists exactly of events below the
aperture. -/
theorem unitRieszSqrtWeightedPrimePrefix_zero
    {N : ℕ} (hN : 1 ≤ N) :
    unitRieszSqrtWeightedPrimePrefix (N + 2) 0 =
      ∑ k ∈ Finset.Ico 2 (N + 2),
        ArithmeticFunction.vonMangoldt k * Real.sqrt k := by
  rw [unitRieszSqrtWeightedPrimePrefix]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, NNReal.coe_zero]
  constructor
  · rintro ⟨⟨hk2, hkX⟩, hlog⟩
    refine ⟨hk2, ?_⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
    have hXpos : (0 : ℝ) < (N + 2 : ℕ) := by positivity
    have hlt : Real.log (k : ℝ) < Real.log (N + 2 : ℕ) := by linarith
    exact_mod_cast ((Real.strictMonoOn_log.lt_iff_lt hkpos hXpos).mp hlt)
  · rintro ⟨hk2, hkX⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
    have hXpos : (0 : ℝ) < (N + 2 : ℕ) := by positivity
    have hltR : (k : ℝ) < (N + 2 : ℕ) := by exact_mod_cast hkX
    have hlog : Real.log (k : ℝ) < Real.log (N + 2 : ℕ) :=
      (Real.strictMonoOn_log.lt_iff_lt hkpos hXpos).mpr hltR
    exact ⟨⟨hk2, hkX.le⟩, sub_pos.mpr hlog⟩

/-- Multiplication by the event label removes the critical Mellin half-density. -/
theorem criticalMellinAtomWeight_mul_natCast_eq_vonMangoldt_mul_sqrt
    {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * criticalMellinAtomWeight k =
      ArithmeticFunction.vonMangoldt k * Real.sqrt k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [criticalMellinAtomWeight]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hkR.le, ← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  have hsqrtNe : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hkR)
  field_simp
  rw [hsqrt]

/-- Exact CCM-FU-to-UR/HG source landing.  The central coherent prime-minus-polar vector is the
signed Suzuki curvature first moment plus the source-free archimedean renormalization. -/
theorem unitRiesz_center_eq_weightedSignedCurvature_add_arch
    {N : ℕ} (hN : 1 ≤ N) :
    ((N + 2 : ℕ) : ℝ) *
        unitRieszCompletedCoherentBarycenter (N + 2) 0 =
      suzukiCheckpointWeightedSignedCurvaturePrefix N +
        suzukiCheckpointWeightedArchRenormalization N := by
  have hXpos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  have hcenter := unitRieszCompletedCoherentBarycenter_eq_incoming_weightedPrefix N 0
  simp only [NNReal.coe_zero, neg_zero, Real.exp_zero, zero_div, one_div] at hcenter
  have hprefix := unitRieszSqrtWeightedPrimePrefix_zero hN
  rw [hprefix] at hcenter
  have hsplit :
      (∑ k ∈ Finset.Ico 2 (N + 2),
          ArithmeticFunction.vonMangoldt k * Real.sqrt k) =
        ArithmeticFunction.vonMangoldt 2 * Real.sqrt 2 +
          ∑ k ∈ Finset.Ico 3 (N + 2),
            ArithmeticFunction.vonMangoldt k * Real.sqrt k := by
    have h3X : 3 ≤ N + 2 := by omega
    have hsum := Finset.sum_Ico_consecutive
      (fun k : ℕ => ArithmeticFunction.vonMangoldt k * Real.sqrt k)
      (show 2 ≤ 3 by omega) h3X
    simpa using hsum.symm
  rw [hsplit] at hcenter
  have hcells :
      suzukiCheckpointWeightedSignedCurvaturePrefix N =
        (∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            screwRegularKernel t)) -
        ∑ k ∈ Finset.Ico 3 (N + 2),
          ArithmeticFunction.vonMangoldt k * Real.sqrt k := by
    rw [suzukiCheckpointWeightedSignedCurvaturePrefix, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
    have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
    rw [suzukiCheckpointSignedCurvatureCell, hsucc]
    calc
      (k : ℝ) *
          ((∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
              screwRegularKernel t) - criticalMellinAtomWeight k) =
        (k : ℝ) *
            (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
              screwRegularKernel t) -
          (k : ℝ) * criticalMellinAtomWeight k := by ring
      _ = _ := by
        rw [criticalMellinAtomWeight_mul_natCast_eq_vonMangoldt_mul_sqrt
          (by omega : 0 < k)]
  rw [hcells]
  unfold suzukiCheckpointWeightedArchRenormalization
  rw [hcenter]
  field_simp [hXpos.ne']
  ring

/-- Natural normalization of the surviving signed first moment. -/
def suzukiCheckpointNormalizedSignedCurvatureFirstMoment (N : ℕ) : ℝ :=
  suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 2 : ℕ)

/-- Normalized form of the source landing.  Any asymptotic UR/HG central-source theorem can now be
stated directly as an order theorem for Suzuki's signed first moment after subtracting only an
explicit source-free term. -/
theorem normalizedSignedCurvatureFirstMoment_eq_unitRieszCenter_sub_arch
    {N : ℕ} (hN : 1 ≤ N) :
    suzukiCheckpointNormalizedSignedCurvatureFirstMoment N =
      unitRieszCompletedCoherentBarycenter (N + 2) 0 -
        suzukiCheckpointWeightedArchRenormalization N / (N + 2 : ℕ) := by
  have hXne : (((N + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [suzukiCheckpointNormalizedSignedCurvatureFirstMoment]
  have hbridge := unitRiesz_center_eq_weightedSignedCurvature_add_arch hN
  field_simp [hXne]
  linarith

end RHTower
