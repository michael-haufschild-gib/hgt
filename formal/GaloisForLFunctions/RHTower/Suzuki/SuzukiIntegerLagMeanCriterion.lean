import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilLagTailBridge
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCoherentOutgoingChargeHankel
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszResolventRHCriterion
import GaloisForLFunctions.RHTower.SPEQuantileRieszSourceTransport

/-!
# Endpoint-corrected signed integer-lag mean for SP-E

The exact source-to-lag Green identity has one moving terminal lag, a signed
interior lag mean, and its fixed endpoint and archimedean corrections.  This
file records their literal combination as one source quantity.  It is exactly
the completed outgoing charge up to the source-free polar lattice correction.

This does not bound the mean.  It identifies the remaining SP-E producer with
an RH-equivalent, cancellation-preserving integer-lag criterion.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- The endpoint-corrected, signed integer-lag mean read by the SP-E Abel source. -/
def coherentSelbergIntegerLagMean (N : ℕ) : ℝ :=
  weilLagTailCellWeight 1 * weilLagChebyshevTail 1 -
    weilLagTailCellWeight (N + 1) *
      (weilLagTailIntegerNumerator (N + 2) / ((N + 2 : ℕ) : ℝ)) +
    ∑ k ∈ Finset.Icc 2 (N + 1),
      (weilLagTailCellWeight k - weilLagTailCellWeight (k - 1)) *
        (weilLagTailIntegerNumerator k / (k : ℝ)) +
    ∑ k ∈ Finset.Icc 1 (N + 1), weilLagTailArchCell k

/-- The exact source-to-lag identification retains both the moving endpoint and signed interior. -/
theorem coherentSelbergSquareRootAbelMoment_eq_integerLagMean (N : ℕ) :
    coherentSelbergSquareRootAbelMoment (N + 2) = coherentSelbergIntegerLagMean N := by
  simpa only [coherentSelbergIntegerLagMean] using
    coherentSelbergSquareRootAbelMoment_eq_integerLag_green N

/-- Completed labelled quantile transport is the endpoint-corrected signed integer-lag current
exactly. The equality retains the terminal seam, lower edge, moving endpoint, signed interior,
and polar lattice term; no absolute-value surrogate enters. -/
theorem speCompletedQuantileRieszTransport_eq_two_mul_integerLagMean_add_polar (N : ℕ) :
    speCompletedQuantileRieszTransport (N + 2) =
      2 * (coherentSelbergIntegerLagMean N +
        coherentSquareRootPolarLatticeDefect (N + 2)) := by
  calc
    speCompletedQuantileRieszTransport (N + 2) =
        ((N + 2 : ℕ) : ℝ) *
          criticalMellinChebyshevResolventSource (Real.log ((N + 2 : ℕ) : ℝ)) :=
      speCompletedQuantileRieszTransport_eq_resolvent_source (by omega : 2 ≤ N + 2)
    _ = 2 * (((N + 2 : ℕ) : ℝ) *
          unitRieszCoherentCompletedOutgoingCharge (N + 2)) := by
      rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half
        (by omega : 2 ≤ N + 2)]
      ring
    _ = 2 * (coherentSelbergSquareRootAbelMoment (N + 2) +
          coherentSquareRootPolarLatticeDefect (N + 2)) := by
      rw [coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect (by omega : 2 ≤ N + 2)]
    _ = 2 * (coherentSelbergIntegerLagMean N +
          coherentSquareRootPolarLatticeDefect (N + 2)) := by
      rw [coherentSelbergSquareRootAbelMoment_eq_integerLagMean]

/-- The completed outgoing charge is the endpoint-corrected signed lag mean plus only its
source-free polar lattice correction. -/
theorem unitRieszCoherentCompletedOutgoingCharge_eq_integerLagMean (N : ℕ) :
    GaloisForLFunctions.RHTower.unitRieszCoherentCompletedOutgoingCharge (N + 2) =
      (coherentSelbergIntegerLagMean N + coherentSquareRootPolarLatticeDefect (N + 2)) /
        ((N + 2 : ℕ) : ℝ) := by
  rw [coherentCompletedOutgoing_eq_abel_add_latticeDefect_div (by omega : 2 ≤ N + 2),
    coherentSelbergSquareRootAbelMoment_eq_integerLagMean]

/-- A uniform bound on the literal signed lag mean transfers with an explicit constant to every
integer-logarithmic critical-Mellin resolvent sample.  The only loss is the source-free polar
lattice defect. -/
theorem abs_criticalMellinChebyshevResolventSource_log_nat_le_of_integerLagMeanBound
    {B : ℝ}
    (hmean : ∀ N : ℕ,
      |coherentSelbergIntegerLagMean N / ((N + 2 : ℕ) : ℝ)| ≤ B)
    {M : ℕ} (hM : 2 ≤ M) :
    |criticalMellinChebyshevResolventSource (Real.log M)| ≤ 2 * (B + 1) := by
  have hMpos : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hmeanM := hmean (M - 2)
  have hshift : M - 2 + 2 = M := by omega
  rw [hshift] at hmeanM
  have hdef : |coherentSquareRootPolarLatticeDefect M / (M : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hMpos]
    calc
      |coherentSquareRootPolarLatticeDefect M| / (M : ℝ) ≤ Real.sqrt M / M :=
        div_le_div_of_nonneg_right
          (abs_coherentSquareRootPolarLatticeDefect_le (by omega : 1 ≤ M)) hMpos.le
      _ ≤ 1 := by
        apply (div_le_one hMpos).2
        apply (Real.sqrt_le_left hMpos.le).mpr
        calc
          (M : ℝ) = 1 * M := (one_mul _).symm
          _ ≤ M * M := mul_le_mul_of_nonneg_right hMone hMpos.le
          _ = (M : ℝ) ^ (2 : ℕ) := (pow_two _).symm
  have hcharge := coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM
  rw [← hshift, coherentSelbergSquareRootAbelMoment_eq_integerLagMean, add_div] at hcharge
  have hchargeM : unitRieszCoherentCompletedOutgoingCharge M =
      coherentSelbergIntegerLagMean (M - 2) / (M : ℝ) +
        coherentSquareRootPolarLatticeDefect M / M := by
    simpa only [hshift] using hcharge
  have hres : criticalMellinChebyshevResolventSource (Real.log M) =
      2 * unitRieszCoherentCompletedOutgoingCharge M := by
    linarith [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM]
  rw [hres, hchargeM, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |coherentSelbergIntegerLagMean (M - 2) / (M : ℝ) +
        coherentSquareRootPolarLatticeDefect M / M| ≤
        2 * (|coherentSelbergIntegerLagMean (M - 2) / (M : ℝ)| +
          |coherentSquareRootPolarLatticeDefect M / M|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ 2 * (B + 1) := by gcongr

/-- Uniform boundedness of the literal endpoint-corrected signed integer-lag mean. -/
def CoherentSelbergIntegerLagMeanBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    |coherentSelbergIntegerLagMean N / ((N + 2 : ℕ) : ℝ)| ≤ B

/-- The exact signed integer-lag mean closes the analytic critical-Mellin endpoint directly.
No positivity replacement is used: the argument preserves the endpoint correction and all
signed interior lag coefficients through the outgoing-charge identity. -/
theorem riemannHypothesis_of_coherentSelbergIntegerLagMeanBounded :
    CoherentSelbergIntegerLagMeanBounded → RiemannHypothesis := by
  rintro ⟨B, _hB, hmean⟩
  apply riemannHypothesis_of_criticalMellinChebyshevResolventSource_log_nat_bound
  intro M hM
  exact abs_criticalMellinChebyshevResolventSource_log_nat_le_of_integerLagMeanBound
    hmean hM

/-- The endpoint-corrected signed integer-lag mean is an exact RH boundary. -/
theorem riemannHypothesis_iff_coherentSelbergIntegerLagMeanBounded :
    RiemannHypothesis ↔ CoherentSelbergIntegerLagMeanBounded := by
  constructor
  · intro hRH
    obtain ⟨B, hB, habel⟩ :=
      riemannHypothesis_iff_coherentSelbergSquareRootAbelBounded.mp hRH
    refine ⟨B, hB, fun N => ?_⟩
    rw [← coherentSelbergSquareRootAbelMoment_eq_integerLagMean]
    exact habel (N + 2) (by omega)
  · exact riemannHypothesis_of_coherentSelbergIntegerLagMeanBounded

end

end RHTower
