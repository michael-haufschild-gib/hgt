import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeOutgoingDilationFlux
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalSignedCompensationSaturation

/-!
# Completed quarter-dilation balance for the SP-E outgoing charge

The prime outgoing charge changes through a global history-wide quarter-dilation
gain-minus-debt balance. Completing it introduces no free channel: it subtracts
the exact continuum increment `(sqrt (N + 1) - sqrt N) / 3`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Topology

/-- **Exact completed SP-E aperture balance.** The one-step completed outgoing charge is the
global quarter-dilation prime gain minus debt, corrected by the literal continuum increment. -/
theorem unitRieszCoherentCompletedOutgoingCharge_succ_sub_eq_quarterDilationBalance
    {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentCompletedOutgoingCharge (N + 1) -
        unitRieszCoherentCompletedOutgoingCharge N =
      unitRieszCoherentOutgoingQuarterDilationGain N -
        unitRieszCoherentOutgoingQuarterDilationDebt N -
          (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) / 3 := by
  simp only [unitRieszCoherentCompletedOutgoingCharge,
    unitRieszCoherentPolarOutgoingCharge_eq]
  linarith [unitRieszCoherentPrimeOutgoingCharge_succ_sub_eq_quarterDilationGain_sub_debt hN]

/-- The complete finite SP-E history is exactly its cumulative prime-continuum dilation
imbalance.  This identifies the nonlocal quantity that must be improved from sub-root control
to bounded control. -/
theorem sum_quarterDilationBalance_eq_completedOutgoingCharge_sub
    {N : ℕ} (hN : 2 ≤ N) :
    Finset.sum (Finset.Ico 2 N) (fun j =>
      unitRieszCoherentOutgoingQuarterDilationGain j -
        unitRieszCoherentOutgoingQuarterDilationDebt j -
          (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) / 3) =
      unitRieszCoherentCompletedOutgoingCharge N -
        unitRieszCoherentCompletedOutgoingCharge 2 := by
  calc
    Finset.sum (Finset.Ico 2 N) (fun j =>
      unitRieszCoherentOutgoingQuarterDilationGain j -
        unitRieszCoherentOutgoingQuarterDilationDebt j -
          (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) / 3) =
        Finset.sum (Finset.Ico 2 N) (fun j =>
          unitRieszCoherentCompletedOutgoingCharge (j + 1) -
            unitRieszCoherentCompletedOutgoingCharge j) := by
      refine Finset.sum_congr
        (s₁ := Finset.Ico 2 N) (s₂ := Finset.Ico 2 N)
        (f := fun j : ℕ =>
          unitRieszCoherentOutgoingQuarterDilationGain j -
            unitRieszCoherentOutgoingQuarterDilationDebt j -
              (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) / 3)
        (g := fun j : ℕ =>
          unitRieszCoherentCompletedOutgoingCharge (j + 1) -
            unitRieszCoherentCompletedOutgoingCharge j) rfl fun j hj => ?_
      exact (unitRieszCoherentCompletedOutgoingCharge_succ_sub_eq_quarterDilationBalance
        (Finset.mem_Ico.mp hj).1).symm
    _ = unitRieszCoherentCompletedOutgoingCharge N -
          unitRieszCoherentCompletedOutgoingCharge 2 := by
      rw [Finset.sum_Ico_eq_sub _ hN,
        Finset.sum_range_sub, Finset.sum_range_sub]
      ring

/-- **Unconditional sub-root global cancellation.**  The cumulative literal SP-E
prime-continuum imbalance is `o(sqrt N)`.  This is the strongest source cancellation presently
obtained without the RH-equivalent boundedness upgrade. -/
theorem tendsto_sum_quarterDilationBalance_div_sqrt_atTop_zero :
    Tendsto (fun N : ℕ =>
      Finset.sum (Finset.Ico 2 N) (fun j =>
        unitRieszCoherentOutgoingQuarterDilationGain j -
          unitRieszCoherentOutgoingQuarterDilationDebt j -
            (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) / 3) /
        Real.sqrt (N : ℝ)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst : Tendsto (fun N : ℕ =>
      unitRieszCoherentCompletedOutgoingCharge 2 / Real.sqrt (N : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hsqrt
  have hlimit :=
    tendsto_unitRieszCoherentCompletedOutgoingCharge_div_sqrt_atTop_zero.sub hconst
  have hlimit0 : Tendsto (fun N : ℕ =>
      unitRieszCoherentCompletedOutgoingCharge N / Real.sqrt (N : ℝ) -
        unitRieszCoherentCompletedOutgoingCharge 2 / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit0.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  rw [sum_quarterDilationBalance_eq_completedOutgoingCharge_sub hN]
  ring

/-- Uniform boundedness of the exact cumulative quarter-dilation imbalance. -/
def CompletedQuarterDilationBalanceBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 2 ≤ N →
    abs (Finset.sum (Finset.Ico 2 N) (fun j =>
      unitRieszCoherentOutgoingQuarterDilationGain j -
        unitRieszCoherentOutgoingQuarterDilationDebt j -
          (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) / 3)) ≤ B

/-- **Sharp SP-E dynamic boundary.**  Upgrading the unconditional sub-root cancellation of the
literal quarter-dilation imbalance to uniform boundedness is equivalent to RH. -/
theorem riemannHypothesis_iff_completedQuarterDilationBalanceBounded :
    RiemannHypothesis ↔ CompletedQuarterDilationBalanceBounded := by
  constructor
  · intro hRH
    obtain ⟨B, hB, hres⟩ :=
      RHTower.riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mp hRH
    refine ⟨B + |unitRieszCoherentCompletedOutgoingCharge 2|, by positivity, ?_⟩
    intro N hN
    rw [sum_quarterDilationBalance_eq_completedOutgoingCharge_sub hN]
    have hcharge : |unitRieszCoherentCompletedOutgoingCharge N| ≤ B := by
      rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        |RHTower.criticalMellinChebyshevResolventSource (Real.log N)| / 2 ≤ B / 2 :=
          div_le_div_of_nonneg_right (hres N hN) (by norm_num)
        _ ≤ B := by linarith
    exact (abs_sub _ _).trans (add_le_add hcharge le_rfl)
  · rintro ⟨B, _hB, hbalance⟩
    apply riemannHypothesis_of_criticalMellinChebyshevResolventSource_log_nat_bound
      (B₀ := 2 * (B + |unitRieszCoherentCompletedOutgoingCharge 2|))
    intro N hN
    have hdiff : |unitRieszCoherentCompletedOutgoingCharge N -
        unitRieszCoherentCompletedOutgoingCharge 2| ≤ B := by
      rw [← sum_quarterDilationBalance_eq_completedOutgoingCharge_sub hN]
      exact hbalance N hN
    have hcharge : |unitRieszCoherentCompletedOutgoingCharge N| ≤
        B + |unitRieszCoherentCompletedOutgoingCharge 2| := by
      have hrewrite : unitRieszCoherentCompletedOutgoingCharge N =
          (unitRieszCoherentCompletedOutgoingCharge N -
            unitRieszCoherentCompletedOutgoingCharge 2) +
              unitRieszCoherentCompletedOutgoingCharge 2 := by ring
      rw [hrewrite]
      exact (abs_add_le _ _).trans (add_le_add hdiff le_rfl)
    have hres : RHTower.criticalMellinChebyshevResolventSource (Real.log N) =
        2 * unitRieszCoherentCompletedOutgoingCharge N := by
      rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN]
      ring
    rw [hres, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hcharge (by norm_num)

end

end GaloisForLFunctions.RHTower
