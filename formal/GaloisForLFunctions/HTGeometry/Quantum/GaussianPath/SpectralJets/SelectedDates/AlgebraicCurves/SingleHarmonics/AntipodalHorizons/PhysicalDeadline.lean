import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.FrozenSchedule
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.PhysicalScales

/-! # Two-sided physical first-wait bounds from late spectral antipodes -/

open Set MeasureTheory Filter Real Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open SharpOccupation
noncomputable section

/-- For every prescribed winding schedule above a deterministic cutoff,
the true continuous first empty-circuit wait on a single frozen chain
lies between b^(-D) and 2·2^(D^c) in physical time. -/
theorem gaussian_two_sided_antipodal_first_wait :
    ∃ c : ℕ, ∀ ε ∈ Ioo (0:ℝ) (sqrt 2), ∀ b ∈ Ioo (physicalArc ε) 1,
      ∃ N₀ : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, N₀ k ≤ n k) →
        ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
          let D := 2^(k+3)
          (1/b)^D < elapsed k (n k) ε ω ∧ elapsed k (n k) ε ω ≤ 2*(2:ℝ)^(D^c) := by
  obtain ⟨c,hu⟩ := gaussian_elapsed_upper
  obtain ⟨C,hC,hperiod⟩ := gaussian_periods_per_time
  refine ⟨c,?_⟩
  intro ε hε b hb
  obtain ⟨y,hxy,hyb⟩ := exists_between hb.1
  have hy := (physicalArc_spec hε.1 hε.2).1.1.trans hxy
  have hpos := hy.trans hyb
  obtain ⟨A,hA⟩ := gaussian_frozen_antipodal_wait hε hxy (hyb.trans hb.2)
  refine ⟨A,?_⟩
  intro n hn
  have hdim : Tendsto (fun k : ℕ => 2^(k+3)) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k ≤ k+3 by omega).trans (Nat.lt_two_pow_self (n:=k+3)).le) tendsto_id
  have hrate := hdim.eventually (FirstClockIndex.linear_mul_pow_eventually_lt C (one_div_pos.mpr hpos)
    (one_div_lt_one_div_of_lt hy hyb))
  filter_upwards [hu,hperiod,hA n hn] with ω hupper hP hwait
  filter_upwards [hupper ε hε,hP,hwait,hrate] with k hk hpk hlong hfast
  intro D
  refine ⟨?_,?_⟩
  · by_contra! hshort
    have hkd : ((k+3:ℕ):ℝ) ≤ (D:ℝ)+1 := by
      have h : k+3 ≤ D := (Nat.lt_two_pow_self (n:=k+3)).le
      exact (Nat.cast_le.mpr h).trans (le_add_of_nonneg_right zero_le_one)
    have hshorter : firstPeriods k (n k) ε ω ≤ C*((D:ℝ)+1)*(1/b)^D := calc
      firstPeriods k (n k) ε ω ≤ elapsed k (n k) ε ω*(C*(k+3:ℕ)) := hpk (n k) ε hε.1
      _ ≤ (1/b)^D*(C*(k+3:ℕ)) := mul_le_mul_of_nonneg_right hshort (by positivity)
      _ ≤ (1/b)^D*(C*((D:ℝ)+1)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkd hC.le)
        (pow_nonneg (one_div_nonneg.mpr hpos.le) _)
      _ = _ := mul_comm ..
    exact hlong.not_ge (hshorter.trans hfast.le)
  · exact hk (origin k (n k) ω)

#print axioms gaussian_two_sided_antipodal_first_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
