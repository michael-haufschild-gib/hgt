import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ThermalTransition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import Mathlib.Analysis.Complex.ReImTopology

/-! # Probability-conserving composition is the frontier of bounded thermal losses

Squaring a Gibbs amplitude at parameter s gives power exponent 2 Re(s).
Allowing every finite omitted dimension determines a boundedness region
directly from these costs.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- In the convergence region, the surviving occupations and their relative cost sum to the Gibbs partition. -/
theorem partition_eq_relative_add_surviving {β : GibbsExponent} (hβ : 1 < β.val)
    {r : ℕ} (b : SpectralBand r) :
    (riemannZeta (β.val:ℂ)).re = relativeReading (powerResponse β) b + ∑' n, (b n).val ^ β.val := by
  have he (n : ℕ) : occupationWeight n ^ β.val = shellPower β n := by
    rw [shellPower,occupationWeight_eq,Real.inv_rpow (by positivity),one_div]
  have ha := (hasSum_shellPower hβ).congr_fun he
  have hb : Summable (fun n => (b n).val ^ β.val) :=
    .of_nonneg_of_le (fun n => Real.rpow_nonneg (band_in_unit b n).1 _)
      (fun n => Real.rpow_le_rpow (band_in_unit b n).1 (b n).property.2 β.property.le) ha.summable
  change _ = (∑' n, (occupationWeight n ^ β.val - (b n).val ^ β.val)) + ∑' n, (b n).val ^ β.val
  rw [ha.summable.tsum_sub hb,sub_add_cancel,ha.tsum_eq]

/-- Parameters whose squared Gibbs amplitudes yield a bounded set of finite-omission costs. -/
def boundedOmissionRegion : Set ℂ :=
  {s | ∃ β : GibbsExponent, β.val = 2*s.re ∧ BddAbove (finiteGibbsLosses β)}

theorem boundedOmissionRegion_eq : boundedOmissionRegion = Complex.re ⁻¹' Ioi (1/2:ℝ) := by
  ext s
  constructor
  · rintro ⟨β,hβ,hb⟩
    have h := (finiteGibbsLosses_bounded_iff β).mp hb
    change 1/2 < s.re
    linarith only [h,hβ]
  · intro hs
    change 1/2 < s.re at hs
    let β : GibbsExponent := ⟨2*s.re,by change 0 < 2*s.re; linarith only [hs]⟩
    exact ⟨β,rfl,(finiteGibbsLosses_bounded_iff β).mpr (by change 1 < 2*s.re; linarith only [hs])⟩

/-- The cyclic-order composition is an isometry exactly on the topological frontier of bounded losses. -/
theorem split_isometry_iff_omission_frontier (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔ s ∈ frontier boundedOmissionRegion := by
  simp only [split_isometric_iff,boundedOmissionRegion_eq,Complex.frontier_preimage_re,frontier_Ioi,
    mem_preimage,mem_singleton_iff]

theorem harmonic_range_at_composition_line (r : ℕ) :
    responseAtRank (powerResponse ⟨1,show (0:ℝ) < 1 from zero_lt_one⟩) (r+1) =
      Ioo 0 (∑ n ∈ Finset.range (r+1), ((n:ℝ)+1)⁻¹) := by
  rw [gibbs_range_at_rank,gibbsHead]
  simp only [shellPower,Real.rpow_one,one_div]

#print axioms partition_eq_relative_add_surviving
#print axioms boundedOmissionRegion_eq
#print axioms split_isometry_iff_omission_frontier
#print axioms harmonic_range_at_composition_line

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
