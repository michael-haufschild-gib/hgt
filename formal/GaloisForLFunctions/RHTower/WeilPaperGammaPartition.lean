import GaloisForLFunctions.RHTower.WeilPaperCauchyPartition
import GaloisForLFunctions.RHTower.WeilPaperGammaDensity

/-!
# Exact discrete energy and contractive recovery for the native Weil phase

The normalized Cauchy partition turns the actual pole-free Gamma energy into
a positive countable decomposition. The discrete total equals the energy at
every width, and all widths share the same L1 recovery error bound.
-/

open Complex Set Filter MeasureTheory Topology
open scoped BigOperators

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

def paperGammaPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) : ℤ → ℝ := paperCauchyPartitionSample (paperGammaOddDensity hW) k

def paperGammaPartitionInteriorProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (x : ℝ) (k : ℕ) : ℤ → ℝ := paperCauchyPartitionSample (paperGammaOddInteriorDensity hW x) k

theorem paperGammaPartitionProfile_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (n : ℤ) : 0 ≤ paperGammaPartitionProfile hW k n :=
  paperCauchyPartitionSample_nonneg (paperGammaOddDensity_nonneg hW) k n

theorem summable_paperGammaPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) : Summable (paperGammaPartitionProfile hW k) :=
  summable_paperCauchyPartitionSample (integrable_paperGammaOddDensity hW)
    (paperGammaOddDensity_nonneg hW) k

/-- Every width yields exactly the same actual pole-free energy. -/
theorem tsum_paperGammaPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) :
    (∑' n : ℤ, paperGammaPartitionProfile hW k n) =
      paperGammaEnergy (paperGammaOdd (remainderTrace hW)) :=
  tsum_paperCauchyPartitionSample (integrable_paperGammaOddDensity hW)
    (paperGammaOddDensity_nonneg hW) k

/-- Exact discrete version of the actual even/odd energy decomposition. -/
theorem paperGammaPartitionProfile_energy_decomposition {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) :
    paperGammaEnergy (paperGammaEven (remainderTrace hW)) +
      (∑' n : ℤ, paperGammaPartitionProfile hW k n) = paperGammaEnergy (remainderTrace hW) := by
  rw [tsum_paperGammaPartitionProfile]
  exact paperGammaEnergy_decomposition (integrable_remainderTrace hW)
    (integrable_paperGamma_remainderTrace_norm_sq hW)

theorem tsum_paperGammaPartitionProfile_eq_zero_iff {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) :
    (∑' n : ℤ, paperGammaPartitionProfile hW k n) = 0 ↔
      ∀ᵐ y : ℝ, remainderTrace hW y / paperPoleGamma y =
        remainderTrace hW (-y) / paperPoleGamma (-y) := by
  rw [tsum_paperGammaPartitionProfile, paperGammaEnergy_native_eq_zero_iff]

/-- No amplification: discrete profile error is at most native density error. -/
theorem tsum_abs_paperGammaPartitionProfile_error_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    (∑' n : ℤ, |paperGammaPartitionInteriorProfile hW x k n -
      paperGammaPartitionProfile hW k n|) ≤
        ∫ y, |paperGammaOddInteriorDensity hW x y - paperGammaOddDensity hW y| :=
  tsum_abs_paperCauchyPartitionSample_sub_le (integrable_paperGammaOddInteriorDensity hW hx hx1)
    (integrable_paperGammaOddDensity hW) k

/-- Recovery is simultaneous over every width and all integer sites, with constant one. -/
theorem eventually_uniform_paperGammaPartitionProfile_recovery {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ k : ℕ,
      (∑' n : ℤ, |paperGammaPartitionInteriorProfile hW x k n -
        paperGammaPartitionProfile hW k n|) < ε := by
  filter_upwards [(tendsto_integral_abs_paperGammaOddDensity_sub hW).eventually
      (eventually_lt_nhds hε), self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x hsmall (hx : 0 < x) hx1
  exact fun k => (tsum_abs_paperGammaPartitionProfile_error_le hW hx hx1.le k).trans_lt hsmall

end RHTower.WeilWorkSettledPhase
