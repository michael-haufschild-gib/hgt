import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPrimePhysicalEnergy
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecificLimits.Normed

/-!
The literal Euler-deletion clock dominates an exponential via the lcmUpto theorem.
This makes every fixed polynomial-to-clock quotient vanish cofinally.
-/

set_option autoImplicit false
open Finset Filter Topology
namespace RHTower.DeletionResidueMartingale

theorem lcmUpto_dvd_clock (L : ℕ) : Nat.lcmUpto L ∣ clock L := by
  unfold Nat.lcmUpto clock
  apply Finset.lcm_dvd
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  have hi : k - 1 ∈ range L := Finset.mem_range.mpr (by omega)
  simpa [Nat.sub_add_cancel hkBounds.1] using
    (Finset.dvd_lcm (f := fun i : ℕ => i + 1) hi)

theorem two_pow_le_mul_clock (L : ℕ) : 2 ^ L ≤ (L + 1) * clock L := by
  have hle : Nat.lcmUpto L ≤ clock L :=
    Nat.le_of_dvd (clock_pos L) (lcmUpto_dvd_clock L)
  exact (Chebyshev.two_pow_le_mul_lcmUpto L).trans (Nat.mul_le_mul_left (L + 1) hle)

theorem tendsto_sq_div_clock_zero :
    Tendsto (fun L : ℕ => (L : ℝ) ^ 2 / (clock L : ℝ)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun L : ℕ => (L : ℝ) ^ 3 / (2 : ℝ) ^ L) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num)
  have h2 : Tendsto (fun L : ℕ => (L : ℝ) ^ 2 / (2 : ℝ) ^ L) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hmaj : Tendsto
      (fun L : ℕ => ((L : ℝ) ^ 3 + (L : ℝ) ^ 2) / (2 : ℝ) ^ L)
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using h3.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
  · exact Filter.Eventually.of_forall fun L => by positivity
  · exact Filter.Eventually.of_forall fun L => by
      have hC : (0 : ℝ) < clock L := Nat.cast_pos.mpr (clock_pos L)
      have htwo : (0 : ℝ) < (2 : ℝ) ^ L := pow_pos (by norm_num) L
      have hpow : (2 : ℝ) ^ L ≤ ((L : ℝ) + 1) * (clock L : ℝ) := by
        exact_mod_cast two_pow_le_mul_clock L
      apply (div_le_div_iff₀ hC htwo).2
      calc
        (L : ℝ) ^ 2 * (2 : ℝ) ^ L ≤
            (L : ℝ) ^ 2 * (((L : ℝ) + 1) * (clock L : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
        _ = ((L : ℝ) ^ 3 + (L : ℝ) ^ 2) * (clock L : ℝ) := by ring

end RHTower.DeletionResidueMartingale

open MeasureTheory
namespace RHTower.DeletionPrimeWindowPhase

/-- The full upper-half prime correction has vanishing physical energy for every cofinal
    schedule with `L ≤ N(L) ≤ 2L`. -/
theorem upperHalfPhysicalPrimeWindow_energy_tendsto_zero
    (N : ℕ → ℕ) (hlo : ∀ L, L ≤ N L) (hhi : ∀ L, N L ≤ 2 * L) :
    Tendsto
      (fun L : ℕ =>
        ∑ r ∈ range (DeletionResidueMartingale.clock L),
          (∫ x in (0 : ℝ)..1,
            ∑ p ∈ (Icc (L + 1) (N L)).filter Nat.Prime,
              upperHalfPrimePacketKernel (N L) L p r x) ^ 2 /
            DeletionResidueMartingale.cellMeasure.real
              (DeletionResidueMartingale.historyFibre L r))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun L : ℕ => 8 * ((L : ℝ) ^ 2 /
        (DeletionResidueMartingale.clock L : ℝ))) atTop (𝓝 0) := by
    simpa using DeletionResidueMartingale.tendsto_sq_div_clock_zero.const_mul (8 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun L => by
      apply Finset.sum_nonneg
      intro r hr
      have hm := DeletionResidueMartingale.historyFibre_mass_pos L r
        (Finset.mem_range.mp hr)
      exact div_nonneg (sq_nonneg _) hm.le
  · exact Filter.Eventually.of_forall fun L => by
      have hE := upperHalfPhysicalPrimeWindow_fibre_energy_le (N L) L
        (hlo L) (hhi L)
      have hNreal : ((N L : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
        exact_mod_cast hhi L
      have hsq : (N L : ℝ) ^ 2 ≤ (2 * (L : ℝ)) ^ 2 :=
        (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) (N L)) (by positivity)).mpr hNreal
      have hC : (0 : ℝ) ≤ DeletionResidueMartingale.clock L :=
        Nat.cast_nonneg _
      calc
        _ ≤ 2 * (N L : ℝ) ^ 2 /
            (DeletionResidueMartingale.clock L : ℝ) := hE
        _ ≤ 2 * (2 * (L : ℝ)) ^ 2 /
            (DeletionResidueMartingale.clock L : ℝ) := by
          apply div_le_div_of_nonneg_right _ hC
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = 8 * ((L : ℝ) ^ 2 /
            (DeletionResidueMartingale.clock L : ℝ)) := by ring

end RHTower.DeletionPrimeWindowPhase
