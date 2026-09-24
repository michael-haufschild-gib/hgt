import GaloisForLFunctions.RHTower.EulerDeletionHighClockLayerTail
import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingaleL2Limit

/-!
# Whole-source four-logarithm clock localization

The source is approximated at one clock, so its prediction errors are summed
before squaring. This removes the extra number-of-layers factor in the older
layerwise high-clock estimate. The martingale correction is square-summable;
the genuinely unresolved field is the signed conditional source below this
smaller clock.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology

namespace RHTower.DeletionResidueMartingale

def fourLogClockThreshold (N : ℕ) : ℕ :=
  4 * (Nat.log2 (N + 1) + 1)

theorem source_fourLogClockProjection_error_norm_sq_le (N : ℕ) :
    ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N -
      (historySpace (fourLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) ≤
      9 / ((N : ℝ) + 1) := by
  let M := N + 1
  let H := Nat.log2 M + 1
  let K := fourLogClockThreshold N
  have hMposNat : 1 ≤ M := by dsimp [M]; omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hNleM : (N : ℝ) ≤ M := by dsimp [M]; push_cast; linarith
  have hKdef : K = 4 * H := rfl
  have hMlt : M < 2 ^ H := by
    dsimp [H]
    exact Nat.lt_log2_self
  have hMpowNat : M ^ 4 ≤ 2 ^ K := by
    calc
      M ^ 4 ≤ (2 ^ H) ^ 4 := by gcongr
      _ = 2 ^ K := by rw [← pow_mul, hKdef]; congr 1; omega
  have hKboundNat : K + 1 ≤ 9 * M := by
    have hlog := Nat.log2_le_self (N + 1)
    change 4 * (Nat.log2 (N + 1) + 1) + 1 ≤ 9 * (N + 1)
    omega
  have hKbound : ((K : ℝ) + 1) ≤ 9 * (M : ℝ) := by
    exact_mod_cast hKboundNat
  have hclockNat : M ^ 4 ≤ (K + 1) * clock K :=
    hMpowNat.trans (two_pow_le_mul_clock K)
  have hclock : (M : ℝ) ^ 4 ≤ ((K : ℝ) + 1) * (clock K : ℝ) := by
    exact_mod_cast hclockNat
  have hMthree : (M : ℝ) ^ 3 ≤ 9 * (clock K : ℝ) := by
    apply (mul_le_mul_iff_left₀ hMpos).mp
    calc
      (M : ℝ) ^ 3 * (M : ℝ) = (M : ℝ) ^ 4 := by ring
      _ ≤ ((K : ℝ) + 1) * (clock K : ℝ) := hclock
      _ ≤ (9 * (M : ℝ)) * (clock K : ℝ) :=
        mul_le_mul_of_nonneg_right hKbound (by positivity)
      _ = (9 * (clock K : ℝ)) * (M : ℝ) := by ring
  have hN2 : (N : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) N) hMpos.le).mpr hNleM
  have hcross : (N : ℝ) ^ 2 * (M : ℝ) ≤
      9 * ((clock K : ℝ) + 1) := by
    calc
      _ ≤ (M : ℝ) ^ 2 * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hN2 hMpos.le
      _ = (M : ℝ) ^ 3 := by ring
      _ ≤ 9 * (clock K : ℝ) := hMthree
      _ ≤ 9 * ((clock K : ℝ) + 1) := by linarith
  have hsource := source_sub_historyProjection_energy_le_clock_tail
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
    (fun n => by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))) N K
  change _ ≤ 9 / ((N : ℝ) + 1)
  calc
    _ ≤ (N : ℝ) ^ 2 / ((clock K : ℝ) + 1) := hsource
    _ ≤ 9 / (M : ℝ) :=
      (div_le_div_iff₀ (by positivity : (0 : ℝ) < (clock K : ℝ) + 1) hMpos).mpr hcross
    _ = 9 / ((N : ℝ) + 1) := by simp [M]

end RHTower.DeletionResidueMartingale
