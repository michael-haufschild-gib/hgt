import GaloisForLFunctions.RHTower.Sieve.MaynardMultiscaleReferenceTelescope
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceCountNormalization
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceArbitraryOrderLocalization

/-!
# Prime-free composition for the physical Route-T slice

This module supplies quantitative bounds needed to compose the dyadic prime-free defect producer
with arbitrary-order physical-slice localization.  The literal floor envelope and the number of
dyadic rungs each cost only one logarithm.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- The literal floor-truncated physical-slice envelope costs at most one logarithm. -/
theorem routeTPhysicalSliceEnvelope_le_six_log_three_mul
    {N R : ℝ} (hN : 2 ≤ N) (hR : 0 ≤ R) (hRN : R ≤ N) :
    routeTPhysicalSliceEnvelope N R ≤ 6 * Real.log (3 * N) := by
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  have hN0 : 0 ≤ N := by linarith
  have hBarg0 : 0 ≤ N + 2 * R := by linarith
  have hAupper : (A : ℝ) ≤ N := by
    dsimp only [A]
    exact Nat.floor_le hN0
  have hAlower : N - 1 < (A : ℝ) := by
    have h := Nat.lt_floor_add_one N
    dsimp only [A]
    linarith
  have hAone : (1 : ℝ) ≤ A := by linarith
  have hApos : (0 : ℝ) < A := by linarith
  have hBupper : (B : ℝ) ≤ 3 * N := by
    calc
      (B : ℝ) ≤ N + 2 * R := by
        dsimp only [B]
        exact Nat.floor_le hBarg0
      _ ≤ 3 * N := by linarith
  have hBone : (1 : ℝ) ≤ B := by
    have hAB : A ≤ B := by
      dsimp only [A, B]
      exact Nat.floor_mono (by linarith)
    have hAoneNat : 1 ≤ A := by exact_mod_cast hAone
    exact_mod_cast hAoneNat.trans hAB
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hBone
  have hlogB : Real.log B ≤ Real.log (3 * N) :=
    Real.log_le_log (by positivity) hBupper
  have hratio : (B : ℝ) / A ≤ 6 := by
    rw [div_le_iff₀ hApos]
    nlinarith [hBupper, hAlower]
  change (B : ℝ) * (Real.log B / A) ≤ 6 * Real.log (3 * N)
  calc
    (B : ℝ) * (Real.log B / A) = ((B : ℝ) / A) * Real.log B := by ring
    _ ≤ 6 * Real.log B := mul_le_mul_of_nonneg_right hratio hlogB0
    _ ≤ 6 * Real.log (3 * N) := mul_le_mul_of_nonneg_left hlogB (by norm_num)

/-- The endpoint power bracket makes the dyadic telescope loss explicitly logarithmic. -/
theorem routeTComparableWidthLadder_index_le_log
    {H R : ℝ} (hH : 0 < H) (hHR : H ≤ R) {J : ℕ} (hJ : 0 < J)
    (hbelow : (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ R / H) :
    (J : ℝ) ≤ 1 + Real.log (R / H) / Real.log 2 := by
  have hratio : 1 ≤ R / H := by
    exact (le_div_iff₀ hH).2 (by simpa using hHR)
  have hpow0 : (0 : ℝ) < (((2 ^ (J - 1) : ℕ) : ℝ)) := by positivity
  have hlog := Real.log_le_log hpow0 hbelow
  have hJone : 1 ≤ J := by omega
  have hlogpow :
      Real.log (((2 ^ (J - 1) : ℕ) : ℝ)) =
        ((J - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hlog
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : ((J - 1 : ℕ) : ℝ) ≤ Real.log (R / H) / Real.log 2 := by
    exact (le_div_iff₀ hlogtwo).2 (by simpa [mul_comm] using hlog)
  have hJcast : (J : ℝ) = (J - 1 : ℕ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hJone).symm
  rw [hJcast]
  linarith

end RHTower.Sieve
