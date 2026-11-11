import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheHarmonicProfileProductsHaveTheirExpectedLimits
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergFormIsAHarmonicModel

/-!
# The exact shifted principal row in profile coordinates

Factoring the power shift along each dilation identifies the arithmetic
Möbius transform with the normalized smooth profile. The harmonic row
then has one outer dilation factor and one diagonal exponential. The
latter is exactly one at the detector's coupled shift.
-/

open ArithmeticFunction Filter Set Topology
open RHTower.Sieve
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The polynomial mollifier weight with a normalized real power shift. -/
def shiftedProfileWeight (P : ℝ → ℝ) (N : ℕ) (v : ℝ) (n : ℕ) : ℝ :=
  Real.exp (v * Real.log n / Real.log N) * P (1 - Real.log n / Real.log N)

/-- The finite exponential cutoff is the literal integer quotient. -/
theorem shiftedProfile_cutoff {N q : ℕ} (hN : 1 < N) (hq : 0 < q) :
    ⌊Real.exp (Real.log N * (1 - Real.log q / Real.log N))⌋₊ = N / q := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have he : Real.log N * (1 - Real.log q / Real.log N) = Real.log ((N : ℝ) / q) := by
    rw [Real.log_div hNR.ne' hqR.ne']
    field_simp [hlog] <;> ring
  rw [he, Real.exp_log (div_pos hNR hqR), Nat.floor_div_natCast, Nat.floor_natCast]

/-- The normalized arithmetic Möbius row is the smooth profile at its remaining length. -/
theorem selbergMoebiusWeightedSum_shiftedProfile
    (P : ℝ → ℝ) (v : ℝ) {N q : ℕ} (hN : 1 < N) (hq : 0 < q) :
    selbergMoebiusWeightedSum (shiftedProfileWeight P N v) N q =
      Real.exp (v * Real.log q / Real.log N) *
        normalizedShiftedMobiusProfile P (Real.log N) (1 - Real.log q / Real.log N) v / Real.log N := by
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold selbergMoebiusWeightedSum normalizedShiftedMobiusProfile
  rw [shiftedProfile_cutoff hN hq]
  have he (n : ℕ) (hn : n ∈ Finset.Icc 1 (N / q)) :
      selbergMoebiusReciprocalCoeff n * shiftedProfileWeight P N v (q * n) =
      Real.exp (v * Real.log q / Real.log N) *
        (((moebius n : ℤ) : ℝ) / n * Real.exp (v * Real.log n / Real.log N) *
          P ((1 - Real.log q / Real.log N) - Real.log n / Real.log N)) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
    have hg : Real.log ((q * n : ℕ) : ℝ) = Real.log (q : ℝ) + Real.log n := by
      rw [Nat.cast_mul, Real.log_mul hqR hnR]
    have he' : Real.exp (v * (Real.log q + Real.log n) / Real.log N) =
        Real.exp (v * Real.log q / Real.log N) * Real.exp (v * Real.log n / Real.log N) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hp : 1 - (Real.log q + Real.log n) / Real.log N =
        (1 - Real.log q / Real.log N) - Real.log n / Real.log N := by ring
    simp only [selbergMoebiusReciprocalCoeff, shiftedProfileWeight, hg, he', hp]
    ring
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum]
  field_simp [hlog] <;> ring

/-- The two-profile principal row, with both normalized shifts visible. -/
def shiftedProfileHarmonicRow (P Q : ℝ → ℝ) (N a b : ℕ) (c v : ℝ) (k : ℕ) : ℝ :=
  Real.log N * (∑ d ∈ Finset.Icc 1 (N / max a b),
    (Real.log d / Real.log N) ^ k * Real.exp (c * (Real.log d / Real.log N)) *
      (selbergMoebiusWeightedSum (shiftedProfileWeight P N v) N (a * d) *
        selbergMoebiusWeightedSum (shiftedProfileWeight Q N v) N (b * d)) / d)

/-- Factoring the two dilation powers gives the exact normalized harmonic profile row. -/
theorem shiftedProfileHarmonicRow_eq (P Q : ℝ → ℝ) (c v : ℝ) (k : ℕ)
    {N a b : ℕ} (hN : 1 < N) (ha : 0 < a) (hb : 0 < b) :
    shiftedProfileHarmonicRow P Q N a b c v k =
      Real.exp (v * (Real.log a + Real.log b) / Real.log N) *
        normalizedHarmonicArray (max a b) N (fun d =>
          (Real.log d / Real.log N) ^ k *
            (Real.exp ((c + 2 * v) * (Real.log d / Real.log N)) *
              normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) v *
              normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) v)) := by
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold shiftedProfileHarmonicRow normalizedHarmonicArray
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [selbergMoebiusWeightedSum_shiftedProfile P v hN (Nat.mul_pos ha hd0),
    selbergMoebiusWeightedSum_shiftedProfile Q v hN (Nat.mul_pos hb hd0)]
  have hla : Real.log ((a * d : ℕ) : ℝ) = Real.log (a : ℝ) + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') hdR]
  have hlb : Real.log ((b * d : ℕ) : ℝ) = Real.log (b : ℝ) + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hb.ne') hdR]
  rw [hla, hlb]
  have hua : 1 - (Real.log a + Real.log d) / Real.log N = dilatedLogProfileCoordinate a N d := by
    dsimp only [dilatedLogProfileCoordinate]
    ring
  have hub : 1 - (Real.log b + Real.log d) / Real.log N = dilatedLogProfileCoordinate b N d := by
    dsimp only [dilatedLogProfileCoordinate]
    ring
  rw [hua, hub]
  have he : Real.exp (c * (Real.log d / Real.log N)) *
      Real.exp (v * (Real.log a + Real.log d) / Real.log N) *
      Real.exp (v * (Real.log b + Real.log d) / Real.log N) =
      Real.exp (v * (Real.log a + Real.log b) / Real.log N) *
        Real.exp ((c + 2 * v) * (Real.log d / Real.log N)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (c * (Real.log d / Real.log N)) *
        Real.exp (v * (Real.log a + Real.log d) / Real.log N) *
        Real.exp (v * (Real.log b + Real.log d) / Real.log N)) *
        ((Real.log d / Real.log N) ^ k *
          (normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) v *
            normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) v)) /
          ((d : ℝ) * Real.log N) := by field_simp [hlog, hdR] <;> ring
    _ = _ := by rw [he]; field_simp [hlog, hdR] <;> ring

/-- At the detector's coupled shift the diagonal exponential cancels exactly. -/
theorem shiftedProfileHarmonicRow_coupled (P Q : ℝ → ℝ) (v : ℝ) (k : ℕ)
    {N a b : ℕ} (hN : 1 < N) (ha : 0 < a) (hb : 0 < b) :
    shiftedProfileHarmonicRow P Q N a b (-2 * v) v k =
      Real.exp (v * (Real.log a + Real.log b) / Real.log N) *
        normalizedHarmonicArray (max a b) N (fun d =>
          (Real.log d / Real.log N) ^ k *
            (normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) v *
              normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) v)) := by
  rw [shiftedProfileHarmonicRow_eq P Q (-2 * v) v k hN ha hb]
  simp only [show -2 * v + 2 * v = 0 by ring, zero_mul, Real.exp_zero, one_mul]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
