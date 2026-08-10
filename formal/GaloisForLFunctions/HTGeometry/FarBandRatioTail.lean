import GaloisForLFunctions.HTGeometry.IntegerSeriesBounds
import GaloisForLFunctions.HTGeometry.NearDiagonalHarmonicTail

/-!
# The far-band ratio weight

On the frequency lattice the weight

`c · I / ((1 + |j|)² · |I + j|)`,

restricted to the far band `I < 2|j|`, tends to zero as `I → ∞`.  The two regimes are separated by
comparing `|j|` with `2|I + j|`:

* if `|j| ≤ 2|I + j|` the weight is `O(1/(1 + |j|)²)` on a band escaping to infinity;
* otherwise `|I + j| < I` and the weight is `O(1/(I·|I + j|))`, a near-diagonal harmonic band.

Both regimes vanish, by `tendsto_tsum_far_of_ne_top` and `tendsto_tsum_nearDiagonal_zero`.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- **The far-band ratio weight vanishes.** -/
theorem tendsto_tsum_farBandRatio_zero {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0))
      atTop (nhds 0) := by
  have hdom : ∀ I : ℕ, ∀ j : ℤ,
      (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0)
      ≤ (if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intQuadWeight j else 0) +
        (if ((I : ℤ) + j).natAbs < I then
          ENNReal.ofReal (4 * c / ((I : ℝ) * (((I : ℤ) + j).natAbs : ℝ))) else 0) := by
    intro I j
    by_cases hsupp : I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0
    swap
    · rw [if_neg hsupp]
      exact zero_le
    rw [if_pos hsupp]
    obtain ⟨hIa, hn0⟩ := hsupp
    have habsR : |(j : ℝ)| = (j.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have habsZ : |j| = (j.natAbs : ℤ) := (Int.natCast_natAbs j).symm
    have ha1 : 1 ≤ j.natAbs := by omega
    have hn1 : 1 ≤ ((I : ℤ) + j).natAbs := by omega
    have haR : (1 : ℝ) ≤ (j.natAbs : ℝ) := by exact_mod_cast ha1
    have hnR : (1 : ℝ) ≤ (((I : ℤ) + j).natAbs : ℝ) := by exact_mod_cast hn1
    have hIR : (0 : ℝ) ≤ (I : ℝ) := Nat.cast_nonneg _
    have hIaR : (I : ℝ) < 2 * (j.natAbs : ℝ) := by exact_mod_cast hIa
    have hXne : ((1 : ℝ) + (j.natAbs : ℝ)) ^ 2 ≠ 0 := by positivity
    have hden : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ) := by
      have : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ 2 := by positivity
      nlinarith
    by_cases hcase : j.natAbs ≤ 2 * ((I : ℤ) + j).natAbs
    · -- escaping quadratic band
      refine le_trans ?_ (le_add_right le_rfl)
      have hband : ((I / 2 : ℕ) : ℤ) < |j| := by
        rw [habsZ]
        omega
      rw [if_pos hband]
      have hquad : intQuadWeight j = ENNReal.ofReal (1 / (1 + (j.natAbs : ℝ)) ^ 2) := by
        rw [intQuadWeight, habsR]
      rw [hquad, ← ENNReal.ofReal_mul (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      have hcaseR : (j.natAbs : ℝ) ≤ 2 * (((I : ℤ) + j).natAbs : ℝ) := by exact_mod_cast hcase
      rw [div_le_iff₀ hden]
      have hsimp : 8 * c * (1 / (1 + (j.natAbs : ℝ)) ^ 2) *
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))
          = 8 * c * (((I : ℤ) + j).natAbs : ℝ) := by
        field_simp
      rw [hsimp]
      nlinarith
    · -- near-diagonal harmonic band
      rw [not_le] at hcase
      have hnI : ((I : ℤ) + j).natAbs < I := by omega
      refine le_trans ?_ (le_add_left le_rfl)
      rw [if_pos hnI]
      apply ENNReal.ofReal_le_ofReal
      have hIpos : (0 : ℝ) < (I : ℝ) := by
        have : 0 < I := by omega
        exact_mod_cast this
      have hInpos : (0 : ℝ) < (I : ℝ) * (((I : ℤ) + j).natAbs : ℝ) := by positivity
      rw [div_le_div_iff₀ hden hInpos]
      have hI2 : (I : ℝ) ^ 2 ≤ 4 * (1 + (j.natAbs : ℝ)) ^ 2 := by nlinarith
      nlinarith [hI2, mul_nonneg hc (by linarith : (0 : ℝ) ≤ (((I : ℤ) + j).natAbs : ℝ))]
  have hfar : Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intQuadWeight j else 0))
      atTop (nhds 0) := by
    have hb : Tendsto (fun I : ℕ => I / 2) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨2 * b, fun I hI => by omega⟩
    exact tendsto_tsum_far_of_ne_top
      (tsum_const_mul_intQuadWeight_ne_top ENNReal.ofReal_ne_top) hb
  have hnear : Tendsto (fun I : ℕ => ∑' j : ℤ,
      (if ((I : ℤ) + j).natAbs < I then
        ENNReal.ofReal (4 * c / ((I : ℝ) * (((I : ℤ) + j).natAbs : ℝ))) else 0))
      atTop (nhds 0) := by
    have hbase := tendsto_tsum_nearDiagonal_zero (c := 4 * c) (by linarith)
    refine hbase.congr ?_
    intro I
    exact (Equiv.tsum_eq (Equiv.addLeft (I : ℤ))
      (fun n : ℤ => if n.natAbs < I then
        ENNReal.ofReal (4 * c / ((I : ℝ) * (n.natAbs : ℝ))) else 0)).symm
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hfar (ε / 2) hhalf,
    ENNReal.tendsto_nhds_zero.mp hnear (ε / 2) hhalf] with I h1 h2
  calc ∑' j : ℤ, (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (c * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0)
      ≤ ∑' j : ℤ,
          ((if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intQuadWeight j else 0) +
            (if ((I : ℤ) + j).natAbs < I then
              ENNReal.ofReal (4 * c / ((I : ℝ) * (((I : ℤ) + j).natAbs : ℝ))) else 0)) :=
        ENNReal.tsum_le_tsum (hdom I)
    _ = (∑' j : ℤ,
          (if ((I / 2 : ℕ) : ℤ) < |j| then ENNReal.ofReal (8 * c) * intQuadWeight j else 0)) +
        ∑' j : ℤ, (if ((I : ℤ) + j).natAbs < I then
          ENNReal.ofReal (4 * c / ((I : ℝ) * (((I : ℤ) + j).natAbs : ℝ))) else 0) :=
        ENNReal.tsum_add
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

end GaloisForLFunctions
