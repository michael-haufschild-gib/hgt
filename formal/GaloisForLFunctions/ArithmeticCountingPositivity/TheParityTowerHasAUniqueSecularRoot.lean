import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityIsExhaustedByItsRamanujanTower
import GaloisForLFunctions.RHTower.ConstrainedProlateInfiniteSecular
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The secular data of the arithmetic parity tower

The counted Ramanujan coefficients have squared sum one. Their explicit
prime-power energies define a unique secular root, strictly below the
two-mode value because every higher tower coefficient is nonzero.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticIntersectionTheory

/-- The harmonic parity coefficient at conductor `p^k`, including the ground. -/
def primeParityTowerCoefficient (p : ℕ) : ℕ → ℝ
  | 0 => primeParityMean p
  | k + 1 => 2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) /
      Real.sqrt ((p ^ (k + 1)).totient : ℝ)

/-- The conductor-`p^k` adjunction energy measured above the ground energy. -/
def primeParityTowerEnergy (p : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (k + 1 : ℕ) * Real.log p + Real.log p / ((p : ℝ) - 1)

/-- The unique secular root of the counted parity constraint on its arithmetic tower. -/
def primeParitySecularRoot (p : ℕ) : ℝ :=
  RHTower.infiniteSecularRoot (primeParityTowerEnergy p) (primeParityTowerCoefficient p)

/-- The explicit tower diagonal is the actual arithmetic adjunction energy above gamma. -/
theorem primeParityTowerEnergy_eq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeParityTowerEnergy p k =
      ramanujanAdjunctionEnergy (p ^ k) - Real.eulerMascheroniConstant := by
  cases k with
  | zero => simp only [primeParityTowerEnergy, pow_zero, ramanujanAdjunctionEnergy_one, sub_self]
  | succ k =>
      rw [ramanujanAdjunctionEnergy, tameDifferent_prime_pow hp (Nat.succ_ne_zero k),
        Nat.cast_pow, Real.log_pow]
      change ((k + 1 : ℕ) : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1) = _
      ring

/-- Every positive tower coefficient has an explicit geometric square. -/
theorem primeParityTowerCoefficient_sq_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeParityTowerCoefficient p (k + 1) ^ 2 =
      4 * primeParityMean p ^ 2 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
  have hsign : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
    rw [sq, ← mul_pow]
    norm_num
  rw [primeParityTowerCoefficient, div_pow, mul_pow, mul_pow, hsign,
    Real.sq_sqrt (Nat.cast_nonneg _), Nat.totient_prime_pow_succ hp,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
  norm_num

/-- The arithmetic tower coefficients carry exactly unit squared mass. -/
theorem hasSum_primeParityTowerCoefficient_sq {p : ℕ} (hp : p.Prime) :
    HasSum (fun k => primeParityTowerCoefficient p k ^ 2) 1 := by
  have hlim : Tendsto (fun K => ∑ k ∈ range K, primeParityTowerCoefficient p (k + 1) ^ 2)
      atTop (𝓝 (1 - primeParityMean p ^ 2)) := by
    apply ((tendsto_primeParityTower_coefficient_mass hp).sub_const
      (primeParityMean p ^ 2)).congr'
    exact Eventually.of_forall fun K => by
      simp only [primeParityTowerCoefficient]
      ring
  have htail : HasSum (fun k => primeParityTowerCoefficient p (k + 1) ^ 2)
      (1 - primeParityMean p ^ 2) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun k => sq_nonneg _) _).mpr hlim
  have hs : Summable (fun k => primeParityTowerCoefficient p k ^ 2) :=
    (summable_nat_add_iff 1).mp htail.summable
  have he : (∑' k, primeParityTowerCoefficient p k ^ 2) = 1 := by
    rw [hs.tsum_eq_zero_add, htail.tsum_eq]
    change primeParityMean p ^ 2 + (1 - primeParityMean p ^ 2) = 1
    ring
  simpa only [he] using hs.hasSum

private theorem tower_coefficient_ne_zero {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeParityTowerCoefficient p k ≠ 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hc : 0 < primeParityMean p := div_pos (sub_pos.mpr hpR) (by positivity)
  cases k with
  | zero => exact hc.ne'
  | succ k =>
      have hsq : 0 < primeParityTowerCoefficient p (k + 1) ^ 2 := by
        rw [primeParityTowerCoefficient_sq_succ hp]
        exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hc))
          (mul_pos (pow_pos (by linarith only [hpR]) _) (sub_pos.mpr hpR))
      intro hz
      rw [hz] at hsq
      norm_num at hsq

private theorem tower_energy_order {p : ℕ} (hp : p.Prime) :
    primeParityTowerEnergy p 0 < primeParityTowerEnergy p 1 ∧
      primeParityTowerEnergy p 1 < primeParityTowerEnergy p 2 ∧
        ∀ j, primeParityTowerEnergy p 2 ≤ primeParityTowerEnergy p (j + 2) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hpR
  have hcorr : 0 < Real.log p / ((p : ℝ) - 1) := div_pos hlog (sub_pos.mpr hpR)
  refine ⟨?_, ?_, ?_⟩
  · norm_num only [primeParityTowerEnergy, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_add, one_mul]
    linarith only [hlog, hcorr]
  · norm_num only [primeParityTowerEnergy, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_add, one_mul]
    linarith only [hlog]
  · intro j
    change (2 : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1) ≤
      ((j + 2 : ℕ) : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1)
    push_cast
    nlinarith only [mul_nonneg (Nat.cast_nonneg j) hlog.le]

private theorem parity_twoModeRoot {p : ℕ} (hp : p.Prime) :
    GaloisForLFunctions.twoModeSecularRoot (primeParityTowerEnergy p 0)
      (primeParityTowerEnergy p 1) (primeParityTowerCoefficient p 0)
      (primeParityTowerCoefficient p 1) = (p : ℝ) * Real.log p / ((p : ℝ) + 3) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hm : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
  have hp3 : (p : ℝ) + 3 ≠ 0 := by positivity
  have hc : primeParityMean p ≠ 0 :=
    (div_pos (sub_pos.mpr hpR) (by positivity : (0 : ℝ) < p + 1)).ne'
  have h0 : primeParityTowerCoefficient p 0 = primeParityMean p := rfl
  have h1 : primeParityTowerCoefficient p 1 ^ 2 =
      4 * primeParityMean p ^ 2 / ((p : ℝ) - 1) := by
    simpa only [zero_add, pow_zero, one_mul] using primeParityTowerCoefficient_sq_succ hp 0
  have hden : primeParityMean p ^ 2 + 4 * primeParityMean p ^ 2 / ((p : ℝ) - 1) =
      primeParityMean p ^ 2 * ((p : ℝ) + 3) / ((p : ℝ) - 1) := by
    field_simp [hm]
    ring
  rw [GaloisForLFunctions.twoModeSecularRoot, h0, h1, hden]
  simp only [primeParityTowerEnergy, Nat.cast_one, zero_add, one_mul, mul_zero, add_zero]
  field_simp [hm, hp3, hc]
  ring

/-- The parity secular root is positive, annihilates its full series, and lies
strictly below the two-mode bound because the higher tower has positive mass. -/
theorem primeParitySecularRoot_spec {p : ℕ} (hp : p.Prime) :
    primeParitySecularRoot p ∈ Set.Ioo 0 ((p : ℝ) * Real.log p / ((p : ℝ) + 3)) ∧
      RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p)
        (primeParitySecularRoot p) = 0 ∧
      primeParitySecularRoot p < primeParityTowerEnergy p 1 := by
  obtain ⟨h01, h12, htail⟩ := tower_energy_order hp
  have hs := (hasSum_primeParityTowerCoefficient_sq hp).summable
  have h0 := tower_coefficient_ne_zero hp 0
  have h1 := tower_coefficient_ne_zero hp 1
  obtain ⟨hr, hz, hle⟩ := RHTower.infiniteSecularRoot_spec h01 h12 htail hs h0 h1
  let B := GaloisForLFunctions.twoModeSecularRoot (primeParityTowerEnergy p 0)
    (primeParityTowerEnergy p 1) (primeParityTowerCoefficient p 0) (primeParityTowerCoefficient p 1)
  have hB := GaloisForLFunctions.twoModeSecularRoot_mem_Ioo h01 h0 h1
  have hB2 : B < primeParityTowerEnergy p 2 := hB.2.trans h12
  have hfirst : 0 < primeParityTowerCoefficient p 2 ^ 2 /
      (primeParityTowerEnergy p 2 - B) :=
    div_pos (sq_pos_of_ne_zero (tower_coefficient_ne_zero hp 2)) (sub_pos.mpr hB2)
  have htailSum := RHTower.summable_infiniteSecularTail htail hs hB2
  have hleTail := le_hasSum htailSum.hasSum 0
    (fun j _ => RHTower.infiniteSecularTail_term_nonneg htail hB2 j)
  have hF : 0 < RHTower.infiniteSecular (primeParityTowerEnergy p)
      (primeParityTowerCoefficient p) B := by
    rw [RHTower.infiniteSecular_apply_twoModeRoot h01 h0 h1]
    exact hfirst.trans_le (by simpa only [zero_add, RHTower.infiniteSecularTail] using hleTail)
  have hstrict : RHTower.infiniteSecularRoot (primeParityTowerEnergy p)
      (primeParityTowerCoefficient p) < B := by
    apply lt_of_le_of_ne hle
    intro he
    dsimp only [B] at hF
    rw [← he, hz] at hF
    exact lt_irrefl 0 hF
  refine ⟨⟨hr.1, ?_⟩, hz, hr.2⟩
  simpa only [primeParitySecularRoot, B, parity_twoModeRoot hp] using hstrict

/-- No other zero of the full parity secular series lies between its first two poles. -/
theorem primeParitySecularRoot_unique {p : ℕ} (hp : p.Prime) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 (primeParityTowerEnergy p 1))
    (hz : RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p) s = 0) :
    s = primeParitySecularRoot p := by
  obtain ⟨h01, h12, htail⟩ := tower_energy_order hp
  obtain ⟨hr, hr0, _⟩ := RHTower.infiniteSecularRoot_spec h01 h12 htail
    (hasSum_primeParityTowerCoefficient_sq hp).summable
    (tower_coefficient_ne_zero hp 0) (tower_coefficient_ne_zero hp 1)
  exact RHTower.infiniteSecular_root_unique h12 htail
    (hasSum_primeParityTowerCoefficient_sq hp).summable
    (tower_coefficient_ne_zero hp 0) hs hr hz hr0

end GaloisForLFunctions.ArithmeticCountingPositivity
