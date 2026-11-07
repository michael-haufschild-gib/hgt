import GaloisForLFunctions.RHTower.Matveev.EffectiveBaker
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.EffectiveLogarithmicHalfTurn

/-!
# Polynomial discrete returns of the logarithmic rotation

The proved two-prime Baker bound gives a polynomial separation from integers
for multiples of `log 3 / log 4`. A small Dirichlet step, iterated to a
half-turn, therefore costs only a fixed power of the requested precision.
The same logarithmic-form estimate bounds the precision of every half-turn
by a fixed power of its index. Constants depend only on the scales two and three.
-/

noncomputable section
open scoped BigOperators Classical
open GaloisForLFunctions.RHTower.Matveev
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-- The proved two-prime logarithmic-form bound admits a positive integer exponent. -/
theorem exists_two_three_polynomial_separation :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ c : ℝ, 0 < c ∧ ∀ u v : ℤ, u ≠ 0 ∨ v ≠ 0 →
      c / (2 + (u.natAbs : ℝ) + v.natAbs) ^ D ≤
        |(u : ℝ) * Real.log 2 + (v : ℝ) * Real.log 3| := by
  let p : Fin 2 → ℕ := ![2, 3]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [p] at *
  have hprime : ∀ i, (p i).Prime := by
    intro i
    fin_cases i <;> norm_num [p]
  obtain ⟨c, C, hc, hC, hbound⟩ := effectiveBakerBound_holds p hp hprime
  let D := ⌈C⌉₊ + 1
  have hCD : C ≤ (D : ℝ) := by
    have h := Nat.le_ceil C
    dsimp only [D]
    push_cast
    linarith only [h]
  refine ⟨D, by dsimp only [D]; omega, c, hc, ?_⟩
  intro u v huv
  let ν : Fin 2 → ℤ := ![u, v]
  have hν : ν ≠ 0 := by
    intro he
    have hu : u = 0 := by simpa [ν] using congrFun he (0 : Fin 2)
    have hv : v = 0 := by simpa [ν] using congrFun he (1 : Fin 2)
    exact huv.elim (fun h => h hu) (fun h => h hv)
  let x : ℝ := 2 + (u.natAbs : ℝ) + v.natAbs
  have hx1 : 1 ≤ x := by
    have hu : (0 : ℝ) ≤ u.natAbs := Nat.cast_nonneg _
    have hv : (0 : ℝ) ≤ v.natAbs := Nat.cast_nonneg _
    dsimp only [x]
    linarith only [hu, hv]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hb : c * x ^ (-C) ≤ |(u : ℝ) * Real.log 2 + (v : ℝ) * Real.log 3| := by
    simpa [x, primeLogForm, coeffHeight, ν, p, Fin.sum_univ_two, add_assoc] using hbound ν hν
  have hpow : x ^ C ≤ x ^ D := by
    calc
      _ ≤ x ^ (D : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hCD
      _ = _ := Real.rpow_natCast x D
  have hd := div_le_div_of_nonneg_left hc.le (Real.rpow_pos_of_pos hx0 C) hpow
  rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv] at hb
  exact hd.trans hb

/-- Homogeneous returns of the logarithmic rotation have a fixed polynomial lower gap. -/
theorem exists_three_four_polynomial_gap :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ c : ℝ, 0 < c ∧ ∀ q m : ℕ, 1 ≤ q → m ≤ q →
      c / (q : ℝ) ^ D ≤ |(q : ℝ) * threeFourRotation - m| := by
  obtain ⟨D, hD, c, hc, hbound⟩ := exists_two_three_polynomial_separation
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  let c₀ := c / ((5 : ℝ) ^ D * Real.log 4)
  have hc₀ : 0 < c₀ := div_pos hc (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 5) D) h4)
  refine ⟨D, hD, c₀, hc₀, ?_⟩
  intro q m hq hm
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hmR : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hraw := hbound (-(2 * (m : ℤ))) (q : ℤ)
    (Or.inr (by exact_mod_cast (show q ≠ 0 by omega)))
  have hden : 2 + ((-(2 * (m : ℤ))).natAbs : ℝ) + ((q : ℤ).natAbs : ℝ) =
      2 + 2 * (m : ℝ) + q := by simp [Int.natAbs_mul]
  have he : (((-(2 * (m : ℤ))) : ℤ) : ℝ) * Real.log 2 + ((q : ℤ) : ℝ) * Real.log 3 =
      (q : ℝ) * Real.log 3 - m * Real.log 4 := by
    push_cast
    rw [hlog4]
    ring
  rw [hden, he] at hraw
  have hbase : 2 + 2 * (m : ℝ) + q ≤ 5 * (q : ℝ) := by linarith only [hq1, hmR]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 + 2 * m + q) hbase D
  have hgap : c / (5 * (q : ℝ)) ^ D ≤ |(q : ℝ) * Real.log 3 - m * Real.log 4| :=
    (div_le_div_of_nonneg_left hc.le (by positivity) hpow).trans hraw
  have heq : |(q : ℝ) * threeFourRotation - m| =
      |(q : ℝ) * Real.log 3 - m * Real.log 4| / Real.log 4 := by
    have h : (q : ℝ) * threeFourRotation - m =
        ((q : ℝ) * Real.log 3 - m * Real.log 4) / Real.log 4 := by
      dsimp only [threeFourRotation]
      field_simp
    rw [h, abs_div, abs_of_pos h4]
  rw [heq]
  calc
    _ = (c / (5 * (q : ℝ)) ^ D) / Real.log 4 := by
      dsimp only [c₀]
      simp only [div_div, mul_pow]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hgap h4.le

private theorem integer_half_turn_of_small_step {β : ℝ} (hβ : 0 < β) (hsmall : β < 1 / 2) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ 1 / (2 * β) ∧
      0 ≤ 1 / 2 - (j : ℝ) * β ∧ 1 / 2 - (j : ℝ) * β < β := by
  let j := ⌊1 / (2 * β)⌋₊
  have hden : 0 < 2 * β := by positivity
  have hlo : (j : ℝ) ≤ 1 / (2 * β) := Nat.floor_le (by positivity)
  have hhi : 1 / (2 * β) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo' := (le_div_iff₀ hden).mp hlo
  have hhi' := (div_lt_iff₀ hden).mp hhi
  have hj : 1 ≤ j := by
    by_contra hj
    have he : j = 0 := by omega
    rw [he] at hhi'
    norm_num at hhi'
    linarith only [hhi', hsmall]
  refine ⟨j, hj, hlo, ?_, ?_⟩ <;> nlinarith only [hlo', hhi']

/-- The fixed logarithmic rotation reaches every half-turn precision at polynomial cost. -/
theorem exists_polynomial_three_four_half_turn :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ A : ℝ, 0 < A ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ A * (Q : ℝ) ^ (D + 1) ∧
        ∃ ℓ : ℤ, |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / (Q : ℝ) := by
  obtain ⟨D, hD, c, hc, hgap⟩ := exists_three_four_polynomial_gap
  refine ⟨D, hD, 1 / (2 * c), by positivity, ?_⟩
  intro Q hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hhalf : 1 / (Q : ℝ) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hQ0 (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using hQR
  obtain ⟨q, hq, hqQ, hclose⟩ := HTGeometry.exists_simultaneous_dirichlet
    (fun _ : Fin 1 => threeFourRotation) (show 0 < Q by omega)
  simp only [pow_one] at hqQ
  obtain ⟨m, hm⟩ := hclose 0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hqR
  obtain ⟨hαlo, hαhi⟩ := threeFourRotation_bounds
  have hqa : 1 / 2 < (q : ℝ) * threeFourRotation := by
    have h := mul_le_mul_of_nonneg_right hqR (by linarith only [hαlo] : 0 ≤ threeFourRotation)
    simp only [one_mul] at h
    exact hαlo.trans_le h
  have hqb : (q : ℝ) * threeFourRotation < q := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hαhi hq0
  have hab := abs_lt.mp hm
  have hm0 : 0 ≤ m := by
    have hmr : (0 : ℝ) < m := by linarith only [hab.2, hhalf, hqa]
    exact_mod_cast hmr.le
  have hmq : m ≤ (q : ℤ) := by
    have hmr : (m : ℝ) < (q : ℝ) + 1 := by linarith only [hab.1, hhalf, hqb]
    have hi : m < (q : ℤ) + 1 := by exact_mod_cast hmr
    omega
  have hmcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
  let β := |(q : ℝ) * threeFourRotation - m|
  have hβgap : c / (q : ℝ) ^ D ≤ β := by
    simpa only [hmcast] using hgap q m.toNat hq (show m.toNat ≤ q by omega)
  have hβ : 0 < β := (div_pos hc (pow_pos hq0 D)).trans_le hβgap
  have hsmall : β < 1 / 2 := hm.trans_le hhalf
  obtain ⟨j, hj, hjbound, hrem0, hrem⟩ := integer_half_turn_of_small_step hβ hsmall
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hpow : (q : ℝ) ^ D ≤ (Q : ℝ) ^ D := pow_le_pow_left₀ hq0.le hqQR D
  have hQgap : c / (Q : ℝ) ^ D ≤ β :=
    (div_le_div_of_nonneg_left hc.le (pow_pos hq0 D) hpow).trans hβgap
  have hjbound' : (j : ℝ) ≤ (Q : ℝ) ^ D / (2 * c) := by
    apply hjbound.trans
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * β) (by positivity : 0 < 2 * c)).mpr
    have h := (div_le_iff₀ (pow_pos hQ0 D)).mp hQgap
    nlinarith only [h]
  refine ⟨j * q, Nat.mul_pos (by omega) (by omega), ?_, ?_⟩
  · push_cast
    calc
      (j : ℝ) * q ≤ ((Q : ℝ) ^ D / (2 * c)) * Q :=
        mul_le_mul hjbound' hqQR (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  · by_cases hd : 0 ≤ (q : ℝ) * threeFourRotation - m
    · refine ⟨(j : ℤ) * m, ?_⟩
      have he : ((j * q : ℕ) : ℝ) * threeFourRotation - ((j : ℤ) * m : ℤ) - 1 / 2 =
          -(1 / 2 - (j : ℝ) * β) := by
        dsimp only [β]
        rw [abs_of_nonneg hd]
        push_cast
        ring
      rw [he, abs_neg, abs_of_nonneg hrem0]
      exact hrem.trans hm
    · refine ⟨(j : ℤ) * m - 1, ?_⟩
      have he : ((j * q : ℕ) : ℝ) * threeFourRotation - ((j : ℤ) * m - 1 : ℤ) - 1 / 2 =
          1 / 2 - (j : ℝ) * β := by
        dsimp only [β]
        rw [abs_of_neg (lt_of_not_ge hd)]
        push_cast
        ring
      rw [he, abs_of_nonneg hrem0]
      exact hrem.trans hm


/-- Every sufficiently accurate half-turn return obeys a polynomial precision exclusion. -/
theorem exists_polynomial_half_turn_precision_bound :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ A : ℝ, 0 < A ∧ ∀ k Q : ℕ, 1 ≤ k → 2 ≤ Q →
      ∀ ℓ : ℤ, |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / (Q : ℝ) →
        (Q : ℝ) < A * (k : ℝ) ^ D := by
  obtain ⟨D, hD, c, hc, hbound⟩ := exists_two_three_polynomial_separation
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  let A := (6 : ℝ) ^ D * Real.log 4 / c
  refine ⟨D, hD, A, by dsimp only [A]; positivity, ?_⟩
  intro k Q hk hQ ℓ hclose
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hhalf : 1 / (Q : ℝ) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hQ0 (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using hQR
  obtain ⟨hαlo, hαhi⟩ := threeFourRotation_bounds
  have hka : 1 / 2 < (k : ℝ) * threeFourRotation := by
    have h := mul_le_mul_of_nonneg_right hk1 (by linarith only [hαlo] : 0 ≤ threeFourRotation)
    simp only [one_mul] at h
    exact hαlo.trans_le h
  have hkb : (k : ℝ) * threeFourRotation < k := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hαhi hk0
  have hab := abs_lt.mp hclose
  have hℓ0 : 0 ≤ ℓ := by
    have hr : (-1 : ℝ) < ℓ := by linarith only [hab.2, hhalf, hka]
    have hi : (-1 : ℤ) < ℓ := by exact_mod_cast hr
    omega
  have hℓR : (0 : ℝ) ≤ ℓ := by exact_mod_cast hℓ0
  have hℓk : (ℓ : ℝ) ≤ k := by linarith only [hab.1, hhalf, hkb]
  have hraw := hbound (-(2 * ℓ + 1)) (k : ℤ)
    (Or.inr (by exact_mod_cast (show k ≠ 0 by omega)))
  have huabs : ((-(2 * ℓ + 1)).natAbs : ℝ) = 2 * (ℓ : ℝ) + 1 := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    rw [abs_neg]
    exact abs_of_nonneg (by linarith only [hℓR])
  have hden : 2 + ((-(2 * ℓ + 1)).natAbs : ℝ) + ((k : ℤ).natAbs : ℝ) =
      3 + 2 * (ℓ : ℝ) + k := by rw [huabs]; simp; ring
  have hform : (((-(2 * ℓ + 1)) : ℤ) : ℝ) * Real.log 2 + ((k : ℤ) : ℝ) * Real.log 3 =
      ((k : ℝ) * threeFourRotation - ℓ - 1 / 2) * Real.log 4 := by
    push_cast
    dsimp only [threeFourRotation]
    rw [show Real.log 2 = Real.log 4 / 2 by linarith only [hlog4]]
    field_simp
    ring
  rw [hden, hform, abs_mul, abs_of_pos h4] at hraw
  have hbase : 3 + 2 * (ℓ : ℝ) + k ≤ 6 * (k : ℝ) := by linarith only [hk1, hℓk]
  have hbase0 : 0 < 3 + 2 * (ℓ : ℝ) + k := by positivity
  have hpow := pow_le_pow_left₀ hbase0.le hbase D
  have hgap : c / (6 * (k : ℝ)) ^ D ≤
      |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| * Real.log 4 :=
    (div_le_div_of_nonneg_left hc.le (pow_pos hbase0 D) hpow).trans hraw
  have hsmall : |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| * Real.log 4 <
      Real.log 4 / (Q : ℝ) := by
    calc
      _ < (1 / (Q : ℝ)) * Real.log 4 := mul_lt_mul_of_pos_right hclose h4
      _ = _ := by ring
  have hcross := (div_lt_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < 6 * k) D) hQ0).mp
    (hgap.trans_lt hsmall)
  have hq : (Q : ℝ) < Real.log 4 * (6 * (k : ℝ)) ^ D / c := by
    apply (lt_div_iff₀ hc).mpr
    nlinarith only [hcross]
  calc
    _ < Real.log 4 * (6 * (k : ℝ)) ^ D / c := hq
    _ = _ := by dsimp only [A]; rw [mul_pow]; ring


end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
