import GaloisForLFunctions.HTGeometry.LogFrequencySeparation
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Effective half-turns of the logarithmic rotation

For `α = log 3 / log 4`, every precision `1/Q`, with `Q ≥ 2`, admits
an integer half-turn return by index `Q * 4^Q * log 4 / 2`.

Dirichlet approximation supplies a small homogeneous return. Distinct integer
powers of three and four bound that return away from zero. A controlled
multiple therefore reaches a half-turn; its sign does not matter modulo one.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-- The discrete rotation induced by the independent integer scales three and four. -/
def threeFourRotation : ℝ := Real.log 3 / Real.log 4

private theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

theorem threeFourRotation_bounds : 1 / 2 < threeFourRotation ∧ threeFourRotation < 1 := by
  constructor
  · apply (lt_div_iff₀ log_four_pos).mpr
    have h : Real.log 4 < 2 * Real.log 3 := by
      have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < 4)
        (by norm_num : (4 : ℝ) < 3 * 3)
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hh
      linarith only [hh]
    linarith only [h]
  · exact (div_lt_one log_four_pos).mpr
      (Real.log_lt_log (by norm_num) (by norm_num))

/-- Integer separation gives an explicit lower bound for every relevant rational approximation. -/
theorem threeFourRotation_gap {q m : ℕ} (hq : 1 ≤ q) (hm : m ≤ q) :
    1 / ((4 : ℝ) ^ q * Real.log 4) ≤ |(q : ℝ) * threeFourRotation - m| := by
  have hne : (3 : ℕ) ^ q ≠ 4 ^ m := by
    intro he
    have he' : (3 : ℕ) ^ q = 2 ^ (2 * m) := by
      simpa only [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] using he
    have hp3 : Nat.Prime 3 := by norm_num
    have hf := congrArg (fun n : ℕ => n.factorization 3) he'
    simp only [hp3.factorization_pow, Nat.prime_two.factorization_pow,
      Finsupp.single_apply] at hf
    norm_num at hf
    omega
  have h := HTGeometry.inv_le_abs_log_sub_log_of_le
    (pow_pos (by norm_num : 0 < (3 : ℕ)) q)
    (pow_pos (by norm_num : 0 < (4 : ℕ)) m) hne
    (Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ≤ 4) q)
    (Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) hm)
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  have he : |(q : ℝ) * threeFourRotation - m| =
      |(q : ℝ) * Real.log 3 - m * Real.log 4| / Real.log 4 := by
    have he : (q : ℝ) * threeFourRotation - m =
        ((q : ℝ) * Real.log 3 - m * Real.log 4) / Real.log 4 := by
      dsimp only [threeFourRotation]
      field_simp
    rw [he, abs_div, abs_of_pos log_four_pos]
  rw [he]
  calc
    _ = ((4 : ℝ) ^ q)⁻¹ / Real.log 4 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right h log_four_pos.le

/-- A sufficiently close homogeneous return has an integer winding between zero and its index. -/
private theorem dirichlet_winding_range {q Q : ℕ} {m : ℤ}
    (hq : 1 ≤ q) (hQ : 2 ≤ Q)
    (hm : |(q : ℝ) * threeFourRotation - m| < 1 / (Q : ℝ)) :
    0 ≤ m ∧ m ≤ (q : ℤ) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by positivity
  have hhalf : 1 / (Q : ℝ) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hQ0 (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using hQR
  obtain ⟨hlo, hhi⟩ := threeFourRotation_bounds
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hqR
  have hqa : 1 / 2 < (q : ℝ) * threeFourRotation := by
    have h := mul_le_mul_of_nonneg_right hqR (by linarith only [hlo])
    simp only [one_mul] at h
    exact hlo.trans_le h
  have hqb : (q : ℝ) * threeFourRotation < q := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hhi hq0
  have hab := abs_lt.mp hm
  constructor
  · have hr : (0 : ℝ) < m := by linarith only [hab.2, hhalf, hqa]
    exact_mod_cast hr.le
  · have hr : (m : ℝ) < (q : ℝ) + 1 := by linarith only [hab.1, hhalf, hqb]
    have hi : m < (q : ℤ) + 1 := by exact_mod_cast hr
    omega

private theorem half_turn_of_small_step {β : ℝ} (hβ : 0 < β) (hsmall : β < 1 / 2) :
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

/-- A discrete logarithmic orbit reaches a half-turn with an explicit index bound. -/
theorem exists_effective_three_four_half_turn {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / 2 ∧
      ∃ ℓ : ℤ, |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / (Q : ℝ) := by
  obtain ⟨q, hq, hqQ, hqclose⟩ := HTGeometry.exists_simultaneous_dirichlet
    (fun _ : Fin 1 => threeFourRotation) (show 0 < Q by omega)
  simp only [pow_one] at hqQ
  obtain ⟨m, hm⟩ := hqclose 0
  have hrange := dirichlet_winding_range hq hQ hm
  have hmcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hrange.1
  have hmnat : m.toNat ≤ q := by omega
  let β := |(q : ℝ) * threeFourRotation - m|
  have hgap : 1 / ((4 : ℝ) ^ q * Real.log 4) ≤ β := by
    simpa only [hmcast] using threeFourRotation_gap hq hmnat
  have hden : 0 < (4 : ℝ) ^ q * Real.log 4 := by
    exact mul_pos (by positivity) log_four_pos
  have hβ : 0 < β := (div_pos zero_lt_one hden).trans_le hgap
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by positivity
  have hsmall : β < 1 / 2 := by
    apply hm.trans_le
    apply (div_le_div_iff₀ hQ0 (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using hQR
  obtain ⟨j, hj, hjbound, hrem0, hrem⟩ := half_turn_of_small_step hβ hsmall
  have hjbound' : (j : ℝ) ≤ (4 : ℝ) ^ q * Real.log 4 / 2 := by
    apply hjbound.trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * β)).mpr
    have h := (div_le_iff₀ hden).mp hgap
    nlinarith only [h]
  have hpow : (4 : ℝ) ^ q ≤ 4 ^ Q := pow_le_pow_right₀ (by norm_num) hqQ
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  refine ⟨j * q, Nat.mul_pos (by omega) (by omega), ?_, ?_⟩
  · push_cast
    calc
      (j : ℝ) * q ≤ ((4 : ℝ) ^ q * Real.log 4 / 2) * Q :=
        mul_le_mul hjbound' hqQR (Nat.cast_nonneg _) (by positivity)
      _ ≤ ((4 : ℝ) ^ Q * Real.log 4 / 2) * Q := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpow log_four_pos.le) (by norm_num)) hQ0.le
      _ = _ := by ring
  · by_cases hd : 0 ≤ (q : ℝ) * threeFourRotation - m
    · refine ⟨(j : ℤ) * m, ?_⟩
      have he : ((j * q : ℕ) : ℝ) * threeFourRotation - ((j : ℤ) * m : ℤ) - 1 / 2 =
          - (1 / 2 - (j : ℝ) * β) := by
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

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
