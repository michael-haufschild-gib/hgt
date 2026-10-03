import GaloisForLFunctions.HTGeometry.StonehamParityDrift

/-!
# Windows of the Stoneham constants `α_{2,p}`

For an odd `p ≥ 3` let `α_p = Σ_{j ≥ 1} p^{−j} 2^{−p^j}` and `Aₖ = Σ_{j ≤ k} 2^{pᵏ − pʲ} p^{k−j}`.
For `pᵏ ≤ 2n < p^{k+1}`,

`4ⁿ α_p = 2^{2n − pᵏ} Aₖ / pᵏ + t`,  `0 < t`, `4 pᵏ t < 1`,

so inside the `k`-th window the base-4 digits of `α_p` are exactly the first base-4 digits
`⌊4ρ/pᵏ⌋` of the orbit points `ρ = 2Aₖ4ⁱ mod pᵏ` (`quatDigit_stonehamP_window`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamPrimeDrift

open BinaryParityDrift

/-- The terms `p^{−(j+1)} 2^{−p^{j+1}}`. -/
noncomputable def stonehamPTerm (p j : ℕ) : ℝ := 1 / ((p : ℝ) ^ (j + 1) * 2 ^ (p ^ (j + 1)))

/-- The Stoneham constant `α_{2,p} = Σ_{j ≥ 1} p^{−j} 2^{−p^j}`. -/
noncomputable def stonehamP (p : ℕ) : ℝ := ∑' j, stonehamPTerm p j

/-- `Aₖ = Σ_{j < k} 2^{pᵏ − p^{j+1}} p^{k−(j+1)}`. -/
def stonehamPA (p k : ℕ) : ℕ := ∑ j ∈ range k, 2 ^ (p ^ k - p ^ (j + 1)) * p ^ (k - (j + 1))

variable {p : ℕ}

theorem stonehamPTerm_pos (hp : 0 < p) (j : ℕ) : 0 < stonehamPTerm p j := by
  unfold stonehamPTerm; positivity

theorem stonehamPTerm_le (hp : 2 ≤ p) (j : ℕ) : stonehamPTerm p j ≤ (1 / 2) ^ (j + 1) := by
  unfold stonehamPTerm
  rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (2 : ℝ) ^ (j + 1) ≤ (p : ℝ) ^ (j + 1) := pow_le_pow_left₀ (by norm_num) hp' _
  have h2 : (1 : ℝ) ≤ 2 ^ (p ^ (j + 1)) := one_le_pow₀ (by norm_num)
  calc (2 : ℝ) ^ (j + 1) = 2 ^ (j + 1) * 1 := (mul_one _).symm
    _ ≤ (p : ℝ) ^ (j + 1) * 2 ^ (p ^ (j + 1)) := mul_le_mul h1 h2 zero_le_one (by positivity)

theorem summable_stonehamPTerm (hp : 2 ≤ p) : Summable (stonehamPTerm p) :=
  Summable.of_nonneg_of_le (fun j => (stonehamPTerm_pos (by omega) j).le) (stonehamPTerm_le hp)
    ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1))

theorem stonehamPA_mod (hp : 2 ≤ p) {k : ℕ} (hk : 1 ≤ k) : stonehamPA p k % p = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold stonehamPA
  rw [sum_range_succ, Nat.sub_self, Nat.sub_self, pow_zero, pow_zero, mul_one]
  have hdvd : p ∣ ∑ j ∈ range m, 2 ^ (p ^ (m + 1) - p ^ (j + 1)) * p ^ (m + 1 - (j + 1)) := by
    refine dvd_sum fun j hj => ?_
    have : 1 ≤ m + 1 - (j + 1) := by rw [mem_range] at hj; omega
    exact Dvd.dvd.mul_left (dvd_pow_self p (by omega)) _
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega : 1 < p)]

theorem one_add_two_mul_le_pow (hp : 3 ≤ p) (j : ℕ) : 1 + 2 * j ≤ p ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ]; nlinarith

/-- **Window decomposition with a sharp tail.** -/
theorem four_pow_mul_stonehamP (hp : 3 ≤ p) (hodd : p % 2 = 1) {k n : ℕ}
    (hk1 : p ^ k ≤ 2 * n) (hk2 : 2 * n < p ^ (k + 1)) :
    ∃ t : ℝ, 0 < t ∧ 4 * p ^ k * t < 1 ∧
      (4 : ℝ) ^ n * stonehamP p = ((2 ^ (2 * n - p ^ k) * stonehamPA p k : ℕ) : ℝ) / p ^ k + t := by
  have hp2 : 2 ≤ p := by omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hsplit := (summable_stonehamPTerm hp2).sum_add_tsum_nat_add k
  have hsum' := (summable_stonehamPTerm hp2).comp_injective (add_left_injective k)
  refine ⟨(4 : ℝ) ^ n * ∑' j, stonehamPTerm p (j + k), ?_, ?_, ?_⟩
  · exact mul_pos (by positivity) (hsum'.tsum_pos (fun j => (stonehamPTerm_pos (by omega) _).le)
      0 (stonehamPTerm_pos (by omega) _))
  · have hoddk : p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr hodd))
    have hb : ∀ j : ℕ, (4 : ℝ) ^ n * stonehamPTerm p (j + k) ≤
        1 / ((p : ℝ) ^ (k + 1) * 2 * 4 ^ j) := by
      intro j
      unfold stonehamPTerm
      have hexp : 2 * n + 1 + 2 * j ≤ p ^ (j + k + 1) := by
        have hj := one_add_two_mul_le_pow hp j
        have h3 : p ^ (j + k + 1) = p ^ (k + 1) * p ^ j := by rw [← pow_add]; ring_nf
        have h1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
        rw [h3]
        nlinarith
      have h4 : (4 : ℝ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
      have h4j : (4 : ℝ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
      rw [h4, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, h4j]
      have h5 : (2 : ℝ) ^ (2 * n) * 2 * 2 ^ (2 * j) ≤ 2 ^ (p ^ (j + k + 1)) := by
        rw [← pow_succ, ← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h6 : (p : ℝ) ^ (k + 1) ≤ (p : ℝ) ^ (j + k + 1) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      calc (2 : ℝ) ^ (2 * n) * ((p : ℝ) ^ (k + 1) * 2 * 2 ^ (2 * j)) =
          (p : ℝ) ^ (k + 1) * (2 ^ (2 * n) * 2 * 2 ^ (2 * j)) := by ring
        _ ≤ (p : ℝ) ^ (j + k + 1) * 2 ^ (p ^ (j + k + 1)) := by gcongr
    have hg : Summable fun j : ℕ => 1 / ((p : ℝ) ^ (k + 1) * 2 * 4 ^ j) :=
      ((summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
        (1 / ((p : ℝ) ^ (k + 1) * 2))).congr fun j => by rw [one_div_pow]; field_simp
    have htail : (4 : ℝ) ^ n * ∑' j, stonehamPTerm p (j + k) ≤ 2 / (3 * (p : ℝ) ^ (k + 1)) := by
      calc (4 : ℝ) ^ n * ∑' j, stonehamPTerm p (j + k) =
            ∑' j, (4 : ℝ) ^ n * stonehamPTerm p (j + k) := (tsum_mul_left).symm
        _ ≤ ∑' j : ℕ, 1 / ((p : ℝ) ^ (k + 1) * 2 * 4 ^ j) :=
            Summable.tsum_le_tsum hb (hsum'.mul_left _) hg
        _ = 2 / (3 * (p : ℝ) ^ (k + 1)) := by
            have e : ∀ j : ℕ, 1 / ((p : ℝ) ^ (k + 1) * 2 * 4 ^ j) =
                1 / ((p : ℝ) ^ (k + 1) * 2) * (1 / 4 : ℝ) ^ j := fun j => by
              rw [one_div_pow]; field_simp
            simp_rw [e]
            rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            field_simp
            norm_num
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    calc 4 * (p : ℝ) ^ k * ((4 : ℝ) ^ n * ∑' j, stonehamPTerm p (j + k))
        ≤ 4 * (p : ℝ) ^ k * (2 / (3 * (p : ℝ) ^ (k + 1))) := by gcongr
      _ = 8 / (3 * p) := by rw [pow_succ]; field_simp; ring
      _ < 1 := by rw [div_lt_one (by positivity)]; linarith
  · rw [stonehamP, ← hsplit, mul_add]
    congr 1
    rw [Finset.mul_sum, stonehamPA]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    unfold stonehamPTerm
    have hjk : p ^ (j + 1) ≤ p ^ k := Nat.pow_le_pow_right (by omega) hj
    have e2 : (2 : ℝ) ^ (2 * n) = 2 ^ (2 * n - p ^ k) * 2 ^ (p ^ k - p ^ (j + 1)) *
        2 ^ (p ^ (j + 1)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e3 : (p : ℝ) ^ k = (p : ℝ) ^ (k - (j + 1)) * (p : ℝ) ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    have h4 : (4 : ℝ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [h4, e2, e3]
    field_simp

/-- A shift by less than `1/(4q)` does not change the first base-4 digit of `r/q`. -/
theorem floor_four_mul_add_eq {q r : ℕ} (hq : 0 < q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : 4 * q * t < 1) : ⌊4 * ((r : ℝ) / q + t)⌋ = ((4 * r / q : ℕ) : ℤ) := by
  set D := 4 * r / q with hD
  have hlo : D * q ≤ 4 * r := Nat.div_mul_le_self _ _
  have hhi : 4 * r + 1 ≤ (D + 1) * q := by
    have h := Nat.lt_mul_div_succ (4 * r) hq
    rw [← hD] at h
    rw [mul_comm (D + 1)]
    exact h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hloR : (D : ℝ) * q ≤ 4 * r := by exact_mod_cast hlo
  have hhiR : 4 * (r : ℝ) + 1 ≤ (D + 1) * q := by exact_mod_cast hhi
  rw [Int.floor_eq_iff]
  push_cast
  rw [show (4 : ℝ) * (r / q + t) = (4 * r + 4 * q * t) / q by field_simp,
    le_div_iff₀ hqR, div_lt_iff₀ hqR]
  constructor <;> nlinarith

/-- **Digits inside the windows.**  For `2i + 1 < pᵏ(p − 1)` the base-4 digit of `α_p` at
position `(pᵏ + 1)/2 + i + 1` is the first base-4 digit of `ρ/pᵏ`, `ρ = 2Aₖ4ⁱ mod pᵏ`. -/
theorem quatDigit_stonehamP_window (hp : 3 ≤ p) (hodd : p % 2 = 1) {k i : ℕ}
    (hi : 2 * i + 1 < p ^ k * (p - 1)) :
    quatDigit (stonehamP p) ((p ^ k + 1) / 2 + i + 1) =
      ((4 * (2 * stonehamPA p k * 4 ^ i % p ^ k) / p ^ k : ℕ) : ℤ) := by
  have hoddk : p ^ k % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr hodd))
  have hpk : 0 < p ^ k := by positivity
  set n := (p ^ k + 1) / 2 + i with hn
  have h2n : 2 * n = p ^ k + (2 * i + 1) := by rw [hn]; omega
  have hk1 : p ^ k ≤ 2 * n := by omega
  have hk2 : 2 * n < p ^ (k + 1) := by
    rw [h2n, pow_succ]
    have : p ^ k * (p - 1) + p ^ k = p ^ k * p := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  obtain ⟨t, ht0, ht1, heq⟩ := four_pow_mul_stonehamP hp hodd hk1 hk2
  have hM : 2 ^ (2 * n - p ^ k) * stonehamPA p k = 2 * stonehamPA p k * 4 ^ i := by
    rw [show 2 * n - p ^ k = 2 * i + 1 by omega, pow_succ, pow_mul]; norm_num; ring
  rw [hM] at heq
  set M := 2 * stonehamPA p k * 4 ^ i with hMdef
  have hqR : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  rw [StonehamParityDrift.quatDigit_succ_eq_floor_fract, heq]
  have hfract :
      Int.fract ((M : ℝ) / (p : ℝ) ^ k + t) = ((M % p ^ k : ℕ) : ℝ) / (p : ℝ) ^ k + t := by
    have hcast : (M : ℝ) = (p : ℝ) ^ k * ((M / p ^ k : ℕ) : ℝ) + ((M % p ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod M (p ^ k)).symm
    rw [hcast, show
        ((p : ℝ) ^ k * ((M / p ^ k : ℕ) : ℝ) + ((M % p ^ k : ℕ) : ℝ)) / (p : ℝ) ^ k + t =
        ((M % p ^ k : ℕ) : ℝ) / (p : ℝ) ^ k + t + ((M / p ^ k : ℕ) : ℝ) by field_simp; ring,
      Int.fract_add_natCast, Int.fract_eq_self]
    have hlt : ((M % p ^ k : ℕ) : ℝ) + 1 ≤ (p : ℝ) ^ k := by
      exact_mod_cast Nat.mod_lt M hpk
    refine ⟨by positivity, ?_⟩
    rw [div_add' _ _ _ hqR.ne', div_lt_one hqR]
    nlinarith
  rw [hfract]
  have := floor_four_mul_add_eq (q := p ^ k) (r := M % p ^ k) hpk ht0.le
    (by push_cast; exact ht1)
  push_cast at this
  exact this

end GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
