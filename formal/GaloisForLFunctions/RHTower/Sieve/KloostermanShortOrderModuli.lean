import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum

/-!
# Short multiplicative-order moduli in Kloosterman sums

The divisors of `p^r - 1` for `r <= k*n` form a subpower-size family as `n`
grows, for every fixed `p >= 2` and `k`. Consequently their normalized
Kloosterman contribution has a subpower absolute bound, uniformly in both
frequencies and without a Weil or cancellation hypothesis.

This controls only the short-order part of a modulus sum. It does not bound
the large-order complement or prove the Ramanujan-Petersson conjecture.
-/

open scoped BigOperators
open Finset

namespace RHTower.Sieve

noncomputable section

/-- Indices `q` represent positive moduli `q + 1` dividing some `p^r - 1`,
with `1 <= r <= R`. -/
def shortOrderModuli (p R : ℕ) : Finset ℕ :=
  (range R).biUnion fun j => ((p ^ (j + 1) - 1).divisors).image Nat.pred

theorem mem_shortOrderModuli_of_dvd {p R q r : ℕ} (hp : 2 ≤ p)
    (hr : 0 < r) (hrR : r ≤ R) (hd : q + 1 ∣ p ^ r - 1) :
    q ∈ shortOrderModuli p R := by
  have hpow : 1 < p ^ r :=
    lt_of_le_of_lt hr (Nat.lt_pow_self (by omega : 1 < p))
  apply mem_biUnion.mpr
  refine ⟨r - 1, mem_range.mpr (by omega), mem_image.mpr ?_⟩
  refine ⟨q + 1, ?_, by simp⟩
  have he : r - 1 + 1 = r := by omega
  rw [he, Nat.mem_divisors]
  exact ⟨hd, by omega⟩

theorem card_shortOrderModuli_le {p : ℕ} (hp : 2 ≤ p) (R : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ((shortOrderModuli p R).card : ℝ) ≤
      (R : ℝ) * (divisorBoundConst δ * ((p ^ R : ℕ) : ℝ) ^ δ) := by
  have hD : 0 ≤ divisorBoundConst δ := (divisorBoundConst_pos hδ).le
  have hcard : (shortOrderModuli p R).card ≤
      ∑ j ∈ range R, (p ^ (j + 1) - 1).divisors.card := by
    exact card_biUnion_le.trans (sum_le_sum fun j _ => card_image_le)
  calc
    ((shortOrderModuli p R).card : ℝ) ≤
        ∑ j ∈ range R, ((p ^ (j + 1) - 1).divisors.card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _j ∈ range R, divisorBoundConst δ * ((p ^ R : ℕ) : ℝ) ^ δ := by
      apply sum_le_sum
      intro j hj
      have hpow : 1 < p ^ (j + 1) :=
        lt_of_le_of_lt (by omega : 1 ≤ j + 1)
          (Nat.lt_pow_self (by omega : 1 < p))
      have hle : p ^ (j + 1) - 1 ≤ p ^ R :=
        (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega : 0 < p)
          (by simpa using mem_range.mp hj))
      exact (card_divisors_le_rpow hδ (by omega : p ^ (j + 1) - 1 ≠ 0)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) hδ.le) hD)
    _ = _ := by simp

theorem shortOrderModuli_subpower {p : ℕ} (hp : 2 ≤ p) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ((shortOrderModuli p (k * n)).card : ℝ) ≤ C * ((p ^ n : ℕ) : ℝ) ^ ε := by
  let δ : ℝ := ε / (2 * ((k : ℝ) + 1))
  let a : ℝ := Real.log p * ε / 2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hD : 0 < divisorBoundConst δ := divisorBoundConst_pos hδ
  have hδeq : δ * (2 * ((k : ℝ) + 1)) = ε := by
    dsimp [δ]
    field_simp
  have hδk : (k : ℝ) * δ ≤ ε / 2 := by nlinarith
  refine ⟨divisorBoundConst δ * ((k : ℝ) + 1) * (1 + 1 / a),
    by positivity, ?_⟩
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hExp1 : 1 ≤ Real.exp (a * n) := Real.one_le_exp_iff.mpr (mul_nonneg ha.le hn0)
  have hnExp : (n : ℝ) + 1 ≤ (1 + 1 / a) * Real.exp (a * n) := by
    have hna : a * n ≤ Real.exp (a * n) := by
      linarith [Real.add_one_le_exp (a * n)]
    have hn : (n : ℝ) ≤ Real.exp (a * n) / a :=
      (le_div_iff₀ ha).mpr (by simpa [mul_comm] using hna)
    calc
      (n : ℝ) + 1 ≤ Real.exp (a * n) / a + Real.exp (a * n) := add_le_add hn hExp1
      _ = _ := by ring
  have hR : ((p ^ (k * n) : ℕ) : ℝ) ^ δ ≤ Real.exp (a * n) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
      Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδk hlog.le) hn0
    dsimp [a]
    push_cast
    nlinarith [h]
  have hkn : ((k * n : ℕ) : ℝ) ≤ ((k : ℝ) + 1) * ((n : ℝ) + 1) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  calc
    ((shortOrderModuli p (k * n)).card : ℝ) ≤
        ((k * n : ℕ) : ℝ) * (divisorBoundConst δ * ((p ^ (k * n) : ℕ) : ℝ) ^ δ) :=
      card_shortOrderModuli_le hp _ hδ
    _ ≤ (((k : ℝ) + 1) * ((n : ℝ) + 1)) *
        (divisorBoundConst δ * Real.exp (a * n)) :=
      mul_le_mul hkn (mul_le_mul_of_nonneg_left hR hD.le)
        (by positivity) (by positivity)
    _ ≤ (((k : ℝ) + 1) * ((1 + 1 / a) * Real.exp (a * n))) *
        (divisorBoundConst δ * Real.exp (a * n)) := by
      gcongr
    _ = (divisorBoundConst δ * ((k : ℝ) + 1) * (1 + 1 / a)) *
        ((p ^ n : ℕ) : ℝ) ^ ε := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
        Real.rpow_def_of_pos hp0]
      have he : Real.exp (a * n) * Real.exp (a * n) =
          Real.exp (Real.log p * ((n : ℝ) * ε)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [a]
        ring
      calc
        _ = (divisorBoundConst δ * ((k : ℝ) + 1) * (1 + 1 / a)) *
            (Real.exp (a * n) * Real.exp (a * n)) := by ring
        _ = _ := by rw [he]

/-- The short-period part of the actual Kloosterman modulus sum is subpower,
uniformly in the two arithmetic frequencies. No cancellation or Weil bound is assumed. -/
theorem shortOrder_kloosterman_subpower {p : ℕ} (hp : 2 ≤ p) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Q : Finset ℕ),
      Q ⊆ shortOrderModuli p (k * n) → ∀ w : ℕ → ℂ,
      (∀ q ∈ Q, ‖w q‖ ≤ 1 / ((q + 1 : ℕ) : ℝ)) → ∀ m l : ℤ,
      (∑ q ∈ Q, ‖w q * kloostermanSum (q + 1) (m : ZMod (q + 1))
        (l : ZMod (q + 1))‖) ≤ C * ((p ^ n : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC, hc⟩ := shortOrderModuli_subpower hp k hε
  refine ⟨C, hC, ?_⟩
  intro n Q hQ w hw m l
  calc
    _ ≤ ∑ _q ∈ Q, (1 : ℝ) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      have hK : ‖kloostermanSum (q + 1) (m : ZMod (q + 1))
          (l : ZMod (q + 1))‖ ≤ ((q + 1 : ℕ) : ℝ) :=
        (norm_kloostermanSum_le_totient _ _ _).trans
          (by exact_mod_cast Nat.totient_le (q + 1))
      calc
        _ ≤ (1 / ((q + 1 : ℕ) : ℝ)) * ((q + 1 : ℕ) : ℝ) :=
          mul_le_mul (hw q hq) hK (norm_nonneg _) (by positivity)
        _ = 1 := by field_simp
    _ = (Q.card : ℝ) := by simp
    _ ≤ ((shortOrderModuli p (k * n)).card : ℝ) := by exact_mod_cast card_le_card hQ
    _ ≤ _ := hc n

end
end RHTower.Sieve
