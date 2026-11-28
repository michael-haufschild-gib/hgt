import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A quantitative Bertrand bound from the central binomial coefficient.
The prime reciprocal sum is needed only once the rank has grown past
the explicit threshold. -/

noncomputable section

open Finset Nat

namespace WindowedLandauTheory.ConcN

def longPrimes (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)

def longPrimeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ longPrimes N, (1 : ℝ) / p

private def upper (n : ℕ) : Finset ℕ := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)

private theorem centralBinom_le (n : ℕ) (n_large : 2 < n) :
    centralBinom n ≤
      ((2 * n) ^ (primeCounting (sqrt (2 * n))) * 4 ^ (2 * n / 3)) * (2 * n) ^ (upper n).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S0 := {p ∈ Finset.range (2 * n + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => pow_factorization_choose_le (mul_pos two_pos n_pos)
  have h0 : ∏ x ∈ S0, f x = centralBinom n := by
    rw [← n.prod_pow_factorization_centralBinom]
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [← h0, ← Finset.prod_filter_mul_prod_filter_not S0 (· ≤ 2 * n / 3)]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not _ (· ≤ sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ?_
      rw [← primesLE_card_eq_primeCounting]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
      exact mem_primesLE.mpr ⟨h2, (Finset.mem_filter.1 h3).2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
        refine (pow_right_mono₀ (Finset.mem_filter.1 h3).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      · unfold primorial
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
        · intro p hp
          obtain ⟨h1, _⟩ := Finset.mem_filter.1 hp
          obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), (Finset.mem_filter.1 h3).2⟩
        · exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · rw [← Finset.prod_filter_mul_prod_filter_not _ (· ≤ n)]
    have h1 : ∏ x ∈ {x ∈ {x ∈ S0 | ¬ x ≤ 2 * n / 3} | x ≤ n}, f x = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      obtain ⟨_, h4⟩ := Finset.mem_filter.1 h1
      dsimp only [f]
      rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h2 (by omega),
        _root_.pow_zero]
    rw [h1, one_mul]
    refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos (Finset.card_le_card fun x hx => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
    obtain ⟨h5, h6⟩ := Finset.mem_filter.1 h3
    exact Finset.mem_filter.2 ⟨h5, h6, by omega⟩

private theorem primeCounting_le (s : ℕ) (hs : 6 ≤ s) : (primeCounting s : ℝ) ≤ s / 3 + 3 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (s - 6)
  have e : 6 + (s - 6) = s := by omega
  rw [e] at h
  have h6 : primeCounting 6 ≤ 3 := by
    rw [← primesLE_card_eq_primeCounting]
    calc
      (primesLE 6).card ≤ ({2, 3, 5} : Finset ℕ).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨hp6, hp⟩ := mem_primesLE.mp hp
        have hp2 := hp.two_le
        have h4 : p ≠ 4 := fun he => (by norm_num : ¬ Nat.Prime 4) (he ▸ hp)
        have h6 : p ≠ 6 := fun he => (by norm_num : ¬ Nat.Prime 6) (he ▸ hp)
        have he : p = 2 ∨ p = 3 ∨ p = 5 := by omega
        rcases he with rfl | rfl | rfl <;> simp
      _ = 3 := by simp
  have t6 : totient 6 = 2 := by
    calc
      totient 6 = totient (2 * 3) := rfl
      _ = totient 2 * totient 3 := Nat.totient_mul (Nat.coprime_two_left.mpr ⟨1, rfl⟩)
      _ = 2 := by rw [totient_prime prime_two, totient_prime prime_three]
  rw [t6] at h
  have h := h.trans (Nat.add_le_add_right h6 _)
  have h2 : (((s - 6) / 6 : ℕ) : ℝ) ≤ ((s - 6 : ℕ) : ℝ) / 6 := Nat.cast_div_le
  have h3 : ((s - 6 : ℕ) : ℝ) = (s : ℝ) - 6 := by
    rw [Nat.cast_sub hs]; norm_num
  have h4 : (primeCounting s : ℝ) ≤ 3 + 2 * ((((s - 6) / 6 : ℕ) : ℝ) + 1) := by exact_mod_cast h
  rw [h3] at h2
  linarith

private theorem reciprocal_arithmetic {y L k : ℝ} (hy : 141 ≤ y)
    (hL : L ≤ 8 + y / 64)
    (h : 23 / 100 * y ^ 2 ≤ (y / 3 + 4 + k) * L) :
    y ^ 2 + 1 ≤ 5 * (k - 3) * L := by
  have ha := mul_le_mul_of_nonneg_left hL (show 0 ≤ y / 3 + 7 by linarith only [hy])
  have hb : y ^ 2 + 1 ≤
      5 * (23 / 100 * y ^ 2 - (y / 3 + 7) * (8 + y / 64)) := by
    nlinarith only [hy, sq_nonneg (y - 141)]
  nlinarith only [h, ha, hb]

private theorem upper_card (n : ℕ) (hn : 10000 ≤ n) :
    (2 * (n : ℝ) + 1) ≤ 5 * (((upper n).card : ℝ) - 3) * Real.log (2 * n) := by
  have h1 : 4 ^ n < n * centralBinom n := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le n (by omega)
  set k := (upper n).card with hk
  set s := sqrt (2 * n) with hs
  set c := primeCounting s with hc
  have h3 : 4 ^ n < n * (((2 * n) ^ c * 4 ^ (2 * n / 3)) * (2 * n) ^ k) :=
    lt_of_lt_of_le h1 (Nat.mul_le_mul_left n h2)
  have h4 : (4 : ℝ) ^ n < n * (((2 * n) ^ c * 4 ^ (2 * n / 3)) * (2 * n) ^ k) := by
    exact_mod_cast h3
  have hn1 : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have h5 := Real.log_lt_log (by positivity) h4
  rw [Real.log_mul hnpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at h5
  set L := Real.log (2 * n) with hLdef
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4] at h5
  set l := Real.log 2 with hl
  have hl1 : 69 / 100 ≤ l := by linarith only [Real.log_two_gt_d9]
  have hl2 : l ≤ 5 / 7 := by linarith only [Real.log_two_lt_d9]
  set y := Real.sqrt (2 * n) with hy
  have hy2 : y ^ 2 = 2 * n := Real.sq_sqrt h2n.le
  have hy141 : 141 ≤ y := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hypos : 0 < y := by linarith
  have hsy : (s : ℝ) ≤ y := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    simpa [hs, hy] using this
  have hs6 : 6 ≤ s := by
    rw [hs, Nat.le_sqrt]; omega
  have hcs : (c : ℝ) ≤ s / 3 + 3 := primeCounting_le s hs6
  have hLy : L = 2 * Real.log y := by
    rw [hLdef, ← hy2, Real.log_pow]; norm_num
  have hlogy : Real.log y ≤ 7 * l + y / 128 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / 128 by positivity)
    rw [Real.log_div hypos.ne' (by norm_num), show (128 : ℝ) = 2 ^ 7 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlogn : Real.log n ≤ L := Real.log_le_log hnpos (by linarith)
  have hdiv : (((2 * n / 3 : ℕ)) : ℝ) ≤ (2 * n : ℝ) / 3 := by
    have := (Nat.cast_div_le : (((2 * n) / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
    simpa using this
  have hcL : (c : ℝ) * L ≤ (y / 3 + 3) * L := mul_le_mul_of_nonneg_right (by linarith) hL0
  have hdl : (((2 * n / 3 : ℕ)) : ℝ) * (2 * l) ≤ (2 * n : ℝ) / 3 * (2 * l) :=
    mul_le_mul_of_nonneg_right hdiv (by linarith)
  have key : y ^ 2 * l / 3 < (y / 3 + 4 + k) * L := by
    rw [hy2]
    nlinarith only [h5, hcL, hdl, hlogn]
  have hkey : 23 / 100 * y ^ 2 ≤ (y / 3 + 4 + k) * L := by
    have h := mul_le_mul_of_nonneg_right hl1 (sq_nonneg y)
    linarith only [h, key]
  have hr := reciprocal_arithmetic hy141 (by linarith only [hLy, hlogy, hl2]) hkey
  rwa [hy2] at hr

theorem long_prime_reciprocal_sum_le (N : ℕ) (hN : 20000 ≤ N) : 1 / (5 * Real.log N) ≤ longPrimeReciprocalSum N := by
  obtain ⟨n, hn⟩ : ∃ n, n = N / 2 := ⟨_, rfl⟩
  have hn1 : 10000 ≤ n := by omega
  have hU := upper_card n hn1
  set F := longPrimes N with hF
  have hsub : upper n ⊆ F ∪ {N - 2, N - 1, N} := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hp
    have h1' := Finset.mem_range.1 h1
    by_cases h4 : p + 3 ≤ N
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h2, by omega, h4⟩)
    · refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  have hcard : (upper n).card ≤ F.card + 3 :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_three _))
  have hcardR : ((upper n).card : ℝ) ≤ (F.card : ℝ) + 3 := by exact_mod_cast hcard
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hS : (F.card : ℝ) / N ≤ longPrimeReciprocalSum N := by
    have e : (F.card : ℝ) / N = ∑ _p ∈ F, (1 : ℝ) / N := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, _, _⟩ := Finset.mem_filter.1 hp
    have h1' : p ≤ N := by have := Finset.mem_range.1 h1; omega
    exact one_div_le_one_div_of_le (by exact_mod_cast h2.pos) (by exact_mod_cast h1')
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2nN : (2 * (n : ℝ)) ≤ N := by
    have : 2 * n ≤ N := by omega
    exact_mod_cast this
  have hN2n : (N : ℝ) ≤ 2 * n + 1 := by
    have : N ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have hL0 : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hLN : Real.log (2 * n) ≤ Real.log N := Real.log_le_log (by linarith) h2nN
  have hc0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have h1 : 5 * (((upper n).card : ℝ) - 3) * Real.log (2 * n) ≤ 5 * (F.card : ℝ) * Real.log (2 * n) :=
    mul_le_mul_of_nonneg_right (by linarith) hL0.le
  have h2 : 5 * (F.card : ℝ) * Real.log (2 * n) ≤ 5 * (F.card : ℝ) * Real.log N :=
    mul_le_mul_of_nonneg_left hLN (by linarith)
  refine le_trans ?_ hS
  rw [div_le_div_iff₀ (by linarith) hNpos]
  linarith

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.long_prime_reciprocal_sum_le
