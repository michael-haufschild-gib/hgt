import GaloisForLFunctions.SignedSuccessorArithmetic.TheFloorReadsTheParityOfTheShift

/-!
# The shift floors are exact

The logarithmic agreement floor of completely multiplicative signs at lag `h` is determined for
`h = 2` and for every odd `h`.

* **Lag two: the floor is `1/4`.** Three signs `f(n), f(n+1), f(n+2)` always contain an agreeing
  pair, so `a(n) + a(n+1) + a₂(n) ≥ 1` (`one_le_agree_add_agree_add_agreeAt_two`). At odd positions
  this pays `1 − a(n) − a(n+1)`, at even positions the dilation gives `a₂(2m) = a(m)`. The two
  lower bounds `L₂ ≥ L₁/2` and `L₂ ≥ H/2 − L₁/2` add up to `2L₂ ≥ H/2`:
  `Σ_{n ≤ M, f(n) = f(n+2)} 1/n ≥ (1/4) log M − 2` (`lag_two_quarter_floor`). The successor floor
  is not used. The conductor-four twins attain it (`lag_two_floor_sharp`).
* **Odd shifts: the floor is `1/3`, attained at every odd shift by one sign.** The conductor-two
  twin `T(n) = (−1)^{v₂(n)}` (`twoTwin`) has zero lag-`h` doubling defect for every odd `h`
  (`agreeAt_mul_agreeAt_two_mul_twoTwin`): at an agreement of `n, n+h` the odd member forces the
  even one to have even valuation, and then `2n, 2n+h` disagree. Zero lag-`h` defect forces the
  density `1/3` (`logAgreeAt_le_of_zeroDefectAt`), so `T` attains the odd-shift floor at every odd
  `h` simultaneously, including the shifts divisible by `3` at which the conductor-three twins
  agree at two thirds of the steps (`odd_shift_floor_sharp`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-! ## Lag two -/

/-- Three signs contain an agreeing pair: `a(n) + a(n+1) + a₂(n) ≥ 1`. -/
theorem one_le_agree_add_agree_add_agreeAt_two (f : ℕ → ℤˣ) (n : ℕ) :
    1 ≤ agree f n + agree f (n + 1) + agreeAt f 2 n := by
  unfold agree agreeAt succSign shiftSign
  rw [show n + 1 + 1 = n + 2 by ring]
  rcases Int.units_eq_one_or (f n) with h0 | h0 <;>
    rcases Int.units_eq_one_or (f (n + 1)) with h1 | h1 <;>
    rcases Int.units_eq_one_or (f (n + 2)) with h2 | h2 <;>
    simp [h0, h1, h2]

/-- Splitting `[1, 2N+2]` into `1, 2` and the pairs `{2n+1, 2n+2}`. -/
theorem sum_Icc_two_mul_add_two (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Icc 1 (2 * N + 2), g k = g 1 + g 2 + ∑ n ∈ Icc 1 N, (g (2 * n + 1) + g (2 * n + 2)) := by
  induction N with
  | zero => simp [show Icc 1 2 = {1, 2} by rfl]
  | succ N ih =>
    rw [show 2 * (N + 1) + 2 = 2 * N + 2 + 1 + 1 by ring, sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]
    ring_nf

/-- `L(N + k) ≤ L(N) + k/(N+1)`. -/
theorem logAgree_add_le (f : ℕ → ℤˣ) (N k : ℕ) :
    logAgree f (N + k) ≤ logAgree f N + k / (N + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, logAgree, sum_Icc_succ_top (by omega), ← logAgree]
    have ha : (agree f (N + k + 1) : ℝ) ≤ 1 := by exact_mod_cast agree_le_one f _
    have h1 : (agree f (N + k + 1) : ℝ) / ((N + k + 1 : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
      calc (agree f (N + k + 1) : ℝ) / ((N + k + 1 : ℕ) : ℝ) ≤ 1 / ((N + k + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right ha (Nat.cast_nonneg _)
        _ ≤ 1 / ((N : ℝ) + 1) := div_le_div_of_nonneg_left zero_le_one (by positivity)
            (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
    push_cast at ih h1 ⊢
    have : ((k : ℝ) + 1) / ((N : ℝ) + 1) = k / (N + 1) + 1 / (N + 1) := by ring
    linarith

/-- `L₂(2N+1) ≥ H_N/4 − 7/4`. -/
theorem logAgreeAt_two_two_mul_add_one_ge (f : CMSign) (N : ℕ) :
    (harmonic N : ℝ) / 4 - 7 / 4 ≤ logAgreeAt f 2 (2 * N + 1) := by
  -- the split of `[1, 2N+1]` into `1` and the pairs `{2n, 2n+1}`
  have hsplit : logAgreeAt f 2 (2 * N + 1) = (agreeAt f 2 1 : ℝ) / ((1 : ℕ) : ℝ) +
      ∑ n ∈ Icc 1 N, ((agree f n : ℝ) / (2 * n) +
        (agreeAt f 2 (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) := by
    rw [logAgreeAt, sum_Icc_two_mul_add_one (fun k => (agreeAt f 2 k : ℝ) / k)]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [agreeAt_two_two_mul f (by simp at hn; omega)]
    push_cast; ring
  have heven : ∑ n ∈ Icc 1 N, (agree f n : ℝ) / (2 * n) = logAgree f N / 2 := by
    rw [logAgree, Finset.sum_div]
    exact sum_congr rfl fun n _ => by ring
  have h1 : (0 : ℝ) ≤ (agreeAt f 2 1 : ℝ) / ((1 : ℕ) : ℝ) := by positivity
  -- even positions: `L₂ ≥ L₁/2`
  have hE : logAgree f N / 2 ≤ logAgreeAt f 2 (2 * N + 1) := by
    rw [hsplit, sum_add_distrib, heven]
    have : (0 : ℝ) ≤ ∑ n ∈ Icc 1 N, (agreeAt f 2 (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) :=
      sum_nonneg fun n _ => by positivity
    linarith
  -- odd positions pay `1 − a(2n+1) − a(2n+2)`
  have hodd : ∀ n ∈ Icc 1 N, (1 : ℝ) / (2 * n) - 1 / (2 * (n * (n + 1))) -
      ((agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) +
        (agree f (2 * n + 2) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) - 1 / (n * (n + 1)) ≤
      (agreeAt f 2 (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have htri := one_le_agree_add_agree_add_agreeAt_two f (2 * n + 1)
    have htri' : (1 : ℝ) ≤ agree f (2 * n + 1) + agree f (2 * n + 2) + agreeAt f 2 (2 * n + 1) := by
      exact_mod_cast htri
    have hb : (agree f (2 * n + 2) : ℝ) ≤ 1 := by exact_mod_cast agree_le_one f _
    have hb0 : (0 : ℝ) ≤ agree f (2 * n + 2) := Nat.cast_nonneg _
    push_cast
    -- `1/(2n+1) ≥ 1/(2n) − 1/(2n(n+1))` and `b/(2n+1) ≤ b/(2n+2) + 1/(n(n+1))`
    have e1 : (1 : ℝ) / (2 * n) - 1 / (2 * (n * (n + 1))) ≤ 1 / (2 * n + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    have e2 : (agree f (2 * n + 2) : ℝ) / (2 * n + 1) ≤
        (agree f (2 * n + 2) : ℝ) / (2 * n + 2) + 1 / (n * (n + 1)) := by
      have hid : (agree f (2 * n + 2) : ℝ) / (2 * n + 1) - (agree f (2 * n + 2) : ℝ) / (2 * n + 2) =
          (agree f (2 * n + 2) : ℝ) / ((2 * n + 1) * (2 * n + 2)) := by
        field_simp; ring
      have hle : (agree f (2 * n + 2) : ℝ) / ((2 * n + 1) * (2 * n + 2)) ≤ 1 / (n * (n + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (agree f (2 * n + 2) : ℝ) * (n * (n + 1)) ≤ 1 * (n * (n + 1)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
        nlinarith
      linarith
    have e3 : (1 : ℝ) / (2 * n + 1) ≤ ((agree f (2 * n + 1) : ℝ) + agree f (2 * n + 2) +
        agreeAt f 2 (2 * n + 1)) / (2 * n + 1) :=
      div_le_div_of_nonneg_right htri' (by positivity)
    rw [add_div, add_div] at e3
    linarith
  have hsumO := sum_le_sum hodd
  -- the odd-position sums against `H_N` and `L₁(2N+2)`
  have hlin : ∑ n ∈ Icc 1 N, ((1 : ℝ) / (2 * n) - 1 / (2 * (n * (n + 1))) -
      ((agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) +
        (agree f (2 * n + 2) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) - 1 / (n * (n + 1))) =
      (harmonic N : ℝ) / 2 - (3 / 2) * ∑ n ∈ Icc 1 N, (1 : ℝ) / (n * (n + 1)) -
        ∑ n ∈ Icc 1 N, ((agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) +
          (agree f (2 * n + 2) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) := by
    rw [harmonic_eq_sum, Finset.sum_div, Finset.mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have : (n : ℝ) ≠ 0 := by have := (mem_Icc.mp hn).1; positivity
    field_simp; ring
  have htel := sum_inv_mul_succ_le N
  have hpos : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hL22 : ∑ n ∈ Icc 1 N, ((agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) +
      (agree f (2 * n + 2) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) ≤ logAgree f (2 * N + 2) := by
    rw [logAgree, sum_Icc_two_mul_add_two (fun k => (agree f k : ℝ) / k)]
    have : (0 : ℝ) ≤ (agree f 1 : ℝ) / ((1 : ℕ) : ℝ) + (agree f 2 : ℝ) / ((2 : ℕ) : ℝ) := by
      positivity
    linarith
  have hgrow := logAgree_add_le f N (N + 2)
  rw [show N + (N + 2) = 2 * N + 2 by ring] at hgrow
  have hfrac : ((N + 2 : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hO : (harmonic N : ℝ) / 2 - logAgree f N / 2 - 7 / 2 ≤ logAgreeAt f 2 (2 * N + 1) := by
    rw [hsplit, sum_add_distrib, heven]
    linarith
  linarith

/-- **The lag-two floor is one quarter.** For every completely multiplicative sign,
`Σ_{n ≤ M, f(n) = f(n+2)} 1/n ≥ (1/4) log M − 2`. -/
theorem lag_two_quarter_floor (f : CMSign) {M : ℕ} (hM : 0 < M) :
    Real.log M / 4 - 2 ≤ logAgreeAt f 2 M := by
  set N := (M - 1) / 2 with hN
  have hle : 2 * N + 1 ≤ M := by omega
  have hbase := logAgreeAt_two_two_mul_add_one_ge f N
  have hmono := logAgreeAt_mono f 2 hle
  have hH := log_add_one_le_harmonic N
  have hM2 : (M : ℝ) ≤ 2 * ((N + 1 : ℕ) : ℝ) := by
    have : M ≤ 2 * (N + 1) := by omega
    exact_mod_cast this
  have hlog : Real.log M ≤ Real.log 2 + Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by exact_mod_cast hM) hM2
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith
  linarith

/-- **The lag-two floor is exactly `1/4`.** Every sign has lag-two mass at least
`(1/4) log M − 2`, and the conductor-four twins have at most `(1/4) log M + 1`. -/
theorem lag_two_floor_sharp :
    (∀ f : CMSign, ∀ M : ℕ, 0 < M → Real.log M / 4 - 2 ≤ logAgreeAt f 2 M) ∧
      ∀ δ : ℤˣ, ∀ M : ℕ, 0 < M → logAgreeAt (chi4Twin δ) 2 M ≤ Real.log M / 4 + 1 :=
  ⟨fun f _ hM => lag_two_quarter_floor f hM, fun δ _ hM => chi4Twin_lag_two_log_le δ hM⟩

/-! ## Odd shifts: the conductor-two twin -/

/-- Zero lag-`h` doubling defect: `n, n+h` and `2n, 2n+h` never agree together. -/
def ZeroDefectAt (f : ℕ → ℤˣ) (h : ℕ) : Prop :=
  ∀ n, 0 < n → agreeAt f h n * agreeAt f h (2 * n) = 0

/-- For odd `h`, every `k ∈ [h+1, 2N]` is a position `2n` or `2n + h` with `1 ≤ n ≤ N`. -/
theorem sum_Icc_le_sum_two_mul_add {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {h : ℕ} (hodd : Odd h)
    (N : ℕ) :
    ∑ k ∈ Icc (h + 1) (2 * N), g k ≤ ∑ n ∈ Icc 1 N, (g (2 * n) + g (2 * n + h)) := by
  rw [sum_add_distrib]
  have hinj1 : Set.InjOn (fun n => 2 * n) (Icc 1 N : Finset ℕ) := fun a _ b _ hab => by
    simp only at hab; omega
  have hinj2 : Set.InjOn (fun n => 2 * n + h) (Icc 1 N : Finset ℕ) := fun a _ b _ hab => by
    simp only at hab; omega
  obtain ⟨c, rfl⟩ := hodd
  rw [← sum_image (f := g) hinj1, ← sum_image (f := g) hinj2, ← sum_union]
  · refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hg k
    intro k hk
    simp only [mem_union, mem_image, mem_Icc] at hk ⊢
    rcases Nat.even_or_odd k with ⟨d, hd⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨d, by omega, by omega⟩
    · exact Or.inr ⟨d - c, by omega, by omega⟩
  · rw [disjoint_left]
    intro k hk1 hk2
    simp only [mem_image] at hk1 hk2
    obtain ⟨a, _, rfl⟩ := hk1
    obtain ⟨b, _, hb⟩ := hk2
    omega

/-- **Zero lag-`h` defect forces the density `1/3`.** For odd `h`, a sign with zero lag-`h`
doubling defect has `L_h(N) ≤ H_N/3 + h`. -/
theorem logAgreeAt_le_of_zeroDefectAt (f : CMSign) {h : ℕ} (hodd : Odd h)
    (hz : ZeroDefectAt f h) (N : ℕ) :
    logAgreeAt f h N ≤ (harmonic N : ℝ) / 3 + h := by
  -- the per-step identity: `a(2n) + a(2n+h) = 1 − a(n)`
  have hstep : ∀ n, 0 < n →
      (agreeAt f h (2 * n) : ℝ) + agreeAt f h (2 * n + h) = 1 - agreeAt f h n := by
    intro n hn
    have e := agreeAt_doubling f h hn
    rw [hz n hn, mul_zero, add_zero] at e
    have : ((agreeAt f h (2 * n) + agreeAt f h (2 * n + h) + agreeAt f h n : ℕ) : ℝ) =
        (1 : ℕ) := by rw [e]
    push_cast at this; linarith
  -- the positions `2n, 2n+h` carry at most `(H_N − L_h(N))/2`
  have hpairs : ∑ n ∈ Icc 1 N, ((agreeAt f h (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) +
      (agreeAt f h (2 * n + h) : ℝ) / ((2 * n + h : ℕ) : ℝ)) ≤
      ((harmonic N : ℝ) - logAgreeAt f h N) / 2 := by
    have hle : ∀ n ∈ Icc 1 N, (agreeAt f h (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) +
        (agreeAt f h (2 * n + h) : ℝ) / ((2 * n + h : ℕ) : ℝ) ≤
        (1 - (agreeAt f h n : ℝ)) / (2 * n) := by
      intro n hn
      have hn1 : 0 < n := (mem_Icc.mp hn).1
      have hb : (0 : ℝ) ≤ agreeAt f h (2 * n + h) := Nat.cast_nonneg _
      push_cast
      have : (agreeAt f h (2 * n + h) : ℝ) / (2 * n + h) ≤ (agreeAt f h (2 * n + h) : ℝ) / (2 * n) :=
        div_le_div_of_nonneg_left hb (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) h])
      rw [← hstep n hn1, add_div]
      linarith
    refine (sum_le_sum hle).trans (le_of_eq ?_)
    rw [harmonic_eq_sum, logAgreeAt, ← sum_sub_distrib, sum_div]
    exact sum_congr rfl fun n _ => by ring
  -- they cover `[h+1, 2N] ⊇ [h+1, N]`, and `[1, h]` costs at most `h`
  have hcover := sum_Icc_le_sum_two_mul_add (g := fun k => (agreeAt f h k : ℝ) / k)
    (fun k => by positivity) hodd N
  have hlow : logAgreeAt f h N ≤ h + ∑ k ∈ Icc (h + 1) (2 * N), (agreeAt f h k : ℝ) / k := by
    rw [logAgreeAt, ← sum_filter_add_sum_filter_not (Icc 1 N) (fun k => k ≤ h)]
    have h1 : ∑ k ∈ (Icc 1 N).filter (fun k => k ≤ h), (agreeAt f h k : ℝ) / k ≤ h := by
      calc ∑ k ∈ (Icc 1 N).filter (fun k => k ≤ h), (agreeAt f h k : ℝ) / k
          ≤ ∑ k ∈ (Icc 1 N).filter (fun k => k ≤ h), (1 : ℝ) := by
            refine sum_le_sum fun k hk => ?_
            simp only [mem_filter, mem_Icc] at hk
            rw [div_le_one (by exact_mod_cast hk.1.1)]
            have : (agreeAt f h k : ℝ) ≤ 1 := by exact_mod_cast agreeAt_le_one f h k
            have : (1 : ℝ) ≤ k := by exact_mod_cast hk.1.1
            linarith
        _ = ((Icc 1 N).filter (fun k => k ≤ h)).card := by simp
        _ ≤ h := by
            have : ((Icc 1 N).filter (fun k => k ≤ h)).card ≤ (Icc 1 h).card :=
              card_le_card fun k hk => by simp only [mem_filter, mem_Icc] at hk ⊢; omega
            simp only [Nat.card_Icc, add_tsub_cancel_right] at this
            exact_mod_cast this
    have h2 : ∑ k ∈ (Icc 1 N).filter (fun k => ¬ k ≤ h), (agreeAt f h k : ℝ) / k ≤
        ∑ k ∈ Icc (h + 1) (2 * N), (agreeAt f h k : ℝ) / k :=
      sum_le_sum_of_subset_of_nonneg (fun k hk => by
        simp only [mem_filter, mem_Icc] at hk ⊢; omega) fun k _ _ => by positivity
    linarith
  push_cast at hcover hpairs
  have hH0 : (0 : ℝ) ≤ harmonic N := by
    rw [harmonic_eq_sum]; exact sum_nonneg fun n _ => by positivity
  linarith

/-- The conductor-two twin `T(n) = (−1)^{v₂(n)}`: the principal character modulo `2` with value
`−1` at `2`. -/
def twoTwin : CMSign where
  toFun n := (-1) ^ n.factorization 2
  map_one' := by simp
  map_mul' := fun {m n} hm hn => by
    rw [Nat.factorization_mul hm.ne' hn.ne']
    exact pow_add _ _ _

theorem twoTwin_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) : twoTwin n = 1 := by
  change (-1 : ℤˣ) ^ n.factorization 2 = 1
  rw [Nat.factorization_eq_zero_of_not_dvd hn]
  exact pow_zero _

theorem twoTwin_two : twoTwin 2 = -1 := by
  change (-1 : ℤˣ) ^ (2 : ℕ).factorization 2 = -1
  rw [Nat.Prime.factorization_self Nat.prime_two]
  exact pow_one _

theorem twoTwin_two_mul {n : ℕ} (hn : 0 < n) : twoTwin (2 * n) = -twoTwin n := by
  rw [twoTwin.map_mul two_pos hn, twoTwin_two, neg_one_mul]

/-- The conductor-two twin is `1` at every odd prime. -/
theorem twoTwin_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : twoTwin p = 1 :=
  twoTwin_of_odd fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

/-- **The conductor-two twin has zero lag-`h` doubling defect for every odd `h`.** -/
theorem agreeAt_mul_agreeAt_two_mul_twoTwin {h : ℕ} (hodd : Odd h) :
    ZeroDefectAt twoTwin h := by
  intro n hn
  -- `a_h(2n) = [T(n) = −1]`, since `2n + h` is odd
  have h2n : agreeAt twoTwin h (2 * n) = if twoTwin n = -1 then 1 else 0 := by
    have hodd2 : ¬ 2 ∣ 2 * n + h := by obtain ⟨c, rfl⟩ := hodd; omega
    unfold agreeAt shiftSign
    rw [twoTwin_two_mul hn, twoTwin_of_odd hodd2, mul_one]
    rcases Int.units_eq_one_or (twoTwin n) with e | e <;> simp [e]
  rw [h2n]
  rcases Nat.even_or_odd n with ⟨c, hc⟩ | hn2
  · -- `n` even: `n + h` is odd, so an agreement forces `T(n) = 1`
    have hodd3 : ¬ 2 ∣ n + h := by obtain ⟨d, rfl⟩ := hodd; omega
    unfold agreeAt shiftSign
    rw [twoTwin_of_odd hodd3, mul_one]
    rcases Int.units_eq_one_or (twoTwin n) with e | e <;> simp [e]
  · -- `n` odd: `T(n) = 1`
    rw [twoTwin_of_odd (by obtain ⟨c, rfl⟩ := hn2; omega)]
    simp

/-- The conductor-two twin has lag-`h` mass at most `(1/3) log M + h + 1` for every odd `h`. -/
theorem twoTwin_odd_shift_log_le {h : ℕ} (hodd : Odd h) (M : ℕ) :
    logAgreeAt twoTwin h M ≤ Real.log M / 3 + h + 1 := by
  have h1 := logAgreeAt_le_of_zeroDefectAt twoTwin hodd (agreeAt_mul_agreeAt_two_mul_twoTwin hodd) M
  have h2 := harmonic_le_one_add_log M
  linarith

/-- **Every odd shift has floor exactly `1/3`, attained by one sign.** Every completely
multiplicative sign has lag-`h` mass at least `(1/3) log M − (h+1)`, and the conductor-two twin has
at most `(1/3) log M + h + 1`, for every odd `h` at once. -/
theorem odd_shift_floor_sharp :
    (∀ h : ℕ, Odd h → ∀ f : CMSign, ∀ M : ℕ, 0 < M →
        Real.log M / 3 - (h + 1) ≤ logAgreeAt f h M) ∧
      ∀ h : ℕ, Odd h → ∀ M : ℕ, logAgreeAt twoTwin h M ≤ Real.log M / 3 + h + 1 :=
  ⟨fun _ hodd f _ hM => odd_shift_log_floor f hodd hM,
    fun _ hodd M => twoTwin_odd_shift_log_le hodd M⟩

end GaloisForLFunctions.SignedSuccessorArithmetic
