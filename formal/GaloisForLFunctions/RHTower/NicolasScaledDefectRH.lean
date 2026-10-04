import GaloisForLFunctions.RHTower.PrimeLagLowerBoundRH

/-!
# Nicolas's constant is `2 + a₁`

Let `Nic(x) = -log ∏_{p ≤ x}(1 - 1/p) - γ - log log θ(x)` be the Nicolas defect.  Under the Riemann
hypothesis

```text
Nic(x) √x log x - Φ(log x) → 2,
```

where `Φ(L) = Σ_ρ e^{L(ρ-1/2)}/(ρ(1-ρ))` is the lag function.  The `2` is the sum of two unit
contributions: the prime squares, `(ψ(x) - θ(x))/√x → 1`, and the prime tails of the Euler product,
`(P(x) - A(x)) √x log x → 1`, which come from `Σ_{√x < p ≤ x} 1/(2p²)`.  Since
`|Φ| ≤ a₁ = 2 + γ - log 4π`
under RH and `Φ(log p) > a₁ - ε` for infinitely many primes (unconditionally), the limit superior of
`Nic(p)√p log p` along primes is `2 + a₁`: Nicolas's constant `2 + β` is two plus the sharp lag
ceiling.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The prime tails -/

/-- `Σ_{a < n ≤ b} 1/n³ ≤ 1/(2a²)` for `a ≥ 1`. -/
theorem sum_Ioc_inv_cube_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℝ) ^ 3 ≤ 1 / (2 * (a : ℝ) ^ 2) := by
  have key : ∀ b : ℕ, ∑ n ∈ Finset.Ioc a b, 1 / (n : ℝ) ^ 3
      ≤ 1 / (2 * (a : ℝ) ^ 2) - 1 / (2 * (max a b : ℝ) ^ 2) := by
    intro b
    induction b with
    | zero =>
      simp
    | succ b ih =>
      rcases Nat.lt_or_ge b a with h | h
      · have hb1 : b + 1 ≤ a := h
        rw [Finset.Ioc_eq_empty_of_le hb1, Finset.sum_empty]
        have : max (a : ℝ) ((b + 1 : ℕ) : ℝ) = a := max_eq_left (by exact_mod_cast hb1)
        rw [this]; simp
      · rw [Finset.sum_Ioc_succ_top (by omega)]
        have hmax1 : max (a : ℝ) (b : ℝ) = b := max_eq_right (by exact_mod_cast h)
        have hab : (a : ℝ) ≤ b := by exact_mod_cast h
        have hmax2 : max (a : ℝ) ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by
          push_cast; exact max_eq_right (by linarith)
        rw [hmax1] at ih
        rw [hmax2]
        have hb : (1 : ℝ) ≤ b := by exact_mod_cast (le_trans ha h)
        have hstep : 1 / ((b + 1 : ℕ) : ℝ) ^ 3
            ≤ 1 / (2 * (b : ℝ) ^ 2) - 1 / (2 * ((b : ℝ) + 1) ^ 2) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith [sq_nonneg (b : ℝ), mul_pos (by linarith : (0 : ℝ) < b)
            (by linarith : (0 : ℝ) < b + 1)]
        linarith
  refine (key b).trans ?_
  have : 0 ≤ 1 / (2 * (max a b : ℝ) ^ 2) := by positivity
  linarith

/-- For a prime `p ∈ (√x, ⌊x⌋]`: `0 ≤ t_p - 1/(2p²) ≤ 2/(3p³)`. -/
theorem mertensPrimeTail_large_mem {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime) (hpN : p ≤ ⌊x⌋₊)
    (hpx : Real.sqrt x < p) :
    0 ≤ mertensPrimeTail ⌊x⌋₊ p - 1 / (2 * (p : ℝ) ^ 2) ∧
      mertensPrimeTail ⌊x⌋₊ p - 1 / (2 * (p : ℝ) ^ 2) ≤ 2 / (3 * (p : ℝ) ^ 3) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : Nat.log p ⌊x⌋₊ = 1 := by
    rw [Nat.log_eq_one_iff]
    refine ⟨?_, hp.one_lt, hpN⟩
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h2 : x < (p : ℝ) * p := by
      have := Real.sqrt_lt' hp0 |>.mp hpx
      nlinarith
    exact_mod_cast (show (⌊x⌋₊ : ℝ) < p * p by linarith)
  obtain ⟨h0, h1⟩ := log_one_sub_inv_tail_mem hp.two_le 2
  have hsum2 : ∑ k ∈ Finset.Icc (1 : ℕ) 2, 1 / ((k : ℝ) * (p : ℝ) ^ k)
      = 1 / (p : ℝ) + 1 / (2 * (p : ℝ) ^ 2) := by
    rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.sum_pair (by norm_num)]
    push_cast; ring
  have hsum1 : ∑ k ∈ Finset.Icc (1 : ℕ) 1, 1 / ((k : ℝ) * (p : ℝ) ^ k) = 1 / (p : ℝ) := by
    simp
  unfold mertensPrimeTail
  rw [hlog, hsum1]
  rw [hsum2] at h0 h1
  push_cast at h1
  constructor
  · linarith
  · have : 2 / ((2 + 1) * (p : ℝ) ^ (2 + 1)) = 2 / (3 * (p : ℝ) ^ 3) := by norm_num
    linarith

/-- For a prime `p` with `p² ≤ x < p³`: `t_p ≤ 2/(3p³)`. -/
theorem mertensPrimeTail_mid_le {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime)
    (hp2 : (p : ℝ) ^ 2 ≤ x) (hp3 : x < (p : ℝ) ^ 3) :
    mertensPrimeTail ⌊x⌋₊ p ≤ 2 / (3 * (p : ℝ) ^ 3) := by
  have hlog : Nat.log p ⌊x⌋₊ = 2 := by
    rw [Nat.log_eq_iff (Or.inl (by norm_num))]
    constructor
    · exact Nat.le_floor (by push_cast; exact hp2)
    · have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      exact_mod_cast (show (⌊x⌋₊ : ℝ) < (p : ℝ) ^ (2 + 1) by norm_num; linarith)
  obtain ⟨_, h1⟩ := log_one_sub_inv_tail_mem hp.two_le 2
  unfold mertensPrimeTail
  rw [hlog]
  have : 2 / (((2 : ℕ) : ℝ) + 1) / (p : ℝ) ^ (2 + 1) = 2 / (3 * (p : ℝ) ^ 3) := by
    norm_num; ring
  have e : 2 / ((((2 : ℕ) : ℝ) + 1) * (p : ℝ) ^ (2 + 1)) = 2 / (3 * (p : ℝ) ^ 3) := by norm_num
  linarith


/-- **The prime tails are carried by `(√x, x]`.**  With `c = x^{1/3} ≥ 4`:
`Σ_{√x<p≤x} 1/(2p²) ≤ Σ_{p≤x} t_p ≤ Σ_{√x<p≤x} 1/(2p²) + 7/c²`. -/
theorem sum_mertensPrimeTail_mem {x : ℝ} (hx : 64 ≤ x) :
    ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
        1 / (2 * (p : ℝ) ^ 2)
      ≤ ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, mertensPrimeTail ⌊x⌋₊ p ∧
    ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, mertensPrimeTail ⌊x⌋₊ p
      ≤ ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
          1 / (2 * (p : ℝ) ^ 2) + 7 / (x ^ (1 / 3 : ℝ)) ^ 2 := by
  set S := (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime with hS
  set c := x ^ (1 / 3 : ℝ) with hc
  have hx0 : 0 < x := by linarith
  have hc3 : c ^ 3 = x := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hc4 : 4 ≤ c := by
    by_contra h
    have : c ^ 3 < 4 ^ 3 := pow_lt_pow_left₀ (not_le.mp h) (by positivity) (by norm_num)
    linarith
  have hc0 : 0 < c := by linarith
  have hmem : ∀ p ∈ S, p.Prime ∧ p ≤ ⌊x⌋₊ := fun p hp => by
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hp; exact ⟨hp.2, hp.1.2⟩
  have hnn : ∀ p ∈ S, 0 ≤ mertensPrimeTail ⌊x⌋₊ p := fun p hp =>
    (mertensPrimeTail_bounds (by linarith) (hmem p hp).1 (hmem p hp).2).1
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => Real.sqrt x < p)]
  -- large primes
  have hlarge : ∀ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p),
      0 ≤ mertensPrimeTail ⌊x⌋₊ p - 1 / (2 * (p : ℝ) ^ 2) ∧
        mertensPrimeTail ⌊x⌋₊ p - 1 / (2 * (p : ℝ) ^ 2) ≤ 2 / (3 * (p : ℝ) ^ 3) := by
    intro p hp
    obtain ⟨hpS, hpx⟩ := Finset.mem_filter.mp hp
    exact mertensPrimeTail_large_mem (by linarith) (hmem p hpS).1 (hmem p hpS).2 hpx
  have hsx : 8 ≤ Real.sqrt x := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  set a := ⌊Real.sqrt x⌋₊ with ha
  have ha1 : (Real.sqrt x) / 2 ≤ (a : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt x); rw [← ha] at this; linarith
  have ha1' : 1 ≤ a := by
    have : (1 : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hcube_large : ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p), 1 / (p : ℝ) ^ 3
      ≤ 4 / x := by
    have hsub : S.filter (fun p : ℕ => Real.sqrt x < p) ⊆ Finset.Ioc a ⌊x⌋₊ := by
      intro p hp
      obtain ⟨hpS, hpx⟩ := Finset.mem_filter.mp hp
      simp only [Finset.mem_Ioc]
      refine ⟨?_, (hmem p hpS).2⟩
      have := Nat.floor_le (Real.sqrt_nonneg x)
      rw [← ha] at this
      exact_mod_cast (lt_of_le_of_lt this hpx)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans ?_
    refine (sum_Ioc_inv_cube_le ha1' _).trans ?_
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    rw [div_le_div_iff₀ (by positivity) hx0]
    nlinarith
  have hL : ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p), mertensPrimeTail ⌊x⌋₊ p
      ≤ ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p), 1 / (2 * (p : ℝ) ^ 2) + 4 / (3 * c ^ 2) := by
    have h1 : ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p), mertensPrimeTail ⌊x⌋₊ p
        ≤ ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p),
          (1 / (2 * (p : ℝ) ^ 2) + 2 / 3 * (1 / (p : ℝ) ^ 3)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have := (hlarge p hp).2
      have e : 2 / (3 * (p : ℝ) ^ 3) = 2 / 3 * (1 / (p : ℝ) ^ 3) := by ring
      linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    have hxc : 4 / x ≤ 2 / c ^ 2 := by
      rw [← hc3, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left (hcube_large.trans hxc) (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have e : 2 / 3 * (2 / c ^ 2) = 4 / (3 * c ^ 2) := by field_simp; ring
    linarith
  have hLlow : ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p), 1 / (2 * (p : ℝ) ^ 2)
      ≤ ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt x < p), mertensPrimeTail ⌊x⌋₊ p :=
    Finset.sum_le_sum fun p hp => by linarith [(hlarge p hp).1]
  -- small and middle primes
  have hsmallnn : 0 ≤ ∑ p ∈ S.filter (fun p : ℕ => ¬ Real.sqrt x < p), mertensPrimeTail ⌊x⌋₊ p :=
    Finset.sum_nonneg fun p hp => hnn p (Finset.mem_filter.mp hp).1
  set b := ⌊c⌋₊ with hb
  have hb1 : c / 2 ≤ (b : ℝ) := by
    have := Nat.lt_floor_add_one c; rw [← hb] at this; linarith
  have hb1' : 1 ≤ b := by
    have : (1 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  have hsmall : ∑ p ∈ S.filter (fun p : ℕ => ¬ Real.sqrt x < p), mertensPrimeTail ⌊x⌋₊ p
      ≤ 4 / c ^ 2 + 4 / (3 * c ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ => (p : ℝ) ^ 3 ≤ x)]
    -- `p³ ≤ x`: each tail at most `2/x`, at most `c + 1` of them
    have h1 : ∑ p ∈ (S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
        (fun p : ℕ => (p : ℝ) ^ 3 ≤ x), mertensPrimeTail ⌊x⌋₊ p ≤ 4 / c ^ 2 := by
      have hsub : (S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
          (fun p : ℕ => (p : ℝ) ^ 3 ≤ x) ⊆ Finset.Icc 0 b := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        simp only [Finset.mem_Icc, Nat.zero_le, true_and]
        apply Nat.le_floor
        by_contra h
        have : c ^ 3 < (p : ℝ) ^ 3 := pow_lt_pow_left₀ (not_le.mp h) hc0.le (by norm_num)
        linarith [hp.2]
      have hle : ∀ p ∈ (S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
          (fun p : ℕ => (p : ℝ) ^ 3 ≤ x), mertensPrimeTail ⌊x⌋₊ p ≤ 2 / x := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨hpr, hpN⟩ := hmem p hp.1.1
        have h := (mertensPrimeTail_bounds (by linarith) hpr hpN).2.1
        have hlp : Real.log p ≤ Real.log x := Real.log_le_log (by exact_mod_cast hpr.pos)
          (le_trans (by exact_mod_cast hpN) (Nat.floor_le hx0.le))
        have hlx : 0 < Real.log x := Real.log_pos (by linarith)
        refine h.trans ?_
        rw [div_le_div_iff₀ (by positivity) hx0]
        nlinarith
      refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
      rw [nsmul_eq_mul]
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.sub_zero] at hcard
      have hcard' : ((((S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
          (fun p : ℕ => (p : ℝ) ^ 3 ≤ x)).card : ℕ) : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast hcard
      have hbc : (b : ℝ) ≤ c := Nat.floor_le hc0.le
      have h2x : 0 ≤ 2 / x := by positivity
      calc _ ≤ ((b : ℝ) + 1) * (2 / x) := mul_le_mul_of_nonneg_right hcard' h2x
        _ ≤ (c + c) * (2 / x) := mul_le_mul_of_nonneg_right (by linarith) h2x
        _ = 4 / c ^ 2 := by rw [← hc3]; field_simp; ring
    -- `x < p³`, `p ≤ √x`: tails at most `2/(3p³)`
    have h2 : ∑ p ∈ (S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
        (fun p : ℕ => ¬ (p : ℝ) ^ 3 ≤ x), mertensPrimeTail ⌊x⌋₊ p ≤ 4 / (3 * c ^ 2) := by
      have hle : ∀ p ∈ (S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
          (fun p : ℕ => ¬ (p : ℝ) ^ 3 ≤ x),
            mertensPrimeTail ⌊x⌋₊ p ≤ 2 / 3 * (1 / (p : ℝ) ^ 3) := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨hpr, _⟩ := hmem p hp.1.1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
        have hp2 : (p : ℝ) ^ 2 ≤ x := by
          have := not_lt.mp hp.1.2
          have h := Real.sqrt_le_sqrt (sq_nonneg (p : ℝ))
          rw [Real.sqrt_sq hp0.le] at h
          nlinarith [Real.sq_sqrt hx0.le]
        have := mertensPrimeTail_mid_le (by linarith) hpr hp2 (not_le.mp hp.2)
        have e : 2 / (3 * (p : ℝ) ^ 3) = 2 / 3 * (1 / (p : ℝ) ^ 3) := by ring
        linarith
      refine (Finset.sum_le_sum hle).trans ?_
      rw [← Finset.mul_sum]
      have hsub : (S.filter (fun p : ℕ => ¬ Real.sqrt x < p)).filter
          (fun p : ℕ => ¬ (p : ℝ) ^ 3 ≤ x) ⊆ Finset.Ioc b ⌊x⌋₊ := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        simp only [Finset.mem_Ioc]
        refine ⟨?_, (hmem p hp.1.1).2⟩
        by_contra h
        have hpb : (p : ℝ) ≤ b := by exact_mod_cast not_lt.mp h
        have hbc : (b : ℝ) ≤ c := Nat.floor_le hc0.le
        have : (p : ℝ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) (hpb.trans hbc) 3
        exact hp.2 (by linarith)
      have h3 := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans
        (sum_Ioc_inv_cube_le hb1' ⌊x⌋₊)
      have h4 : 1 / (2 * (b : ℝ) ^ 2) ≤ 2 / c ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) (by norm_num : (0 : ℝ) ≤ 2 / 3)
      have e : 2 / 3 * (2 / c ^ 2) = 4 / (3 * c ^ 2) := by field_simp; ring
      linarith
    linarith
  constructor
  · linarith
  · have e : 7 / c ^ 2 = 4 / c ^ 2 + 4 / (3 * c ^ 2) + 4 / (3 * c ^ 2) + 1 / (3 * c ^ 2) := by
      field_simp; ring
    have : 0 ≤ 1 / (3 * c ^ 2) := by positivity
    linarith


/-! ## Prime squares beyond `√x` -/

/-- Von Koch for `θ`: under RH, `|θ(t) - t| ≤ K √t log² t` for `t ≥ 16`. -/
theorem exists_abs_theta_sub_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 16 ≤ t →
      |Chebyshev.theta t - t| ≤ K * Real.sqrt t * Real.log t ^ 2 := by
  set K₀ := 200 * (xiLineTwoLogDerivConstant + 2) with hK₀
  have hK00 : 0 ≤ K₀ := by
    have := (abs_nonneg _).trans (abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH
      (le_refl (16 : ℝ)))
    have h16 : 0 < Real.sqrt 16 * Real.log 16 ^ 2 := by
      have : 0 < Real.log 16 := Real.log_pos (by norm_num)
      positivity
    rw [mul_assoc] at this
    exact nonneg_of_mul_nonneg_left this h16
  refine ⟨K₀ + 2, by linarith, fun t ht => ?_⟩
  have h1 := abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH ht
  rw [← hK₀] at h1
  have h2 := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ t)
  have h3 := Chebyshev.theta_le_psi t
  have hl : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hs := Real.sqrt_nonneg t
  have h4 : 2 * Real.sqrt t * Real.log t ≤ 2 * Real.sqrt t * Real.log t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t * Real.log t)
    nlinarith
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith

/-- The weight `f(t) = 1/(t² log t)` and its derivative for `t > 1`. -/
theorem hasDerivAt_inv_sq_mul_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => 1 / (t ^ 2 * Real.log t))
      (-((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 * Real.log t)
      ((2 : ℕ) * t ^ (2 - 1) * Real.log t + t ^ 2 * t⁻¹) t :=
    (hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht0)
  have h2 := h1.inv (mul_ne_zero (pow_ne_zero 2 ht0) hl)
  simp only [one_div]
  refine h2.congr_deriv ?_
  field_simp
  ring


/-- **Abel summation for prime squares.**  For `2 ≤ y ≤ x`,
`Σ_{y<p≤x} 1/p² = θ(x)/(x² log x) - θ(y)/(y² log y) + ∫_y^x θ(t)(2 log t + 1)/(t³ log² t) dt`. -/
theorem sum_prime_inv_sq_eq_abel {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, 1 / ((n : ℝ) ^ 2 * Real.log n) * (if n.Prime then Real.log n else 0)
      = Chebyshev.theta x / (x ^ 2 * Real.log x) - Chebyshev.theta y / (y ^ 2 * Real.log y)
        + ∫ t in y..x, Chebyshev.theta t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
  have hd : ∀ t ∈ Icc y x, HasDerivAt (fun t : ℝ => 1 / (t ^ 2 * Real.log t))
      (-((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))) t :=
    fun t ht => hasDerivAt_inv_sq_mul_log (by linarith [ht.1])
  have hcont : ContinuousOn (fun t : ℝ => -((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
      (Icc y x) := by
    refine ((continuousOn_const.mul (Real.continuousOn_log.mono ?_)).add continuousOn_const
      |>.div ((continuousOn_id.pow 3).mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_).neg
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
    · intro t ht
      have h1 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have h2 : 0 < t := by linarith [ht.1]
      exact mul_ne_zero (pow_ne_zero 3 h2.ne') (pow_ne_zero 2 h1.ne')
  have hint : IntegrableOn (deriv fun t : ℝ => 1 / (t ^ 2 * Real.log t)) (Icc y x) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (c := fun n => if n.Prime then Real.log n else 0)
    (f := fun t : ℝ => 1 / (t ^ 2 * Real.log t)) (by linarith) hyx
    (fun t ht => (hd t ht).differentiableAt) hint
  have hθ : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0)
      = Chebyshev.theta t := fun t => by rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [hθ] at h
  rw [h]
  have hcongr : ∫ t in Ioc y x, deriv (fun t : ℝ => 1 / (t ^ 2 * Real.log t)) t
        * Chebyshev.theta t
      = -∫ t in y..x, Chebyshev.theta t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
    rw [intervalIntegral.integral_of_le hyx, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    ring
  rw [hcongr]
  field_simp
  ring

/-- The prime-square sum over `(y, x]` as a filtered prime sum. -/
theorem sum_filter_prime_inv_sq_eq {x y : ℝ} (hy : 0 ≤ y) :
    ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => y < p), 1 / (p : ℝ) ^ 2
      = ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊,
          1 / ((n : ℝ) ^ 2 * Real.log n) * (if n.Prime then Real.log n else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  rw [← Finset.sum_subset (s₁ := Finset.Ioc ⌊y⌋₊ ⌊x⌋₊) (s₂ := Finset.Icc 0 ⌊x⌋₊)
    (fun n hn => by simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Ioc] at hn
    have hyn : y < n := (Nat.floor_lt hy).mp hn.1
    by_cases hp : n.Prime
    · have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp only [hp, if_true, hyn]
      field_simp
    · simp [hp]
  · intro n hn hn'
    simp only [Finset.mem_Ioc, Finset.mem_Icc, not_and, not_le] at hn hn'
    have : ¬ y < n := by
      intro h
      have := hn' ((Nat.floor_lt hy).mpr h)
      omega
    simp [this]


theorem one_le_log_of_sixteen_le {t : ℝ} (ht : 16 ≤ t) : 1 ≤ Real.log t := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- `∫_y^x dt/(t²√t) ≤ (2/3)/(y√y)` for `0 < y ≤ x`. -/
theorem integral_inv_sq_mul_sqrt_le_two_thirds {y x : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    ∫ t in y..x, 1 / (t ^ 2 * Real.sqrt t) ≤ 2 / 3 * (1 / (y * Real.sqrt y)) := by
  have hpos : ∀ t ∈ uIcc y x, 0 < t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hd : ∀ t ∈ uIcc y x, HasDerivAt (fun t : ℝ => -(2 / 3) * (t * Real.sqrt t)⁻¹)
      (1 / (t ^ 2 * Real.sqrt t)) t := by
    intro t ht
    have ht0 := hpos t ht
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h1 : HasDerivAt (fun t : ℝ => t * Real.sqrt t)
        (1 * Real.sqrt t + t * (1 / (2 * Real.sqrt t))) t :=
      (hasDerivAt_id t).mul (Real.hasDerivAt_sqrt ht0.ne')
    have h2 := (h1.inv (mul_ne_zero ht0.ne' hs0.ne')).const_mul (-(2 / 3))
    refine h2.congr_deriv ?_
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    field_simp
    nlinarith [hsq]
  have hc : ContinuousOn (fun t : ℝ => 1 / (t ^ 2 * Real.sqrt t)) (uIcc y x) :=
    continuousOn_const.div ((continuousOn_id.pow 2).mul Real.continuous_sqrt.continuousOn)
      fun t ht => by
        have := hpos t ht
        positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have hx0 : 0 < x := by linarith
  have : 0 ≤ (x * Real.sqrt x)⁻¹ := by positivity
  have e : 2 / 3 * (1 / (y * Real.sqrt y)) = 2 / 3 * (y * Real.sqrt y)⁻¹ := by rw [one_div]
  rw [e]
  linarith

/-- `0 ≤ ∫_y^x dt/(t² log²t) ≤ 1/(y log² y)` for `16 ≤ y ≤ x`. -/
theorem integral_inv_sq_log_sq_le {y x : ℝ} (hy : 16 ≤ y) (hyx : y ≤ x) :
    ∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2) ≤ 1 / (y * Real.log y ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hly := one_le_log_of_sixteen_le hy
  have hpos : ∀ t ∈ uIcc y x, 16 ≤ t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hgc : ContinuousOn (fun t : ℝ => 1 / (t ^ 2 * Real.log t ^ 2)) (uIcc y x) := by
    refine continuousOn_const.div ((continuousOn_id.pow 2).mul
      ((Real.continuousOn_log.mono ?_).pow 2)) ?_
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht
      have h1 := one_le_log_of_sixteen_le (hpos t ht)
      have h2 : 0 < t := by linarith [hpos t ht]
      exact mul_ne_zero (pow_ne_zero 2 h2.ne') (pow_ne_zero 2 (by linarith))
  have hcc : ContinuousOn (fun t : ℝ => 1 / Real.log y ^ 2 * (1 / t ^ 2)) (uIcc y x) :=
    continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2) fun s hs => by
      have := hpos s hs
      positivity)
  have hmono : ∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2)
      ≤ ∫ t in y..x, 1 / Real.log y ^ 2 * (1 / t ^ 2) := by
    refine intervalIntegral.integral_mono_on hyx hgc.intervalIntegrable hcc.intervalIntegrable
      fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : Real.log y ≤ Real.log t := Real.log_le_log hy0 ht.1
    have hly0 : 0 < Real.log y := by linarith
    rw [one_div_mul_one_div]
    have h2 : Real.log y ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hly0.le hlt 2
    refine one_div_le_one_div_of_le (mul_pos (pow_pos hly0 2) (pow_pos ht0 2)) ?_
    nlinarith [pow_pos ht0 2]
  have hd2 : ∀ t ∈ uIcc y x, HasDerivAt (fun t : ℝ => -(1 / Real.log y ^ 2) * t⁻¹)
      (1 / Real.log y ^ 2 * (1 / t ^ 2)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [hpos t ht]
    have := (hasDerivAt_inv ht0).const_mul (-(1 / Real.log y ^ 2))
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 hcc.intervalIntegrable] at hmono
  have hx0 : 0 < x := by linarith
  have hxinv : 0 ≤ 1 / Real.log y ^ 2 * x⁻¹ := by positivity
  have e : 1 / (y * Real.log y ^ 2) = 1 / Real.log y ^ 2 * y⁻¹ := by field_simp
  rw [e]
  linarith

/-- `∫_y^x dt/(t² log t) = 1/(y log y) - 1/(x log x) - ∫_y^x dt/(t² log² t)`. -/
theorem integral_inv_sq_log_eq {y x : ℝ} (hy : 16 ≤ y) (hyx : y ≤ x) :
    ∫ t in y..x, 1 / (t ^ 2 * Real.log t)
      = 1 / (y * Real.log y) - 1 / (x * Real.log x)
        - ∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2) := by
  have hpos : ∀ t ∈ uIcc y x, 16 ≤ t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hgd : ∀ t ∈ uIcc y x, HasDerivAt (fun t : ℝ => -(t * Real.log t)⁻¹)
      (1 / (t ^ 2 * Real.log t) + 1 / (t ^ 2 * Real.log t ^ 2)) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [hpos t ht]
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (1 * Real.log t + t * t⁻¹) t :=
      (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
    have h2 := (h1.inv (mul_ne_zero ht0 hl)).neg
    refine h2.congr_deriv ?_
    field_simp
  have hfc : ContinuousOn (fun t : ℝ => 1 / (t ^ 2 * Real.log t)) (uIcc y x) := by
    refine continuousOn_const.div ((continuousOn_id.pow 2).mul (Real.continuousOn_log.mono ?_)) ?_
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht
      have h1 := one_le_log_of_sixteen_le (hpos t ht)
      have h2 : 0 < t := by linarith [hpos t ht]
      exact mul_ne_zero (pow_ne_zero 2 h2.ne') (by linarith)
  have hgc : ContinuousOn (fun t : ℝ => 1 / (t ^ 2 * Real.log t ^ 2)) (uIcc y x) := by
    refine continuousOn_const.div ((continuousOn_id.pow 2).mul
      ((Real.continuousOn_log.mono ?_).pow 2)) ?_
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht
      have h1 := one_le_log_of_sixteen_le (hpos t ht)
      have h2 : 0 < t := by linarith [hpos t ht]
      exact mul_ne_zero (pow_ne_zero 2 h2.ne') (pow_ne_zero 2 (by linarith))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hgd
    (hfc.intervalIntegrable.add hgc.intervalIntegrable)
  rw [intervalIntegral.integral_add hfc.intervalIntegrable hgc.intervalIntegrable] at hFTC
  rw [one_div (y * Real.log y), one_div (x * Real.log x)]
  linarith

/-- The main term: `x f(x) - y f(y) + ∫_y^x t w(t) dt = ∫_y^x f`, `f = 1/(t² log t)`,
`w = -f'`. -/
theorem prime_sq_main_identity {y x : ℝ} (hy : 16 ≤ y) (hyx : y ≤ x) :
    x * (1 / (x ^ 2 * Real.log x)) - y * (1 / (y ^ 2 * Real.log y))
      + ∫ t in y..x, t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
      = ∫ t in y..x, 1 / (t ^ 2 * Real.log t) := by
  have hpos : ∀ t ∈ uIcc y x, 16 ≤ t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hfd : ∀ t ∈ uIcc y x, HasDerivAt (fun t : ℝ => 1 / (t ^ 2 * Real.log t))
      (-((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))) t := fun t ht =>
    hasDerivAt_inv_sq_mul_log (by linarith [hpos t ht])
  have hwc : ContinuousOn (fun t : ℝ => -((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
      (uIcc y x) := by
    refine (((continuousOn_const.mul (Real.continuousOn_log.mono ?_)).add continuousOn_const).div
      ((continuousOn_id.pow 3).mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_).neg
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht
      have h1 := one_le_log_of_sixteen_le (hpos t ht)
      have h2 : 0 < t := by linarith [hpos t ht]
      exact mul_ne_zero (pow_ne_zero 3 h2.ne') (pow_ne_zero 2 (by linarith))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun t : ℝ => t)
    (u' := fun _ => 1) (fun t _ => hasDerivAt_id t) hfd intervalIntegrable_const
    hwc.intervalIntegrable
  simp only [one_mul] at hparts
  have hneg : ∫ t in y..x, t * -((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
      = -∫ t in y..x, t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hneg] at hparts
  linarith


/-- `|(θ(t) - t)/(t² log t)| ≤ K log t/(t√t)` under the von Koch bound. -/
theorem abs_theta_error_mul_weight_le {K t : ℝ} (hK : 0 ≤ K)
    (hS : ∀ t : ℝ, 16 ≤ t → |Chebyshev.theta t - t| ≤ K * Real.sqrt t * Real.log t ^ 2)
    (ht : 16 ≤ t) :
    |(Chebyshev.theta t - t) * (1 / (t ^ 2 * Real.log t))|
      ≤ K * Real.log t / (t * Real.sqrt t) := by
  have ht0 : 0 < t := by linarith
  have hl := one_le_log_of_sixteen_le ht
  have hl0 : 0 < Real.log t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hw0 : 0 < 1 / (t ^ 2 * Real.log t) := by positivity
  rw [abs_mul, abs_of_pos hw0]
  calc |Chebyshev.theta t - t| * (1 / (t ^ 2 * Real.log t))
      ≤ K * Real.sqrt t * Real.log t ^ 2 * (1 / (t ^ 2 * Real.log t)) :=
        mul_le_mul_of_nonneg_right (hS t ht) hw0.le
    _ = K * Real.log t / (t * Real.sqrt t) := by
        field_simp
        nlinarith [hsq]

/-- The error integral: `|∫_y^x (θ - t)(2 log t + 1)/(t³ log² t)| ≤ 2K log x/(y√y)`. -/
theorem abs_integral_theta_error_weight_le {K y x : ℝ} (hK : 0 ≤ K)
    (hS : ∀ t : ℝ, 16 ≤ t → |Chebyshev.theta t - t| ≤ K * Real.sqrt t * Real.log t ^ 2)
    (hy : 16 ≤ y) (hyx : y ≤ x) :
    |∫ t in y..x, (Chebyshev.theta t - t) * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))|
      ≤ 2 * K * Real.log x / (y * Real.sqrt y) := by
  have hy0 : 0 < y := by linarith
  have hpos : ∀ t ∈ uIcc y x, 16 ≤ t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hpt : ∀ᵐ t ∂volume, t ∈ Ioc y x →
      ‖(Chebyshev.theta t - t) * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))‖
        ≤ 3 * K * Real.log x * (1 / (t ^ 2 * Real.sqrt t)) := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht16 : 16 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hlt := one_le_log_of_sixteen_le ht16
    have hlt0 : 0 < Real.log t := by linarith
    have hltx : Real.log t ≤ Real.log x := Real.log_le_log ht0 ht.2
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hw0 : 0 < (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw0]
    have hwle : (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2) ≤ 3 / (t ^ 3 * Real.log t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : 0 < t ^ 3 := pow_pos ht0 3
      nlinarith [mul_pos h3 hlt0]
    calc |Chebyshev.theta t - t| * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
        ≤ K * Real.sqrt t * Real.log t ^ 2 * (3 / (t ^ 3 * Real.log t)) :=
          mul_le_mul (hS t ht16) hwle hw0.le (by positivity)
      _ = 3 * K * Real.log t * (1 / (t ^ 2 * Real.sqrt t)) := by
          field_simp
          nlinarith [hsq]
      _ ≤ 3 * K * Real.log x * (1 / (t ^ 2 * Real.sqrt t)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hltx (by positivity)
  have hgc : ContinuousOn (fun t : ℝ => 1 / (t ^ 2 * Real.sqrt t)) (uIcc y x) :=
    continuousOn_const.div ((continuousOn_id.pow 2).mul Real.continuous_sqrt.continuousOn)
      fun t ht => by
        have := hpos t ht
        positivity
  have hle := intervalIntegral.norm_integral_le_of_norm_le hyx hpt
    (hgc.intervalIntegrable.const_mul (3 * K * Real.log x))
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hle
  have h3 := integral_inv_sq_mul_sqrt_le_two_thirds hy0 hyx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hc0 : 0 ≤ 3 * K * Real.log x := by positivity
  calc _ ≤ 3 * K * Real.log x * ∫ t in y..x, 1 / (t ^ 2 * Real.sqrt t) := hle
    _ ≤ 3 * K * Real.log x * (2 / 3 * (1 / (y * Real.sqrt y))) := mul_le_mul_of_nonneg_left h3 hc0
    _ = 2 * K * Real.log x / (y * Real.sqrt y) := by field_simp

/-- **Prime squares with an error term.**  Under the von Koch bound for `θ`, for `16 ≤ y ≤ x`:
`|Σ_{y<p≤x} 1/p² - 1/(y log y)| ≤ 1/(x log x) + 1/(y log²y) + K log x/(x√x) + 3K log x/(y√y)`. -/
theorem abs_sum_prime_inv_sq_sub_le {K y x : ℝ} (hK : 0 ≤ K)
    (hS : ∀ t : ℝ, 16 ≤ t → |Chebyshev.theta t - t| ≤ K * Real.sqrt t * Real.log t ^ 2)
    (hy : 16 ≤ y) (hyx : y ≤ x) :
    |∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊,
        1 / ((n : ℝ) ^ 2 * Real.log n) * (if n.Prime then Real.log n else 0)
        - 1 / (y * Real.log y)|
      ≤ 1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2) + K * Real.log x / (x * Real.sqrt x)
        + 3 * K * Real.log x / (y * Real.sqrt y) := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ uIcc y x, 16 ≤ t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hwc : ContinuousOn (fun t : ℝ => (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
      (uIcc y x) := by
    refine ((continuousOn_const.mul (Real.continuousOn_log.mono ?_)).add continuousOn_const).div
      ((continuousOn_id.pow 3).mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht
      have h1 := one_le_log_of_sixteen_le (hpos t ht)
      have h2 : 0 < t := by linarith [hpos t ht]
      exact mul_ne_zero (pow_ne_zero 3 h2.ne') (pow_ne_zero 2 (by linarith))
  have hti : IntervalIntegrable (fun t => t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
      volume y x := (continuousOn_id.mul hwc).intervalIntegrable
  have hSi : IntervalIntegrable (fun t => (Chebyshev.theta t - t)
      * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))) volume y x :=
    (((Chebyshev.theta_mono.intervalIntegrable).sub
      (continuous_id.intervalIntegrable _ _))).mul_continuousOn hwc
  have hsplit : ∫ t in y..x, Chebyshev.theta t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
      = (∫ t in y..x, t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
        + ∫ t in y..x, (Chebyshev.theta t - t)
            * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_add hti hSi]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [sum_prime_inv_sq_eq_abel (by linarith) hyx, hsplit]
  have hmain := prime_sq_main_identity hy hyx
  have hF := integral_inv_sq_log_eq hy hyx
  have hg := integral_inv_sq_log_sq_le hy hyx
  have hg0 : 0 ≤ ∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hyx fun t _ => by positivity
  have hEx := abs_theta_error_mul_weight_le hK hS (show 16 ≤ x by linarith)
  have hEy := abs_theta_error_mul_weight_le hK hS hy
  have hEI := abs_integral_theta_error_weight_le hK hS hy hyx
  have hlyx : K * Real.log y / (y * Real.sqrt y) ≤ K * Real.log x / (y * Real.sqrt y) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.log_le_log hy0 hyx) hK)
      (by positivity)
  have hdecomp : Chebyshev.theta x / (x ^ 2 * Real.log x) - Chebyshev.theta y / (y ^ 2 * Real.log y)
      + ((∫ t in y..x, t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
        + ∫ t in y..x, (Chebyshev.theta t - t) * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
      - 1 / (y * Real.log y)
      = -(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2))
        + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x))
        - (Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y))
        + ∫ t in y..x, (Chebyshev.theta t - t)
            * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
    have e1 : Chebyshev.theta x / (x ^ 2 * Real.log x)
        = x * (1 / (x ^ 2 * Real.log x))
          + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x)) := by
      ring
    have e2 : Chebyshev.theta y / (y ^ 2 * Real.log y)
        = y * (1 / (y ^ 2 * Real.log y))
          + (Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y)) := by
      ring
    rw [e1, e2]
    linarith
  rw [hdecomp]
  have hA := abs_add_le (-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2))
      + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x))
      - (Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y)))
    (∫ t in y..x, (Chebyshev.theta t - t) * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
  have hB := abs_sub (-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2))
      + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x)))
    ((Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y)))
  have hC := abs_add_le (-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2)))
    ((Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x)))
  have hlx : 0 < Real.log x := by linarith [one_le_log_of_sixteen_le (show 16 ≤ x by linarith)]
  have hD : |(-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2)))|
      ≤ 1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2) := by
    have : 0 ≤ 1 / (x * Real.log x) := by positivity
    rw [abs_le]; constructor <;> linarith
  have e3 : 3 * K * Real.log x / (y * Real.sqrt y)
      = K * Real.log x / (y * Real.sqrt y) + 2 * K * Real.log x / (y * Real.sqrt y) := by ring
  rw [e3]
  linarith only [hA, hB, hC, hD, hEx, hEy, hlyx, hEI]


/-- `log^k x / x^r → 0` for `r > 0`. -/
theorem tendsto_log_pow_div_rpow_atTop (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => Real.log x ^ k / x ^ r) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.rpow_natCast]

/-- **Prime squares beyond `√x`.**  Under RH, `(Σ_{√x<p≤x} 1/p²) √x log x → 2`. -/
theorem tendsto_sum_prime_inv_sq_scaled (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
        1 / (p : ℝ) ^ 2) * (Real.sqrt x * Real.log x)) atTop (𝓝 2) := by
  obtain ⟨K, hK, hS⟩ := exists_abs_theta_sub_le_of_riemannHypothesis hRH
  have h1 : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h2 : Tendsto (fun x : ℝ => 4 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h3 := (tendsto_log_pow_div_rpow_atTop 2 (r := 1) one_pos).const_mul K
  have h4 := (tendsto_log_pow_div_rpow_atTop 2 (r := 1 / 4) (by norm_num)).const_mul (3 * K)
  have hE0 := ((h1.add h2).add h3).add h4
  rw [show (0 : ℝ) + 0 + K * 0 + 3 * K * 0 = 0 by ring] at hE0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hE0
  filter_upwards [eventually_ge_atTop (256 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hy16 : 16 ≤ Real.sqrt x := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hy0 : 0 < Real.sqrt x := by linarith
  have hyy : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hyx : Real.sqrt x ≤ x := by nlinarith
  have hlogy : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hb := abs_sum_prime_inv_sq_sub_le hK hS hy16 hyx
  rw [← sum_filter_prime_inv_sq_eq (Real.sqrt_nonneg x)] at hb
  set Sm := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
    1 / (p : ℝ) ^ 2 with hSm
  have hD : 0 < Real.sqrt x * Real.log x := by positivity
  have hkey : Sm * (Real.sqrt x * Real.log x) - 2
      = (Sm - 1 / (Real.sqrt x * Real.log (Real.sqrt x))) * (Real.sqrt x * Real.log x) := by
    rw [hlogy]; field_simp
  rw [Real.norm_eq_abs, hkey, abs_mul, abs_of_pos hD]
  have hsy : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have hsy0 : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hy0
  calc |Sm - 1 / (Real.sqrt x * Real.log (Real.sqrt x))| * (Real.sqrt x * Real.log x)
      ≤ (1 / (x * Real.log x) + 1 / (Real.sqrt x * Real.log (Real.sqrt x) ^ 2)
          + K * Real.log x / (x * Real.sqrt x)
          + 3 * K * Real.log x / (Real.sqrt x * Real.sqrt (Real.sqrt x)))
          * (Real.sqrt x * Real.log x) :=
        mul_le_mul_of_nonneg_right hb hD.le
    _ = 1 / Real.sqrt x + 4 / Real.log x + K * (Real.log x ^ 2 / x ^ (1 : ℝ))
          + 3 * K * (Real.log x ^ 2 / x ^ (1 / 4 : ℝ)) := by
        rw [Real.rpow_one, ← hsy, hlogy]
        have hq := hsy0.ne'
        have e1 : 1 / (x * Real.log x) * (Real.sqrt x * Real.log x) = 1 / Real.sqrt x := by
          calc 1 / (x * Real.log x) * (Real.sqrt x * Real.log x) = Real.sqrt x / x := by
                field_simp
            _ = Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by rw [hyy]
            _ = 1 / Real.sqrt x := by field_simp
        have e2 : 1 / (Real.sqrt x * (Real.log x / 2) ^ 2) * (Real.sqrt x * Real.log x)
            = 4 / Real.log x := by field_simp; norm_num
        have e3 : K * Real.log x / (x * Real.sqrt x) * (Real.sqrt x * Real.log x)
            = K * (Real.log x ^ 2 / x) := by field_simp
        have e4 : 3 * K * Real.log x / (Real.sqrt x * Real.sqrt (Real.sqrt x))
            * (Real.sqrt x * Real.log x)
            = 3 * K * (Real.log x ^ 2 / Real.sqrt (Real.sqrt x)) := by field_simp
        rw [add_mul, add_mul, add_mul, e1, e2, e3, e4]


/-! ## The four pieces of the scaled defect -/

theorem mertensProductError_sub_eq_sum (x : ℝ) :
    mertensProductError x - mertensError x
      = ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, mertensPrimeTail ⌊x⌋₊ p := by
  unfold mertensProductError mertensError mertensPrimeTail
  rw [neg_log_mertensPrimeProduct_eq, mertensPowerSum_eq_sum_primes, Finset.sum_sub_distrib]
  ring

/-- **Prime tails.**  Under RH, `(P(x) - A(x)) √x log x → 1`. -/
theorem tendsto_mertensProductError_sub_scaled (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => (mertensProductError x - mertensError x) * (Real.sqrt x * Real.log x))
      atTop (𝓝 1) := by
  have hP := tendsto_sum_prime_inv_sq_scaled hRH
  have hhalf : Tendsto (fun x : ℝ =>
      (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
        1 / (2 * (p : ℝ) ^ 2)) * (Real.sqrt x * Real.log x)) atTop (𝓝 1) := by
    have := hP.const_mul (1 / 2)
    rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num] at this
    refine this.congr fun x => ?_
    rw [← mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have h7 : Tendsto (fun x : ℝ => 7 / (x ^ (1 / 3 : ℝ)) ^ 2 * (Real.sqrt x * Real.log x))
      atTop (𝓝 0) := by
    have h := (tendsto_log_pow_div_rpow_atTop 1 (r := 1 / 6) (by norm_num)).const_mul 7
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h1 : (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    have h2 : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have h3 : x ^ (2 / 3 : ℝ) = x ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    rw [h1, h2, h3, pow_one]
    have h4 := Real.rpow_pos_of_pos hx (1 / 2 : ℝ)
    have h5 := Real.rpow_pos_of_pos hx (1 / 6 : ℝ)
    field_simp
  have hup := hhalf.add h7
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hhalf hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (64 : ℝ)] with x hx
    have hD : 0 ≤ Real.sqrt x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
    rw [mertensProductError_sub_eq_sum]
    exact mul_le_mul_of_nonneg_right (sum_mertensPrimeTail_mem hx).1 hD
  · filter_upwards [eventually_ge_atTop (64 : ℝ)] with x hx
    have hD : 0 ≤ Real.sqrt x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
    rw [mertensProductError_sub_eq_sum, ← add_mul]
    exact mul_le_mul_of_nonneg_right (sum_mertensPrimeTail_mem hx).2 hD

/-- `θ(y)/y → 1` under RH. -/
theorem tendsto_theta_div_self_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Tendsto (fun y : ℝ => Chebyshev.theta y / y) atTop (𝓝 1) := by
  obtain ⟨K, hK, hS⟩ := exists_abs_theta_sub_le_of_riemannHypothesis hRH
  have h0 : Tendsto (fun y : ℝ => K * (Real.log y ^ 2 / y ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow_atTop 2 (r := 1 / 2) (by norm_num)).const_mul K
    rwa [mul_zero] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with y hy
  have hy0 : 0 < y := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hyy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  rw [Real.norm_eq_abs, show Chebyshev.theta y / y - 1 = (Chebyshev.theta y - y) / y by
    field_simp, abs_div, abs_of_pos hy0, div_le_iff₀ hy0, ← Real.sqrt_eq_rpow]
  calc |Chebyshev.theta y - y| ≤ K * Real.sqrt y * Real.log y ^ 2 := hS y hy
    _ = K * (Real.log y ^ 2 / Real.sqrt y) * (Real.sqrt y * Real.sqrt y) := by field_simp
    _ = K * (Real.log y ^ 2 / Real.sqrt y) * y := by rw [hyy]

/-- **Prime squares.**  Under RH, `(ψ(x) - θ(x))/√x → 1`. -/
theorem tendsto_psi_sub_theta_div_sqrt (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x) atTop (𝓝 1) := by
  have hθ := (tendsto_theta_div_self_of_riemannHypothesis hRH).comp Real.tendsto_sqrt_atTop
  have hsmall : Tendsto (fun x : ℝ => 2 * Real.log 4 * (Real.log x ^ 1 / x ^ (1 / 6 : ℝ)))
      atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow_atTop 1 (r := 1 / 6) (by norm_num)).const_mul (2 * Real.log 4)
    rwa [mul_zero] at this
  have hup := hθ.add hsmall
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hθ hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    exact div_le_div_of_nonneg_right (theta_sqrt_le_psi_sub_theta hx) hsx.le
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    -- `ψ - θ = θ(√x) + Σ_{3 ≤ n ≤ N} θ(x^{1/n})`
    rw [Chebyshev.psi_eq_theta_add_sum_theta (by linarith), add_sub_cancel_left]
    set N := ⌊Real.log x / Real.log 2⌋₊ with hN
    have hN2 : 2 ≤ N := by
      apply Nat.le_floor
      rw [le_div_iff₀ hl2]
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_log (by norm_num) hx
      push_cast; linarith
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hN2]
    have hfirst : x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [hfirst]
    have hrest : ∑ n ∈ Finset.Ioc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n))
        ≤ 2 * Real.log 4 * Real.log x * x ^ (1 / 3 : ℝ) := by
      have hle : ∀ n ∈ Finset.Ioc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n))
          ≤ Real.log 4 * x ^ (1 / 3 : ℝ) := by
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn.1
        have h1 := Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0.le ((1 : ℝ) / n))
        have h2 : x ^ ((1 : ℝ) / n) ≤ x ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
        have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        nlinarith
      refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
      rw [nsmul_eq_mul, Nat.card_Ioc]
      have hNle : ((N - 2 : ℕ) : ℝ) ≤ 2 * Real.log x := by
        have h1 : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 2
        have h2 : (N : ℝ) ≤ Real.log x / Real.log 2 := Nat.floor_le (by positivity)
        have h3 : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
          rw [div_le_iff₀ hl2]
          have := Real.log_two_gt_d9
          nlinarith
        linarith
      have hp : 0 ≤ Real.log 4 * x ^ (1 / 3 : ℝ) :=
        mul_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg hx0.le _)
      calc ((N - 2 : ℕ) : ℝ) * (Real.log 4 * x ^ (1 / 3 : ℝ))
          ≤ 2 * Real.log x * (Real.log 4 * x ^ (1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hNle hp
        _ = 2 * Real.log 4 * Real.log x * x ^ (1 / 3 : ℝ) := by ring
    have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have hxr : x ^ (1 / 3 : ℝ) / Real.sqrt x = 1 / x ^ (1 / 6 : ℝ) := by
      rw [hsq, div_eq_div_iff (Real.rpow_pos_of_pos hx0 _).ne' (Real.rpow_pos_of_pos hx0 _).ne',
        one_mul, ← Real.rpow_add hx0]; norm_num
    rw [add_div]
    have : (∑ n ∈ Finset.Ioc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n))) / Real.sqrt x
        ≤ 2 * Real.log 4 * (Real.log x ^ 1 / x ^ (1 / 6 : ℝ)) := by
      rw [div_le_iff₀ hsx]
      refine hrest.trans (le_of_eq ?_)
      have h6 := Real.rpow_pos_of_pos hx0 (1 / 6 : ℝ)
      have e : x ^ (1 / 3 : ℝ) = Real.sqrt x / x ^ (1 / 6 : ℝ) := by
        rw [eq_div_iff h6.ne', hsq, ← Real.rpow_add hx0]; norm_num
      rw [e, pow_one]; field_simp
    simp only [Function.comp_apply]
    linarith


/-- **The second-order θ-term.**  Under RH,
`√x log x ((θ(x) - x)/(x log x) - (log log θ(x) - log log x)) → 0`. -/
theorem tendsto_theta_second_order (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => Real.sqrt x * Real.log x * ((Chebyshev.theta x - x) / (x * Real.log x)
      - (Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x)))) atTop (𝓝 0) := by
  obtain ⟨K, hK, hS⟩ := exists_abs_theta_sub_le_of_riemannHypothesis hRH
  have h0 : Tendsto (fun x : ℝ => 35 / 4 * K ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ))) atTop
      (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow_atTop 4 (r := 1 / 2) (by norm_num)).const_mul (35 / 4 * K ^ 2)
    rwa [mul_zero] at this
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [eventually_two_fifths_le_theta, eventually_ge_atTop (16 : ℝ)] with x hθ hx
    have hx0 : 0 < x := by linarith
    have hθ1 : 1 < Chebyshev.theta x := by linarith
    have h1 := log_log_theta_le (by linarith) hθ1
    have hD : 0 ≤ Real.sqrt x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
    exact mul_nonneg hD (by linarith)
  · filter_upwards [eventually_two_fifths_le_theta, eventually_ge_atTop (16 : ℝ)] with x hθ hx
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hθ1 : 1 < Chebyshev.theta x := by linarith
    have hlθ1 : 1 ≤ Real.log (Chebyshev.theta x) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have h1 := log_log_ge_add (by linarith : (1 : ℝ) < x) hθ1
    have h2 := sub_div_sub_le_sq (by linarith : (1 : ℝ) < x) hθ hlθ1
    have hD : 0 < Real.sqrt x * Real.log x := mul_pos (Real.sqrt_pos.mpr hx0) hlx
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hsq : (Chebyshev.theta x - x) ^ 2 ≤ (K * Real.sqrt x * Real.log x ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hS x hx) 2
    calc Real.sqrt x * Real.log x * ((Chebyshev.theta x - x) / (x * Real.log x)
          - (Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x)))
        ≤ Real.sqrt x * Real.log x * (35 / 4 * ((Chebyshev.theta x - x) ^ 2
            / (x ^ 2 * Real.log x))) := by
          refine mul_le_mul_of_nonneg_left ?_ hD.le
          linarith
      _ ≤ Real.sqrt x * Real.log x * (35 / 4 * ((K * Real.sqrt x * Real.log x ^ 2) ^ 2
            / (x ^ 2 * Real.log x))) := by
          refine mul_le_mul_of_nonneg_left ?_ hD.le
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity))
            (by norm_num)
      _ = 35 / 4 * K ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ)) := by
          have hsq' : (K * Real.sqrt x * Real.log x ^ 2) ^ 2 = K ^ 2 * x * Real.log x ^ 4 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le]; ring
          rw [hsq', ← Real.sqrt_eq_rpow]
          have h3 : Real.sqrt x * Real.log x * (35 / 4 * (K ^ 2 * x * Real.log x ^ 4
              / (x ^ 2 * Real.log x))) = 35 / 4 * K ^ 2 * Real.log x ^ 4 * (Real.sqrt x / x) := by
            field_simp
          have h4 : Real.sqrt x / x = 1 / Real.sqrt x := by
            rw [div_eq_div_iff hx0.ne' hsx.ne']; linarith
          rw [h3, h4]; ring

/-- `|G(T) - h(T)v(T)| ≤ (3/T²)(2a₁ e^{-T/2} + 2e^{-T})` under RH, `T ≥ 4`. -/
theorem abs_mertensErrorRemainder_sub_lag_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 4 ≤ T) :
    |mertensErrorRemainder T - (1 + T) / T ^ 2 * mertensLagPrimitive T|
      ≤ 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T)) := by
  have hT0 : 0 < T := by linarith
  have ha := poleSharpConstant_pos
  have ha3 := poleSharpConstant_lt_three_tenths
  refine le_of_forall_pos_lt_add fun η hη => ?_
  -- a far point `W` where `G(W)` and `h(W)v(W)` are small
  have hGW : Tendsto mertensErrorRemainder atTop (𝓝 0) := by
    have h1 : Tendsto (fun W : ℝ => (poleSharpConstant + 10 / W) * (Real.exp (-W / 2) / W))
        atTop (𝓝 0) := by
      have hA : Tendsto (fun W : ℝ => poleSharpConstant + 10 / W) atTop
          (𝓝 (poleSharpConstant + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
      have hB : Tendsto (fun W : ℝ => Real.exp (-W / 2) / W) atTop (𝓝 0) := by
        have h := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
          (show -(1 / 2 : ℝ) < 0 by norm_num))).div_atTop tendsto_id
        refine h.congr fun W => ?_
        simp only [Function.comp, id]; ring_nf
      simpa using hA.mul hB
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with W hW
    rw [sub_zero, Real.norm_eq_abs]
    exact abs_mertensErrorRemainder_le_sharp_of_riemannHypothesis hRH hW
  have hhv : Tendsto (fun W : ℝ => (1 + W) / W ^ 2 * mertensLagPrimitive W) atTop (𝓝 0) := by
    have h1 : Tendsto (fun W : ℝ => 2 / W * (poleSharpConstant + 2)) atTop (𝓝 0) := by
      have h2W : Tendsto (fun W : ℝ => 2 / W) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using h2W.mul_const (poleSharpConstant + 2)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with W hW
    have hW0 : 0 < W := by linarith
    rw [sub_zero, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    have hv := abs_mertensLagPrimitive_le_of_riemannHypothesis hRH hW0
    have he1 : Real.exp (-W / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he2 : Real.exp (-W) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hv2 : |mertensLagPrimitive W| ≤ poleSharpConstant + 2 := by nlinarith
    have hh : (1 + W) / W ^ 2 ≤ 2 / W := by
      rw [div_le_div_iff₀ (by positivity) hW0]; nlinarith
    exact mul_le_mul hh hv2 (abs_nonneg _) (by positivity)
  obtain ⟨W, hGW', hhvW, hTW⟩ := ((hGW.eventually (Metric.ball_mem_nhds 0 (half_pos hη))).and
    ((hhv.eventually (Metric.ball_mem_nhds 0 (half_pos hη))).and (eventually_ge_atTop T))).exists
  have hGW1 : |mertensErrorRemainder W| < η / 2 := by simpa [Real.dist_eq] using hGW'
  have hhvW1 : |(1 + W) / W ^ 2 * mertensLagPrimitive W| < η / 2 := by
    have h := Metric.mem_ball.mp hhvW
    rwa [Real.dist_eq, sub_zero] at h
  have hI2 := mertensErrorRemainder_sub_eq_lag (by linarith : (1 : ℝ) ≤ T) hTW
  -- the tail integral
  have hint : |∫ t in T..W, (t + 2) / t ^ 3 * mertensLagPrimitive t|
      ≤ 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T)) := by
    have hpt : ∀ᵐ t ∂volume, t ∈ Ioc T W → ‖(t + 2) / t ^ 3 * mertensLagPrimitive t‖
        ≤ 3 / T ^ 2 * (poleSharpConstant * Real.exp (-t / 2)
          + 2 * Real.exp ((2 * (1 / 2) - 2) * t)) := by
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      have hTt : T ≤ t := ht.1.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
      have hv := abs_mertensLagPrimitive_le_of_riemannHypothesis hRH ht0
      have hk : (t + 2) / t ^ 3 ≤ 3 / T ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : T ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hT0.le hTt 2
        nlinarith
      have e : (2 * (1 / 2 : ℝ) - 2) * t = -t := by ring
      rw [e]
      exact mul_le_mul hk hv (abs_nonneg _) (by positivity)
    have hle := intervalIntegral.norm_integral_le_of_norm_le hTW hpt
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hle
    have h2 := integral_exp_weight_le T W ha.le (by norm_num : (0 : ℝ) ≤ 2)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have e1 : (2 * (1 / 2 : ℝ) - 2) * T = -T := by ring
    rw [e1, show (2 : ℝ) - 2 * (1 / 2) = 1 by norm_num, div_one] at h2
    refine hle.trans ?_
    have : 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T))
        = 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T)) := rfl
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have habs : |mertensErrorRemainder T - (1 + T) / T ^ 2 * mertensLagPrimitive T|
      ≤ |mertensErrorRemainder W| + |(1 + W) / W ^ 2 * mertensLagPrimitive W|
        + |∫ t in T..W, (t + 2) / t ^ 3 * mertensLagPrimitive t| := by
    have e : mertensErrorRemainder T - (1 + T) / T ^ 2 * mertensLagPrimitive T
        = mertensErrorRemainder W - (1 + W) / W ^ 2 * mertensLagPrimitive W
          - ∫ t in T..W, (t + 2) / t ^ 3 * mertensLagPrimitive t := by linarith
    rw [e]
    calc _ ≤ |mertensErrorRemainder W - (1 + W) / W ^ 2 * mertensLagPrimitive W|
          + |∫ t in T..W, (t + 2) / t ^ 3 * mertensLagPrimitive t| := abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  linarith


/-- **The Mertens remainder is the lag.**  Under RH, `G(log x) √x log x - Φ(log x) → 0`. -/
theorem tendsto_mertensErrorRemainder_scaled_sub_lag (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => mertensErrorRemainder (Real.log x) * (Real.sqrt x * Real.log x)
      - weilLagFunctionReal (Real.log x)) atTop (𝓝 0) := by
  have ha := poleSharpConstant_pos
  have hB : Tendsto (fun x : ℝ => (7 * poleSharpConstant + 6) / Real.log x + 4 / Real.sqrt x)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (7 * poleSharpConstant + 6) / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => 4 / Real.sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hB
  filter_upwards [eventually_ge_atTop (Real.exp 4)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  set T := Real.log x with hTdef
  have hT4 : 4 ≤ T := by rw [hTdef, Real.le_log_iff_exp_le hx0]; exact hx
  have hT0 : 0 < T := by linarith
  have hsx : Real.sqrt x = Real.exp (T / 2) := by
    rw [hTdef, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; ring_nf
  have hgap := abs_mertensErrorRemainder_sub_lag_le hRH hT4
  have hΦ := weilLagFunctionReal_eq_lagPrimitive hT0
  have hΦa : |weilLagFunctionReal T| ≤ poleSharpConstant := by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH T
    rwa [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  have hX1 : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT0.le
  have hS0 := trivialZeroSeriesReal_nonneg hX1
  have hS1 := trivialZeroSeriesReal_le_one hX1
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 1 < Real.log (2 * Real.pi) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  set δ := Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδ2 : δ ≤ 2 := by rw [hδ]; linarith
  have hEp := Real.exp_pos (T / 2)
  have hEm := Real.exp_pos (-T / 2)
  have hEE : Real.exp (T / 2) * Real.exp (-T / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  -- `e^{T/2} v(T) = Φ(T) + δ e^{-T/2}`
  have hv : Real.exp (T / 2) * mertensLagPrimitive T = weilLagFunctionReal T
      + δ * Real.exp (-T / 2) := by rw [hΦ]; ring
  have hsplit : mertensErrorRemainder T * (Real.exp (T / 2) * T) - weilLagFunctionReal T
      = (mertensErrorRemainder T - (1 + T) / T ^ 2 * mertensLagPrimitive T) * (Real.exp (T / 2) * T)
        + (weilLagFunctionReal T / T + (1 + T) / T * (δ * Real.exp (-T / 2))) := by
    have e : (1 + T) / T ^ 2 * mertensLagPrimitive T * (Real.exp (T / 2) * T)
        = (1 + T) / T * (Real.exp (T / 2) * mertensLagPrimitive T) := by field_simp
    rw [sub_mul, e, hv]
    field_simp
    ring
  rw [Real.norm_eq_abs, sub_zero, hsx, hsplit]
  have h1 : |(mertensErrorRemainder T - (1 + T) / T ^ 2 * mertensLagPrimitive T)
      * (Real.exp (T / 2) * T)| ≤ (6 * poleSharpConstant + 6) / T := by
    rw [abs_mul, abs_of_pos (mul_pos hEp hT0)]
    have he1 : Real.exp (-T / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hprod : 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T))
        * (Real.exp (T / 2) * T) = 3 / T * (2 * poleSharpConstant + 2 * Real.exp (-T / 2)) := by
      have hA : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by rw [mul_comm]; exact hEE
      have hB : Real.exp (-T) * Real.exp (T / 2) = Real.exp (-T / 2) := by
        rw [← Real.exp_add]; ring_nf
      calc 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T))
            * (Real.exp (T / 2) * T)
          = 3 / T ^ 2 * T * (2 * poleSharpConstant * (Real.exp (-T / 2) * Real.exp (T / 2))
            + 2 * (Real.exp (-T) * Real.exp (T / 2))) := by ring
        _ = 3 / T ^ 2 * T * (2 * poleSharpConstant * 1 + 2 * Real.exp (-T / 2)) := by
            rw [hA, hB]
        _ = 3 / T * (2 * poleSharpConstant + 2 * Real.exp (-T / 2)) := by
            field_simp
    calc _ ≤ 3 / T ^ 2 * (2 * poleSharpConstant * Real.exp (-T / 2) + 2 * Real.exp (-T))
          * (Real.exp (T / 2) * T) := mul_le_mul_of_nonneg_right hgap (mul_pos hEp hT0).le
      _ = 3 / T * (2 * poleSharpConstant + 2 * Real.exp (-T / 2)) := hprod
      _ ≤ 3 / T * (2 * poleSharpConstant + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity); linarith
      _ = (6 * poleSharpConstant + 6) / T := by ring
  have h2 : |weilLagFunctionReal T / T + (1 + T) / T * (δ * Real.exp (-T / 2))|
      ≤ poleSharpConstant / T + 4 / Real.exp (T / 2) := by
    have hT1 : (1 + T) / T ≤ 2 := by rw [div_le_iff₀ hT0]; linarith
    have hq : 0 ≤ (1 + T) / T := by positivity
    have hEm' : Real.exp (-T / 2) = 1 / Real.exp (T / 2) := by
      rw [eq_div_iff hEp.ne', mul_comm]; exact hEE
    calc _ ≤ |weilLagFunctionReal T / T| + |(1 + T) / T * (δ * Real.exp (-T / 2))| := abs_add_le _ _
      _ ≤ poleSharpConstant / T + 2 * (2 * Real.exp (-T / 2)) := by
          gcongr
          · rw [abs_div, abs_of_pos hT0]; exact div_le_div_of_nonneg_right hΦa hT0.le
          · rw [abs_mul, abs_of_nonneg hq, abs_mul, abs_of_nonneg hδ0, abs_of_pos hEm]
            exact mul_le_mul hT1 (mul_le_mul_of_nonneg_right hδ2 hEm.le) (by positivity)
              (by norm_num)
      _ = poleSharpConstant / T + 4 / Real.exp (T / 2) := by rw [hEm']; ring
  calc _ ≤ |(mertensErrorRemainder T - (1 + T) / T ^ 2 * mertensLagPrimitive T)
        * (Real.exp (T / 2) * T)|
        + |weilLagFunctionReal T / T + (1 + T) / T * (δ * Real.exp (-T / 2))| := abs_add_le _ _
    _ ≤ (6 * poleSharpConstant + 6) / T + (poleSharpConstant / T + 4 / Real.exp (T / 2)) :=
        add_le_add h1 h2
    _ = (7 * poleSharpConstant + 6) / T + 4 / Real.exp (T / 2) := by ring


/-! ## Nicolas's constant -/

/-- **The scaled Nicolas defect is two plus the lag.**  Under RH,
`Nic(x) √x log x - Φ(log x) → 2`. -/
theorem tendsto_nicolasDefect_scaled_sub_lag (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => nicolasDefect x * (Real.sqrt x * Real.log x)
      - weilLagFunctionReal (Real.log x)) atTop (𝓝 2) := by
  have h := (((tendsto_mertensProductError_sub_scaled hRH).add
    (tendsto_mertensErrorRemainder_scaled_sub_lag hRH)).add
      (tendsto_psi_sub_theta_div_sqrt hRH)).add (tendsto_theta_second_order hRH)
  rw [show (1 : ℝ) + 0 + 1 + 0 = 2 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hG : mertensErrorRemainder (Real.log x)
      = mertensError x - (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [mertensErrorRemainder, Real.exp_log hx0]
  have hψθ : (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x
      = (Chebyshev.psi x - Chebyshev.theta x) / (x * Real.log x) * (Real.sqrt x * Real.log x) := by
    calc (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x
        = (Chebyshev.psi x - Chebyshev.theta x) * Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by
          field_simp
      _ = (Chebyshev.psi x - Chebyshev.theta x) * Real.sqrt x / x := by rw [hxx]
      _ = _ := by field_simp
  rw [hG, hψθ]
  unfold nicolasDefect mertensProductError mertensError
  ring

/-- **Nicolas's constant `2 + a₁` along primes.**  Under RH, for every `ε > 0`:
`Nic(p) √p log p > 2 + a₁ - ε` for infinitely many primes `p`, and
`2 - a₁ - ε < Nic(x) √x log x < 2 + a₁ + ε` for all large `x`. -/
theorem nicolasDefect_scaled_limsup_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    (∃ᶠ p : ℕ in atTop, p.Prime ∧ 2 + poleSharpConstant - ε
      < nicolasDefect p * (Real.sqrt p * Real.log p)) ∧
    ∀ᶠ x : ℝ in atTop, 2 - poleSharpConstant - ε < nicolasDefect x * (Real.sqrt x * Real.log x)
      ∧ nicolasDefect x * (Real.sqrt x * Real.log x) < 2 + poleSharpConstant + ε := by
  have hT := tendsto_nicolasDefect_scaled_sub_lag hRH
  have hev : ∀ᶠ x : ℝ in atTop, |nicolasDefect x * (Real.sqrt x * Real.log x)
      - weilLagFunctionReal (Real.log x) - 2| < ε / 2 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hT).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    simpa [Real.norm_eq_abs] using this
  have hΦ : ∀ L : ℝ, |weilLagFunctionReal L| ≤ poleSharpConstant := fun L => by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH L
    rwa [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  constructor
  · have hnat := tendsto_natCast_atTop_atTop.eventually hev
    refine ((frequently_prime_integerLag_gt (show 0 < ε / 2 by positivity)).and_eventually
      hnat).mono fun p ⟨⟨hp, hlag⟩, hclose⟩ => ⟨hp, ?_⟩
    unfold integerLag at hlag
    have := (abs_lt.mp hclose).1
    linarith
  · filter_upwards [hev] with x hx
    have h1 := (abs_lt.mp hx)
    have h2 := abs_le.mp (hΦ (Real.log x))
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end

end RHTower
