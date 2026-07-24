import GaloisForLFunctions.RHTower.SigmaLadderContraction

/-!
# The σ-contraction in closed form

For any `N ≥ x₁`, choosing the ladder height `J = log_{2Q}(N/x₁)`:

`∑_{x₁ < n ≤ N} |R(n)|(1/n − 1/(n+1))
   ≤ (a − θ)·(log N − log x₁) + (g + 14a/x₁)`,

with per-block gain `g = (a − ε')·ρ/3` and contraction rate
`θ = g / log(2Q)`.  The ladder covers `(x₁, x₁(2Q)^J]` exactly
(`log Y_J = log x₁ + J·log(2Q)`), the tail `(Y_J, N]` has log-length at
most `log(2Q)`, and the geometric error sums to `12a/x₁`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1000000 in
theorem sigma_window_contraction_of_ratio {a δ ρ κ : ℝ} {Q x₀ x₁ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q)
    (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁1 : 1 ≤ x₁) (hx₀x₁ : x₀ ≤ x₁) (hx₁ρ : 2 / ρ ≤ (x₁ : ℝ))
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hjunk1 : ∀ t : ℕ, x₁ < t →
      2 * Real.sqrt t * Real.log t ≤ κ / 2 * t)
    (hbase0 : Real.log ((Q * x₁ : ℕ) : ℝ) + 1 ≤ κ / 2 * x₁)
    (hbase : Real.log ((2 * Q : ℕ) : ℝ) ≤ κ / 2 * x₁)
    {N : ℕ} (hx₁N : x₁ ≤ N) :
    ∑ n ∈ Finset.Ioc x₁ N,
        |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ (a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            / Real.log ((2 * Q : ℕ) : ℝ))
          * (Real.log N - Real.log x₁)
        + ((a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
          + 14 * a / x₁) := by
  set g : ℝ := (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3) with hg
  set L : ℝ := Real.log ((2 * Q : ℕ) : ℝ) with hL
  have hg0 : 0 ≤ g := by
    rw [hg]
    exact mul_nonneg (by linarith) (by linarith)
  have hL0 : 0 < L := by
    rw [hL]
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * Q)
  have hx₁0 : 0 < x₁ := by omega
  have hx₁R : (0 : ℝ) < x₁ := by exact_mod_cast hx₁0
  -- ladder height
  set J : ℕ := Nat.log (2 * Q) (N / x₁) with hJ
  have hNx₁ : N / x₁ ≠ 0 := by
    have : 1 ≤ N / x₁ := (Nat.le_div_iff_mul_le hx₁0).2 (by omega)
    omega
  have hJle : x₁ * (2 * Q) ^ J ≤ N := by
    have h1 : (2 * Q) ^ J ≤ N / x₁ := Nat.pow_log_le_self (2 * Q) hNx₁
    have h2 : (2 * Q) ^ J * x₁ ≤ N :=
      (Nat.le_div_iff_mul_le hx₁0).1 h1
    have h3 : x₁ * (2 * Q) ^ J = (2 * Q) ^ J * x₁ := Nat.mul_comm _ _
    omega
  have hJlt : N < x₁ * (2 * Q) ^ (J + 1) := by
    have h1 : N / x₁ < (2 * Q) ^ (J + 1) :=
      Nat.lt_pow_succ_log_self (by omega) (N / x₁)
    have h2 : N < (N / x₁ + 1) * x₁ := by
      have h3 := Nat.div_add_mod N x₁
      have h4 := Nat.mod_lt N hx₁0
      have hexp : (N / x₁ + 1) * x₁ = N / x₁ * x₁ + x₁ := by ring
      have hcomm : x₁ * (N / x₁) = N / x₁ * x₁ := Nat.mul_comm _ _
      omega
    have h5 : (N / x₁ + 1) * x₁ ≤ (2 * Q) ^ (J + 1) * x₁ := by
      apply Nat.mul_le_mul_right
      omega
    have h6 : x₁ * (2 * Q) ^ (J + 1) = (2 * Q) ^ (J + 1) * x₁ :=
      Nat.mul_comm _ _
    omega
  set Y : ℕ := x₁ * (2 * Q) ^ J with hY
  have hY1 : 1 ≤ Y := by
    rw [hY]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega)
      (Nat.pos_iff_ne_zero.1 (pow_pos (by omega) J)))
  have hx₁Y : x₁ ≤ Y := by
    rw [hY]
    exact Nat.le_mul_of_pos_right x₁ (pow_pos (by omega) J)
  -- exact ladder log
  have hlogY : Real.log ((Y : ℕ) : ℝ) = Real.log x₁ + (J : ℝ) * L := by
    rw [hY, hL]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  -- ladder bound
  have hladder := sigma_ladder_contraction ha hδ hρ0 hρ1 hκ hQ1 hQ hx₁1
    hx₀x₁ hx₁ρ hε'a hratio hjunk1 hbase0 hbase J
  -- geometric error
  have hgeom : ∑ j ∈ Finset.range J, 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)
      ≤ 12 / x₁ := by
    have hterm : ∀ j ∈ Finset.range J,
        6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)
          ≤ 6 / x₁ * ((1 : ℝ) / 2) ^ j := by
      intro j _
      have h1 : (x₁ : ℝ) * 2 ^ j ≤ ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
        push_cast
        have h2 : (2 : ℝ) ^ j ≤ (2 * Q : ℝ) ^ j := by
          apply pow_le_pow_left₀ (by norm_num)
          have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
          linarith
        nlinarith [h2, hx₁R]
      have h3 : (0 : ℝ) < (x₁ : ℝ) * 2 ^ j := by positivity
      calc 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)
          ≤ 6 / ((x₁ : ℝ) * 2 ^ j) :=
            div_le_div_of_nonneg_left (by norm_num) h3 h1
        _ = 6 / x₁ * ((1 : ℝ) / 2) ^ j := by
            rw [div_pow, one_pow]
            field_simp
    calc ∑ j ∈ Finset.range J, 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)
        ≤ ∑ j ∈ Finset.range J, 6 / x₁ * ((1 : ℝ) / 2) ^ j :=
          Finset.sum_le_sum hterm
      _ = 6 / x₁ * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ 6 / x₁ * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [geom_sum_eq (by norm_num)]
          have h2 : ((1 : ℝ) / 2) ^ J ≤ 1 :=
            pow_le_one₀ (by norm_num) (by norm_num)
          have h3 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ J :=
            pow_nonneg (by norm_num) J
          rw [div_le_iff_of_neg (by norm_num : (1 : ℝ) / 2 - 1 < 0)]
          linarith
      _ = 12 / x₁ := by ring
  -- tail bound
  have htail : ∑ n ∈ Finset.Ioc Y N,
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ a * (Real.log N - Real.log Y + 2 / Y) := by
    have hpart : ∀ n ∈ Finset.Ioc Y N,
        |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          ≤ a * (1 / ((n : ℝ) + 1)) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hR := hratio n (by omega)
      have hnw : (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      have hwpos : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [sub_nonneg]
        apply div_le_div_of_nonneg_left one_pos.le hn0
        linarith
      calc |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          ≤ (a * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hR hwpos
        _ = a * ((n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by ring
        _ = a * (1 / ((n : ℝ) + 1)) := by rw [hnw]
    have hH := abs_le.1 (abs_sum_inv_succ_window_sub_le hY1 hJle)
    calc ∑ n ∈ Finset.Ioc Y N,
          |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ ∑ n ∈ Finset.Ioc Y N, a * (1 / ((n : ℝ) + 1)) :=
          Finset.sum_le_sum hpart
      _ = a * ∑ n ∈ Finset.Ioc Y N, 1 / ((n : ℝ) + 1) := by
          rw [Finset.mul_sum]
      _ ≤ a * (Real.log N - Real.log Y + 2 / Y) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          linarith [hH.2]
  -- split and combine
  have hsplit : Finset.Ioc x₁ N = Finset.Ioc x₁ Y ∪ Finset.Ioc Y N := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc hx₁Y hJle]
  have hdisj : Disjoint (Finset.Ioc x₁ Y) (Finset.Ioc Y N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- quantitative combination
  have hDle : Real.log N - Real.log x₁ ≤ ((J : ℝ) + 1) * L := by
    have h1 : (N : ℝ) < (x₁ : ℝ) * ((2 * Q : ℕ) : ℝ) ^ (J + 1) := by
      have := hJlt
      push_cast
      exact_mod_cast this
    have h2 : Real.log N ≤ Real.log ((x₁ : ℝ)
        * ((2 * Q : ℕ) : ℝ) ^ (J + 1)) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < N))
      linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
    rw [hL]
    push_cast at h2 ⊢
    linarith
  have hquot : (Real.log N - Real.log x₁) / L ≤ (J : ℝ) + 1 := by
    rw [div_le_iff₀ hL0]
    linarith [hDle]
  have hgainquot : g * ((Real.log N - Real.log x₁) / L)
      ≤ g * ((J : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hquot hg0
  have h2Y : 2 / (Y : ℝ) ≤ 2 / x₁ := by
    apply div_le_div_of_nonneg_left (by norm_num) hx₁R
    exact_mod_cast hx₁Y
  have hYR : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have egoal : (a - g / L) * (Real.log N - Real.log x₁)
      = a * (Real.log N - Real.log x₁)
        - g * ((Real.log N - Real.log x₁) / L) := by
    ring
  have e12 : a * (12 / (x₁ : ℝ)) + a * (2 / x₁) = 14 * a / x₁ := by
    ring
  have hgeom' : a * (∑ j ∈ Finset.range J,
      6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)) ≤ a * (12 / x₁) :=
    mul_le_mul_of_nonneg_left hgeom ha.le
  have ha2Y : a * (2 / (Y : ℝ)) ≤ a * (2 / x₁) :=
    mul_le_mul_of_nonneg_left h2Y ha.le
  -- expand the tail bound and ladder bound, then close linearly
  have etail : a * (Real.log N - Real.log ((Y : ℕ) : ℝ) + 2 / Y)
      = a * (Real.log N - Real.log ((Y : ℕ) : ℝ)) + a * (2 / Y) := by
    ring
  have eladder : a * (Real.log ((Y : ℕ) : ℝ) - Real.log x₁)
      + a * (Real.log N - Real.log ((Y : ℕ) : ℝ))
      = a * (Real.log N - Real.log x₁) := by
    ring
  rw [← hY] at hladder
  rw [← hg] at hladder
  rw [egoal]
  linarith [hladder, htail, hgeom', ha2Y, hgainquot, etail, eladder, e12,
    hlogY]

end RHTower
