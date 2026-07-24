import GaloisForLFunctions.RHTower.MLadderContraction

/-!
# The m-window contraction in closed form

For a cutoff `c ≥ 8Q` wide enough that the top usable block keeps fibers
above `c/(2Q) − 1`, choosing the ladder height `J = log_{2Q}(⌊N/(cx₁)⌋)`:

`∑_{x₁ < m ≤ N} (2 log m + 2)·|R(⌊N/m⌋)|
   ≤ N·((a − θ)·(G(N) − G(x₁))
       + (2 log N + 1)·3a·(2 log N + 8)/x₁
       + 8·(2 log N + 8)/x₁ + 8·log c·(2 log N + 2))`,

`G = log² + 2 log`, `θ = (a − ε')·ρ/(8·log(2Q))`.  The ladder covers
`(x₁, x₁(2Q)^{J+1}]` with at most `2 log N + 1` blocks; the tail
`(x₁(2Q)^{J+1}, N]` has log-length at most `log c` by maximality of `J`
and is priced by the crude remainder bound `|R(j)| ≤ 8j`, so it costs
only `O(log N)` against the `log² N`-sized main term.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1600000 in
theorem m_window_contraction_of_ratio {a δ ρ κ : ℝ} {Q x₀ x₁ c N : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁8 : 8 ≤ x₁) (hx₁ρ : 8 / ρ ≤ (x₁ : ℝ))
    (hx₁Q : Real.log ((2 * Q : ℕ) : ℝ) + 2 ≤ 2 * Real.log x₁)
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hc8 : 8 * Q ≤ c)
    (hρc : 2 / ρ ≤ (c : ℝ) / (2 * Q) - 1)
    (hx₀c : (x₀ : ℝ) ≤ (c : ℝ) / (2 * Q) - 1)
    (hcx₁N : c * x₁ ≤ N)
    (hjunkc : ∀ t : ℕ, (c : ℝ) / (2 * Q) - 1 ≤ (t : ℝ) →
      Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t) :
    ∑ m ∈ Finset.Ioc x₁ N,
        (2 * Real.log m + 2) * |psiRemainder (N / m)|
      ≤ (N : ℝ) * ((a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * ρ
            / (8 * Real.log ((2 * Q : ℕ) : ℝ)))
          * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        + 8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)) := by
  set ε' : ℝ := δ + ρ * (Real.log (1 / ρ) + 3) + κ with hε'
  set L : ℝ := Real.log ((2 * Q : ℕ) : ℝ) with hL
  set θ : ℝ := (a - ε') * ρ / (8 * L) with hθ
  have hεa : ε' ≤ a := hε'a
  have hε'0 : 0 ≤ ε' := by
    have hρlog0 : 0 ≤ Real.log (1 / ρ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hρ0, one_mul]; linarith)
    rw [hε']
    positivity
  have hLhalf : 1 / 2 ≤ L := by
    have h1 : Real.log 2 ≤ L := by
      rw [hL]
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (by omega : 2 ≤ 2 * Q)
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  have hx₁0 : 0 < x₁ := by omega
  have hx₁0R : (0 : ℝ) < x₁ := by exact_mod_cast hx₁0
  have hlogx₁0 : 0 ≤ Real.log x₁ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x₁))
  have hc0 : 0 < c := by omega
  have hN0 : 0 < N := by
    have : 0 < c * x₁ := Nat.mul_pos hc0 hx₁0
    omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlogN0 : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hQR0 : (0 : ℝ) < 2 * (Q : ℝ) := by
    have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    linarith
  -- ladder height and its basic inequalities
  set J : ℕ := Nat.log (2 * Q) (N / (c * x₁)) with hJdef
  have hcx₁0 : 0 < c * x₁ := Nat.mul_pos hc0 hx₁0
  have hM1 : 1 ≤ N / (c * x₁) :=
    (Nat.le_div_iff_mul_le hcx₁0).2 (by omega)
  have hpowJ : (2 * Q) ^ J ≤ N / (c * x₁) := by
    rw [hJdef]
    exact Nat.pow_log_le_self (2 * Q) (by omega)
  have hYpos : 0 < x₁ * (2 * Q) ^ J :=
    Nat.mul_pos hx₁0 (pow_pos (by omega) J)
  have hY1pos : 0 < x₁ * (2 * Q) ^ (J + 1) :=
    Nat.mul_pos hx₁0 (pow_pos (by omega) (J + 1))
  have hx₁Y : x₁ ≤ x₁ * (2 * Q) ^ J :=
    Nat.le_mul_of_pos_right x₁ (pow_pos (by omega) J)
  have hx₁Y1 : x₁ ≤ x₁ * (2 * Q) ^ (J + 1) :=
    Nat.le_mul_of_pos_right x₁ (pow_pos (by omega) (J + 1))
  -- `c·Y_J ≤ N`
  have hcY : c * (x₁ * (2 * Q) ^ J) ≤ N := by
    have h1 : x₁ * (2 * Q) ^ J ≤ x₁ * (N / (c * x₁)) :=
      Nat.mul_le_mul le_rfl hpowJ
    have h2 : c * (x₁ * (N / (c * x₁))) = (N / (c * x₁)) * (c * x₁) := by
      ring
    have h3 : (N / (c * x₁)) * (c * x₁) ≤ N := Nat.div_mul_le_self N _
    have h4 : c * (x₁ * (2 * Q) ^ J) ≤ c * (x₁ * (N / (c * x₁))) :=
      Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hpowJ)
    omega
  -- top-block usability `8Q·Y_J ≤ N`
  have h8QY : 8 * Q * (x₁ * (2 * Q) ^ J) ≤ N := by
    have h1 : 8 * Q * (x₁ * (2 * Q) ^ J) ≤ c * (x₁ * (2 * Q) ^ J) :=
      Nat.mul_le_mul_right _ hc8
    omega
  have hQY0 : 0 < 2 * Q * (x₁ * (2 * Q) ^ J) :=
    Nat.mul_pos (by omega) hYpos
  -- the top-block fiber floor `⌊N/(2Q·Y_J)⌋ ≥ c/(2Q) − 1`
  have hWc : (c : ℝ) / (2 * Q) - 1
      ≤ ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) := by
    have hdm := Nat.div_add_mod N (2 * Q * (x₁ * (2 * Q) ^ J))
    have hml := Nat.mod_lt N hQY0
    have h3 : (N : ℝ) = ((2 * Q * (x₁ * (2 * Q) ^ J) : ℕ) : ℝ)
        * ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ)
        + ((N % (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) := by
      exact_mod_cast hdm.symm
    have h4 : ((N % (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ)
        < ((2 * Q * (x₁ * (2 * Q) ^ J) : ℕ) : ℝ) := by
      exact_mod_cast hml
    have hEcast : ((2 * Q * (x₁ * (2 * Q) ^ J) : ℕ) : ℝ)
        = 2 * (Q : ℝ) * ((x₁ * (2 * Q) ^ J : ℕ) : ℝ) := by
      push_cast
      ring
    have hYR : (0 : ℝ) < ((x₁ * (2 * Q) ^ J : ℕ) : ℝ) := by
      exact_mod_cast hYpos
    have hcYcast : (c : ℝ) * ((x₁ * (2 * Q) ^ J : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hcY
    -- `c·Y < 2Q·Y·(W+1)` hence `c < 2Q·(W+1)`
    have h5 : (c : ℝ) * ((x₁ * (2 * Q) ^ J : ℕ) : ℝ)
        < (2 * (Q : ℝ)
            * (((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) + 1))
          * ((x₁ * (2 * Q) ^ J : ℕ) : ℝ) := by
      rw [hEcast] at h3 h4
      nlinarith [h3, h4, hcYcast]
    have h6 : (c : ℝ)
        < 2 * (Q : ℝ)
          * (((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) + 1) :=
      lt_of_mul_lt_mul_right h5 hYR.le
    have h7 : (c : ℝ) / (2 * Q)
        < ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hQR0]
      nlinarith [h6]
    linarith
  -- ladder hypotheses at the top block
  have hWρJ : 2 / ρ ≤ ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) :=
    le_trans hρc hWc
  have hx₀J : x₀ ≤ N / (2 * Q * (x₁ * (2 * Q) ^ J)) := by
    have h1 : (x₀ : ℝ) ≤ ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) :=
      le_trans hx₀c hWc
    exact_mod_cast h1
  have hjunkUJ : ∀ t : ℕ, N / (2 * Q * (x₁ * (2 * Q) ^ J)) < t →
      Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t := by
    intro t ht
    apply hjunkc
    have h1 : ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast le_of_lt ht
    linarith [hWc]
  have hladder := m_ladder_contraction ha hδ hρ0 hρ1 hκ hQ1 hQ hx₁8 hx₁ρ
    hx₁Q hε'a hratio J h8QY hWρJ hx₀J hjunkUJ
  rw [← hε', ← hL, ← hθ] at hladder
  -- ladder top `Y_{J+1} ≤ N` and tail shortness `N < c·Y_{J+1}`
  have hY1N : x₁ * (2 * Q) ^ (J + 1) ≤ N := by
    have h1 : x₁ * (2 * Q) ^ (J + 1) = 2 * Q * (x₁ * (2 * Q) ^ J) := by
      ring
    have h2 : 2 * Q * (x₁ * (2 * Q) ^ J)
        ≤ 8 * Q * (x₁ * (2 * Q) ^ J) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hNltcY1 : N < c * (x₁ * (2 * Q) ^ (J + 1)) := by
    have h1 : N / (c * x₁) < (2 * Q) ^ (J + 1) := by
      rw [hJdef]
      exact Nat.lt_pow_succ_log_self (by omega) _
    have hdm := Nat.div_add_mod N (c * x₁)
    have hml := Nat.mod_lt N hcx₁0
    have h2 : (N / (c * x₁) + 1) * (c * x₁)
        ≤ (2 * Q) ^ (J + 1) * (c * x₁) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (N / (c * x₁) + 1) * (c * x₁)
        = c * x₁ * (N / (c * x₁)) + c * x₁ := by ring
    have h4 : (2 * Q) ^ (J + 1) * (c * x₁)
        = c * (x₁ * (2 * Q) ^ (J + 1)) := by ring
    omega
  -- tail: crude remainder ratio `8` on `(Y_{J+1}, N]`
  have htailpt : ∀ m ∈ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N,
      (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ 8 * (N : ℝ) * ((2 * Real.log m + 2) / m) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : 0 < m := by
      have := hY1pos
      omega
    have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
    have hw0 : (0 : ℝ) ≤ 2 * Real.log m + 2 := by
      have := Real.log_nonneg
        (by exact_mod_cast (by omega : 1 ≤ m) : (1 : ℝ) ≤ (m : ℝ))
      linarith
    have hcr := abs_psiRemainder_le (N / m)
    have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
      rw [le_div_iff₀ hm0R]
      exact_mod_cast Nat.div_mul_le_self N m
    calc (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ (2 * Real.log m + 2) * (8 * ((N : ℝ) / m)) := by
          apply mul_le_mul_of_nonneg_left _ hw0
          calc |psiRemainder (N / m)| ≤ 8 * ((N / m : ℕ) : ℝ) := hcr
            _ ≤ 8 * ((N : ℝ) / m) := by linarith
      _ = 8 * (N : ℝ) * ((2 * Real.log m + 2) / m) := by
          field_simp
  have hY1two : 2 ≤ x₁ * (2 * Q) ^ (J + 1) := by omega
  have hM1' := sum_log_harmonic_window_le hY1two hY1N
  have htail : ∑ m ∈ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N,
      (2 * Real.log m + 2) * |psiRemainder (N / m)|
      ≤ 8 * (N : ℝ) * ((Real.log N ^ 2 + 2 * Real.log N)
          - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
            + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
        + (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
          / (x₁ * (2 * Q) ^ (J + 1) : ℕ)) := by
    calc ∑ m ∈ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N,
          (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ ∑ m ∈ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N,
            8 * (N : ℝ) * ((2 * Real.log m + 2) / m) :=
          Finset.sum_le_sum htailpt
      _ = 8 * (N : ℝ) * ∑ m ∈ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N,
            (2 * Real.log m + 2) / m := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hM1' (by positivity)
  -- tail `G`-mass is at most `log c · (2 log N + 2)`
  have hY1R : (0 : ℝ) < ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) := by
    exact_mod_cast hY1pos
  have hlogY1N : Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ)
      ≤ Real.log N :=
    Real.log_le_log hY1R (by exact_mod_cast hY1N)
  have hlogY10 : 0 ≤ Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x₁ * (2 * Q) ^ (J + 1)))
  have hlogc0 : 0 ≤ Real.log c :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
  have hlogNY1 : Real.log N
      ≤ Real.log c + Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) := by
    have h1 : Real.log N ≤ Real.log ((c * (x₁ * (2 * Q) ^ (J + 1)) : ℕ) : ℝ) :=
      Real.log_le_log hNR (by exact_mod_cast le_of_lt hNltcY1)
    have h2 : ((c * (x₁ * (2 * Q) ^ (J + 1)) : ℕ) : ℝ)
        = (c : ℝ) * ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [h2, Real.log_mul (by exact_mod_cast hc0.ne') hY1R.ne'] at h1
    exact h1
  have hGtail : (Real.log N ^ 2 + 2 * Real.log N)
      - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
        + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
      ≤ Real.log c * (2 * Real.log N + 2) := by
    have hfact : (Real.log N ^ 2 + 2 * Real.log N)
        - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
          + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
        = (Real.log N - Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
          * (Real.log N + Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ)
            + 2) := by
      ring
    rw [hfact]
    apply mul_le_mul (by linarith) (by linarith) (by linarith) hlogc0
  -- tail window error normalization
  have htailerr : (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
      / ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ)
      ≤ (2 * Real.log N + 8) / x₁ := by
    have h1 : Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1)
        ≤ Real.log ((N : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      have : ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hY1N
      linarith
    have h2 := log_succ_sub_log_le (j := N) (by omega)
    have h3 : (1 : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNR]
      exact_mod_cast (by omega : 1 ≤ N)
    have hnum0 : 0 ≤ 2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1)
        + 6 := by
      have := Real.log_nonneg
        (show (1 : ℝ) ≤ ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1 by linarith)
      linarith
    calc (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
          / ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ)
        ≤ (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
          / (x₁ : ℝ) := by
          apply div_le_div_of_nonneg_left hnum0 hx₁0R
          exact_mod_cast hx₁Y1
      _ ≤ (2 * Real.log N + 8) / x₁ := by
          apply div_le_div_of_nonneg_right _ hx₁0R.le
          linarith
  -- block count `J + 1 ≤ 2 log N + 1`
  have hJcount : (J : ℝ) ≤ 2 * Real.log N := by
    have h1 : (2 * Q) ^ J ≤ N :=
      le_trans hpowJ (Nat.div_le_self N _)
    have h2 : (((2 * Q) ^ J : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    have h3 : (((2 * Q) ^ J : ℕ) : ℝ) = ((2 * Q : ℕ) : ℝ) ^ J := by
      push_cast
      ring
    have h4 : (J : ℝ) * L ≤ Real.log N := by
      have h5 : Real.log (((2 * Q) ^ J : ℕ) : ℝ) ≤ Real.log N :=
        Real.log_le_log (by rw [h3]; positivity) h2
      rw [h3, Real.log_pow, ← hL] at h5
      exact_mod_cast h5
    nlinarith [h4, hLhalf, (Nat.cast_nonneg J : (0 : ℝ) ≤ (J : ℝ))]
  -- `θ ≤ a`, hence the main coefficient is monotone under `G`-growth
  have hθa : θ ≤ a := by
    have h1 : (a - ε') * ρ ≤ a * (1 / 2) :=
      mul_le_mul (by linarith) hρ1 hρ0.le ha.le
    have h2 : θ ≤ a * (1 / 2) / (8 * L) := by
      rw [hθ]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : a * (1 / 2) / (8 * L) ≤ a * (1 / 2) / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith
    have h4 : a * (1 / 2) / 4 ≤ a := by linarith
    linarith
  have hGmono : Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
      + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ)
      ≤ Real.log N ^ 2 + 2 * Real.log N := by
    have := pow_le_pow_left₀ hlogY10 hlogY1N 2
    linarith
  -- split `(x₁, N]` at the ladder top and combine
  have hsplit : Finset.Ioc x₁ N
      = Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1))
        ∪ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc hx₁Y1 hY1N]
  have hdisj : Disjoint (Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1)))
      (Finset.Ioc (x₁ * (2 * Q) ^ (J + 1)) N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- assemble the two halves against the closed form
  have hb1 : (N : ℝ) * ((a - θ)
        * ((Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
            + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
          - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
      + ((J : ℝ) + 1) * (3 * a * ((2 * Real.log N + 8) / x₁)))
      ≤ (N : ℝ) * ((a - θ)
          * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))) := by
    apply mul_le_mul_of_nonneg_left _ hNR.le
    have hm1 : (a - θ)
        * ((Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
            + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
          - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
        ≤ (a - θ)
          * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log x₁ ^ 2 + 2 * Real.log x₁)) := by
      apply mul_le_mul_of_nonneg_left (by linarith [hGmono])
        (by linarith [hθa])
    have hm2 : ((J : ℝ) + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        ≤ (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁)) := by
      apply mul_le_mul_of_nonneg_right (by linarith [hJcount])
      positivity
    linarith
  have hb2 : 8 * (N : ℝ) * ((Real.log N ^ 2 + 2 * Real.log N)
        - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
          + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
      + (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
        / (x₁ * (2 * Q) ^ (J + 1) : ℕ))
      ≤ (N : ℝ) * (8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)) := by
    have hinner : 8 * ((Real.log N ^ 2 + 2 * Real.log N)
        - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
          + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
        + (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
          / (x₁ * (2 * Q) ^ (J + 1) : ℕ))
        ≤ 8 * ((2 * Real.log N + 8) / x₁)
          + 8 * Real.log c * (2 * Real.log N + 2) := by
      linarith [hGtail, htailerr]
    calc 8 * (N : ℝ) * ((Real.log N ^ 2 + 2 * Real.log N)
          - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
            + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
        + (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
          / (x₁ * (2 * Q) ^ (J + 1) : ℕ))
        = (N : ℝ) * (8 * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ 2
              + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
          + (2 * Real.log (((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) + 1) + 6)
            / (x₁ * (2 * Q) ^ (J + 1) : ℕ))) := by
          ring
      _ ≤ (N : ℝ) * (8 * ((2 * Real.log N + 8) / x₁)
          + 8 * Real.log c * (2 * Real.log N + 2)) :=
          mul_le_mul_of_nonneg_left hinner hNR.le
  have hfinal : (N : ℝ) * ((a - θ)
        * ((Real.log N ^ 2 + 2 * Real.log N)
          - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
      + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁)))
      + (N : ℝ) * (8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2))
      = (N : ℝ) * ((a - θ)
          * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        + 8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)) := by
    ring
  linarith [hladder, htail, hb1, hb2, hfinal]

end RHTower
