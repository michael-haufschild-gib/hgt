import GaloisForLFunctions.RHTower.Matveev.FeldmanExtrapolation

/-!
# Parameters for Fel'dman's extrapolation

All parameters except the polynomial degree `N = a n` and the initial node count `X₀ = c n` are
constants, `n ≍ log B`.  The common divisor beats the polynomial factor up to a linear cost,

`(ρ + N + 1)^N ≤ D(N + 1, S) · e^{ρ + (N+1)(1 + κ_S)}`,  `κ_S = (log 4 + 4)(3 + 2 log₂ S)`,

so every quantity of the extrapolation is `e^{O(n)}`.  The gain `(2/7)^{MX}` of one step beats the
growth once `M` dominates `q W`, and the Hermite and `Λ` terms are absorbed by `|Λ| < e^{−C₀ n}`.
The constants are fixed by `FeldmanParams`, whose conditions all reduce to `poly(R) ≤ 2^R`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Real

/-- Fel'dman's divisor exponent `κ_S = (log 4 + 4)(3 + 2 log₂ S)`. -/
def feldmanKappa (S : ℕ) : ℝ := (Real.log 4 + 4) * (3 + 2 * (Nat.log 2 S : ℝ))

theorem feldmanKappa_nonneg (S : ℕ) : 0 ≤ feldmanKappa S := by
  unfold feldmanKappa
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

theorem feldmanKappa_le {S R : ℕ} (h : Nat.log 2 S ≤ R) : feldmanKappa S ≤ 18 + 12 * R := by
  unfold feldmanKappa
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl := Real.log_two_lt_d9
  have hR : (Nat.log 2 S : ℝ) ≤ R := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ Nat.log 2 S := Nat.cast_nonneg _
  have hL : Real.log 4 + 4 ≤ 6 := by rw [h4]; linarith
  have hL0 : 0 ≤ Real.log 4 + 4 := by rw [h4]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  calc (Real.log 4 + 4) * (3 + 2 * (Nat.log 2 S : ℝ)) ≤ 6 * (3 + 2 * (R : ℝ)) := by
        apply mul_le_mul hL (by linarith) (by positivity) (by norm_num)
    _ = 18 + 12 * R := by ring

/-- `k^k ≤ k! e^k`. -/
theorem pow_self_le_factorial_mul_exp (k : ℕ) :
    (k : ℝ) ^ k ≤ (k.factorial : ℝ) * Real.exp k := by
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  linarith

/-- `(N + 1)! ≤ D(N + 1, S) e^{κ_S (N + 1)}`. -/
theorem factorial_le_feldmanDivisor_mul_exp (N S : ℕ) :
    ((N + 1).factorial : ℝ) ≤ feldmanDivisor (N + 1) S * Real.exp ((N + 1) * feldmanKappa S) := by
  have h := log_factorial_sub_log_feldmanDivisor_le (N + 1) S
  have hD : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hf : (0 : ℝ) < ((N + 1).factorial : ℝ) := by exact_mod_cast (N + 1).factorial_pos
  rw [← Real.exp_log hf]
  calc Real.exp (Real.log ((N + 1).factorial : ℝ)) ≤
      Real.exp (Real.log (feldmanDivisor (N + 1) S) + (N + 1) * feldmanKappa S) := by
        apply Real.exp_le_exp.mpr
        unfold feldmanKappa
        push_cast at h ⊢
        linarith
    _ = feldmanDivisor (N + 1) S * Real.exp ((N + 1) * feldmanKappa S) := by
        rw [Real.exp_add, Real.exp_log hD]

/-- **The common divisor against the polynomial factor.** -/
theorem pow_le_feldmanDivisor_mul_exp (N S : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (ρ + N + 1) ^ N ≤
      feldmanDivisor (N + 1) S * Real.exp (ρ + (N + 1) * (1 + feldmanKappa S)) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hbase : (1 : ℝ) ≤ ρ + N + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  have h1 : (ρ + N + 1) ^ N ≤ (ρ + N + 1) ^ (N + 1) := pow_le_pow_right₀ hbase (Nat.le_succ N)
  have h2 : (ρ + N + 1) ^ (N + 1) ≤ ((N : ℝ) + 1) ^ (N + 1) * Real.exp ρ := by
    have hsplit : ρ + N + 1 = ((N : ℝ) + 1) * (ρ / ((N : ℝ) + 1) + 1) := by
      field_simp; ring
    have hexp : (ρ / ((N : ℝ) + 1) + 1) ^ (N + 1) ≤ Real.exp ρ := by
      calc (ρ / ((N : ℝ) + 1) + 1) ^ (N + 1) ≤ (Real.exp (ρ / ((N : ℝ) + 1))) ^ (N + 1) :=
            pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
        _ = Real.exp ρ := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
    rw [hsplit, mul_pow]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have h3 : ((N : ℝ) + 1) ^ (N + 1) ≤ ((N + 1).factorial : ℝ) * Real.exp ((N : ℝ) + 1) := by
    exact_mod_cast pow_self_le_factorial_mul_exp (N + 1)
  have h4 := factorial_le_feldmanDivisor_mul_exp N S
  have hD : (0 : ℝ) ≤ feldmanDivisor (N + 1) S := by positivity
  calc (ρ + N + 1) ^ N ≤ ((N : ℝ) + 1) ^ (N + 1) * Real.exp ρ := h1.trans h2
    _ ≤ ((N + 1).factorial : ℝ) * Real.exp ((N : ℝ) + 1) * Real.exp ρ :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ ≤ feldmanDivisor (N + 1) S * Real.exp ((N + 1) * feldmanKappa S) *
          Real.exp ((N : ℝ) + 1) * Real.exp ρ := by
        gcongr
    _ = feldmanDivisor (N + 1) S * Real.exp (ρ + (N + 1) * (1 + feldmanKappa S)) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2; ring

/-! ## The constants -/

/-- The constants of the extrapolation for `m + 1` primes with `Σ log p_j ≤ Wb`. -/
structure FeldmanParams (m Wb : ℕ) where
  /-- the number of extrapolation steps -/
  R : ℕ
  /-- the jet order consumed per step -/
  M : ℕ
  /-- the exponent box size -/
  q : ℕ
  /-- the initial derivative order -/
  S : ℕ
  /-- `X₀ = c n` -/
  c : ℕ
  /-- `N = a n` -/
  a : ℕ
  one_le_R : 1 ≤ R
  one_le_q : 1 ≤ q
  one_le_c : 1 ≤ c
  S_eq : S = R * M + 1
  M_ge : 4 * (9 + 17 * q * Wb) ≤ M
  siegel : 2 * c * S ^ (m + 1) ≤ a * q ^ (m + 1)
  terminal : 2 * a * q ^ (m + 1) ≤ 2 ^ R * c
  logS : Nat.log 2 S ≤ R
  gain : 4 * ((m + 1) * S * (1 + 2 * q) + 4 * a + 2 * (m + 1) * q + 2 * (a + 1) * (19 + 12 * R) + 1)
    ≤ 3 * M * c

/-- A polynomial is eventually below `2^R`. -/
theorem exists_mul_pow_le_two_pow (K D : ℕ) : ∃ R : ℕ, 1 ≤ R ∧ K * (R + 1) ^ D ≤ 2 ^ R := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt D (one_lt_two : (1 : ℝ) < 2)
  have hK : (0 : ℝ) < 1 / ((K : ℝ) * 2 ^ D + 1) := by positivity
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp
    ((h.eventually (gt_mem_nhds hK)).and (Filter.eventually_ge_atTop 1))
  obtain ⟨hlt, hR1⟩ := hR₀ R₀ le_rfl
  refine ⟨R₀, hR1, ?_⟩
  have h2R : (0 : ℝ) < 2 ^ R₀ := by positivity
  have hR1' : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR1
  rw [div_lt_div_iff₀ h2R (by positivity), one_mul] at hlt
  have hpow : ((R₀ : ℝ) + 1) ^ D ≤ 2 ^ D * (R₀ : ℝ) ^ D := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) D
  have hreal : (K : ℝ) * ((R₀ : ℝ) + 1) ^ D ≤ 2 ^ R₀ := by
    calc (K : ℝ) * ((R₀ : ℝ) + 1) ^ D ≤ (K : ℝ) * (2 ^ D * (R₀ : ℝ) ^ D) :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg K)
      _ = ((K : ℝ) * 2 ^ D) * (R₀ : ℝ) ^ D := by ring
      _ ≤ ((K : ℝ) * 2 ^ D + 1) * (R₀ : ℝ) ^ D := by
          have : (0 : ℝ) ≤ (R₀ : ℝ) ^ D := by positivity
          nlinarith
      _ = (R₀ : ℝ) ^ D * ((K : ℝ) * 2 ^ D + 1) := by ring
      _ ≤ 2 ^ R₀ := hlt.le
  exact_mod_cast hreal

/-- The size identity behind the choice of `R`. -/
theorem feldman_pow_identity (E R Wb m : ℕ) (hE : E = 1000 * Wb * (R + 1)) :
    4 * E ^ (m + 1) * (E ^ (m + 1) * (R + 1)) ^ (m + 1) =
      4 * (1000 * Wb) ^ ((m + 1) * (m + 2)) * (R + 1) ^ ((m + 1) * (m + 2) + (m + 1)) := by
  have hk : (m + 1) + (m + 1) * (m + 1) = (m + 1) * (m + 2) := by ring
  calc 4 * E ^ (m + 1) * (E ^ (m + 1) * (R + 1)) ^ (m + 1)
      = 4 * (E ^ (m + 1) * E ^ ((m + 1) * (m + 1))) * (R + 1) ^ (m + 1) := by
        rw [mul_pow, ← pow_mul]; ring
    _ = 4 * E ^ ((m + 1) * (m + 2)) * (R + 1) ^ (m + 1) := by rw [← pow_add, hk]
    _ = 4 * (1000 * Wb) ^ ((m + 1) * (m + 2)) * (R + 1) ^ ((m + 1) * (m + 2) + (m + 1)) := by
        rw [hE, mul_pow, pow_add]; ring

/-- **The constants exist.** -/
theorem exists_feldmanParams (m Wb : ℕ) (hWb : 1 ≤ Wb) : Nonempty (FeldmanParams m Wb) := by
  obtain ⟨R, hR1, hR⟩ := exists_mul_pow_le_two_pow (4 * (1000 * Wb) ^ ((m + 1) * (m + 2)))
    ((m + 1) * (m + 2) + (m + 1))
  obtain ⟨E, hE⟩ : ∃ E, E = 1000 * Wb * (R + 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = E ^ (m + 1) * (R + 1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 1000 * Wb * q := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = R * M + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 16 * (m + 1) * (R + 1) * q := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * c * E ^ (m + 1) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hc1 : 1 ≤ c := by rw [hc]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpoly : 4 * E ^ (m + 1) * q ^ (m + 1) ≤ 2 ^ R := by
    rw [hq, feldman_pow_identity E R Wb m hE]; exact hR
  have hWq : 1 ≤ Wb * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hSEq : S ≤ E * q := by
    have h1 : E * q = R * (1000 * Wb * q) + 1000 * (Wb * q) := by rw [hE]; ring
    rw [hS, hM, h1]
    omega
  have hEq : E * q ≤ 4 * E ^ (m + 1) * q ^ (m + 1) := by
    have h1 : E ≤ E ^ (m + 1) := Nat.le_self_pow (Nat.succ_ne_zero m) E
    have h2 : q ≤ q ^ (m + 1) := Nat.le_self_pow (Nat.succ_ne_zero m) q
    calc E * q ≤ E ^ (m + 1) * q ^ (m + 1) := Nat.mul_le_mul h1 h2
      _ ≤ 4 * E ^ (m + 1) * q ^ (m + 1) := by
          rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)
  have haq : a = 32 * ((m + 1) * q * q) := by
    rw [ha, hc, hq]; ring
  refine ⟨⟨R, M, q, S, c, a, hR1, hq1, hc1, hS, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h : 1000 * Wb * q = 1000 * (Wb * q) := by ring
    have h' : 4 * (9 + 17 * q * Wb) = 36 + 68 * (Wb * q) := by ring
    rw [hM, h, h']
    omega
  · calc 2 * c * S ^ (m + 1) ≤ 2 * c * (E * q) ^ (m + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSEq _)
      _ = a * q ^ (m + 1) := by rw [ha, mul_pow]; ring
  · calc 2 * a * q ^ (m + 1) = c * (4 * E ^ (m + 1) * q ^ (m + 1)) := by rw [ha]; ring
      _ ≤ c * 2 ^ R := Nat.mul_le_mul_left _ hpoly
      _ = 2 ^ R * c := by ring
  · have hlt : S < 2 ^ (R + 1) := by
      calc S ≤ 2 ^ R := hSEq.trans (hEq.trans hpoly)
        _ < 2 ^ (R + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self R)
    have := Nat.log_lt_of_lt_pow (show S ≠ 0 by rw [hS]; omega) hlt
    omega
  · -- the gain inequality
    obtain ⟨u, hu⟩ : ∃ u, u = (m + 1) * Wb * q * q := ⟨_, rfl⟩
    have hu1 : 1 ≤ u := by rw [hu]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hRWq : 1 ≤ R * Wb * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hSle : S ≤ 1001 * (R * Wb * q) := by
      have h : R * M = 1000 * (R * Wb * q) := by rw [hM]; ring
      rw [hS, h]; omega
    have h1 : (m + 1) * S * (1 + 2 * q) ≤ 3003 * R * u := by
      calc (m + 1) * S * (1 + 2 * q) ≤ (m + 1) * (1001 * (R * Wb * q)) * (3 * q) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hSle) (by omega)
        _ = 3003 * R * u := by rw [hu]; ring
    have hqq : (m + 1) * q * q ≤ u := by
      rw [hu]
      calc (m + 1) * q * q = (m + 1) * 1 * q * q := by ring
        _ ≤ (m + 1) * Wb * q * q := by gcongr
    have h2 : 4 * a ≤ 128 * u := by
      rw [haq]
      calc 4 * (32 * ((m + 1) * q * q)) = 128 * ((m + 1) * q * q) := by ring
        _ ≤ 128 * u := Nat.mul_le_mul_left _ hqq
    have h3 : 2 * (m + 1) * q ≤ 2 * u := by
      have : (m + 1) * q ≤ (m + 1) * q * q := Nat.le_mul_of_pos_right _ (by omega)
      calc 2 * (m + 1) * q = 2 * ((m + 1) * q) := by ring
        _ ≤ 2 * u := Nat.mul_le_mul_left _ (this.trans hqq)
    have h4 : 2 * (a + 1) * (19 + 12 * R) ≤ 66 * u * (19 + 12 * R) := by
      have ha1 : a + 1 ≤ 33 * u := by
        rw [haq]
        have := Nat.mul_le_mul_left 32 hqq
        omega
      calc 2 * (a + 1) * (19 + 12 * R) ≤ 2 * (33 * u) * (19 + 12 * R) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha1)
        _ = 66 * u * (19 + 12 * R) := by ring
    calc 4 * ((m + 1) * S * (1 + 2 * q) + 4 * a + 2 * (m + 1) * q + 2 * (a + 1) * (19 + 12 * R)
          + 1)
        ≤ 4 * (3003 * R * u + 128 * u + 2 * u + 66 * u * (19 + 12 * R) + u) := by gcongr
      _ = u * (15180 * R + 5540) := by ring
      _ ≤ u * (48000 * (R + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * M * c := by rw [hM, hc, hu]; ring

end GaloisForLFunctions.RHTower.Matveev
