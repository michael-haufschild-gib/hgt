import GaloisForLFunctions.LogarithmicChowla.TwistTransfer

/-!
# `V(b/s, T) → 0`

* (A4) `normSq_dilWin_principal_le`: `λχ₀(m) = λ(m)[(m, q) = 1] = Σ_{e|q, e|m} μ(e)λ(m)` and
  `λ(ek) = λ(e)λ(k)`, so the window of `λχ₀` is `Σ_{e|q} μ(e)λ(e)` times dilated windows of `λ` with
  dilation `ge`: `|dilWin_g(λχ₀)|² ≤ τ(q) Σ_{e|q} |dilWin_{ge}(λ)|²`.
* (A5) `tendsto_twistVar_zero`: by (A3) and (A4), `V(b/s, T)` is at most a fixed linear combination
  of `L(|T^{-1} dilWin_g(λχ)|²)`, `χ ≠ 1`, and `L(|T^{-1} dilWin_{ge}(λ)|²)`; each tends to zero by
  (A2) (`tendsto_limAvg_dilWin`) with Matomäki–Radziwiłł for `λχ` and for `λ`.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {U : Ultrafilter ℝ}

/-- The principal character mod `q` is the coprimality indicator. -/
theorem trivialChar_mod_apply {q : ℕ} (m : ℕ) :
    (1 : DirichletCharacter ℂ q) m = if Nat.Coprime m q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime m q).mpr h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime m q).mp hu))

/-- `Σ_{d | N} μ(d) = [N = 1]`. -/
theorem sum_divisors_moebius_eq (N : ℕ) :
    ∑ d ∈ N.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if N = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F N) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

/-- Coprimality through the Möbius function. -/
theorem coprime_indicator_eq {q : ℕ} (hq : 0 < q) {m : ℕ} (hm : 0 < m) :
    (if Nat.Coprime m q then (1 : ℂ) else 0)
      = ∑ e ∈ q.divisors.filter (· ∣ m), ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
  have hset : q.divisors.filter (· ∣ m) = (Nat.gcd m q).divisors := by
    ext e
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨heq, -⟩, hem⟩; exact ⟨⟨hem, heq⟩, (Nat.gcd_pos_of_pos_left q hm).ne'⟩
    · rintro ⟨⟨hem, heq⟩, -⟩; exact ⟨⟨heq, hq.ne'⟩, hem⟩
  rw [hset, sum_divisors_moebius_eq]

/-- The multiples of `e` in a dilated window form a dilated window. -/
theorem sum_dilWin_dvd (F : ℕ → ℂ) {g e : ℕ} (hg : 1 ≤ g) (he : 1 ≤ e) (n T : ℕ) :
    ∑ m ∈ ((range (n + T)).filter (fun m => n ≤ g * m ∧ g * m < n + T)).filter (e ∣ ·), F m
      = dilWin (fun k => F (e * k)) (g * e) n T := by
  refine Finset.sum_nbij' (fun m => m / e) (fun k => e * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_filter, mem_filter, mem_range] at hm
    obtain ⟨⟨hm1, hm2, hm3⟩, k, hk⟩ := hm
    rw [mem_filter, mem_range]
    show m / e < n + T ∧ n ≤ g * e * (m / e) ∧ g * e * (m / e) < n + T
    rw [hk, Nat.mul_div_cancel_left k (by omega), mul_assoc, ← hk]
    have hkm : k ≤ m := by rw [hk]; exact Nat.le_mul_of_pos_left k (by omega)
    omega
  · intro k hk
    rw [mem_filter, mem_range] at hk
    obtain ⟨-, hk1, hk2⟩ := hk
    rw [mem_filter, mem_filter, mem_range]
    rw [mul_assoc] at hk1 hk2
    have hek : e * k ≤ g * (e * k) := Nat.le_mul_of_pos_left _ (by omega)
    exact ⟨⟨by omega, hk1, hk2⟩, k, rfl⟩
  · intro m hm
    rw [mem_filter] at hm
    obtain ⟨-, k, hk⟩ := hm
    show e * (m / e) = m
    rw [hk, Nat.mul_div_cancel_left k (by omega)]
  · intro k _
    show e * k / e = k
    exact Nat.mul_div_cancel_left k (by omega)
  · intro m hm
    rw [mem_filter] at hm
    obtain ⟨-, k, hk⟩ := hm
    show F m = F (e * (m / e))
    rw [hk, Nat.mul_div_cancel_left k (by omega)]

/-- **(A4) Principal windows through dilated windows of `λ`.** -/
theorem normSq_dilWin_principal_le {q : ℕ} (hq : 0 < q) {g : ℕ} (hg : 1 ≤ g) (n T : ℕ) :
    ‖dilWin (twLiouville (1 : DirichletCharacter ℂ q)) g n T‖ ^ 2
      ≤ (q.divisors.card : ℝ) * ∑ e ∈ q.divisors,
          ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (g * e) n T‖ ^ 2 := by
  -- `λχ₀(m) = Σ_{e|q, e|m} μ(e) λ(m)`
  have hpt : ∀ m, twLiouville (1 : DirichletCharacter ℂ q) m
      = ∑ e ∈ q.divisors, if e ∣ m then ((ArithmeticFunction.moebius e : ℤ) : ℂ)
          * (ArithmeticFunction.liouville m : ℂ) else 0 := by
    intro m
    rw [twLiouville, trivialChar_mod_apply, ← sum_filter]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [coprime_indicator_eq hq hm, mul_sum]
      exact sum_congr rfl fun e _ => mul_comm _ _
  have hwin : dilWin (twLiouville (1 : DirichletCharacter ℂ q)) g n T
      = ∑ e ∈ q.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ)
          * (ArithmeticFunction.liouville e : ℂ)
          * dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (g * e) n T := by
    rw [dilWin]
    simp_rw [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
    rw [← Finset.sum_filter, ← Finset.mul_sum,
      sum_dilWin_dvd (fun m => (ArithmeticFunction.liouville m : ℂ)) hg he1, mul_assoc]
    congr 1
    rw [dilWin, dilWin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.liouville_apply_mul]
    push_cast; ring
  rw [hwin]
  have hb : ‖∑ e ∈ q.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ)
      * (ArithmeticFunction.liouville e : ℂ)
      * dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (g * e) n T‖
      ≤ ∑ e ∈ q.divisors, ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (g * e) n T‖ := by
    refine le_trans (norm_sum_le _ _) (sum_le_sum fun e he => ?_)
    have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
    have hμ : ‖((ArithmeticFunction.moebius e : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hlv : ‖(ArithmeticFunction.liouville e : ℂ)‖ ≤ 1 := by
      rw [ArithmeticFunction.liouville_apply he0]
      push_cast
      rw [norm_pow, norm_neg, norm_one, one_pow]
    rw [norm_mul, norm_mul]
    have h1 : ‖((ArithmeticFunction.moebius e : ℤ) : ℂ)‖ * ‖(ArithmeticFunction.liouville e : ℂ)‖
        ≤ 1 := by
      have := mul_le_mul hμ hlv (norm_nonneg _) zero_le_one
      linarith
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have h3 := sq_sum_le_card_mul_sum_sq (s := q.divisors)
    (f := fun e => ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (g * e) n T‖)
  exact le_trans h2 h3

theorem bdd_dilWin_sq {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {D : ℕ} (hD : 1 ≤ D) (T : ℕ) :
    Bdd fun n => ‖dilWin f D n T‖ ^ 2 / (T : ℝ) ^ 2 := by
  refine ⟨((T : ℝ) + 1) ^ 2 / (T : ℝ) ^ 2, fun n => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_dilWin_le hf hD n T) 2) (by positivity)

/-- (A2) as a limit. -/
theorem tendsto_limAvg_dilWin (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hMR : DyadicMR f) {D : ℕ} (hD : 1 ≤ D) :
    Tendsto (fun T : ℕ => limAvg U (fun n => ‖dilWin f D n T‖ ^ 2 / (T : ℝ) ^ 2)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := exists_limAvg_dilWin_le hU hf hMR hD (ε := ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h0 := limAvg_nonneg hU (bdd_dilWin_sq hf hD T) (fun n => by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith [hT₀ T hT]

theorem dyadicMR_twLiouville {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    DyadicMR (twLiouville χ) :=
  fun _ hε => exists_short_sum_mean_square_twLiouville_le χ hχ hε

theorem dyadicMR_liouville : DyadicMR fun m => (ArithmeticFunction.liouville m : ℂ) :=
  fun _ hε => exists_short_sum_mean_square_liouville_le hε

theorem norm_liouville_le (m : ℕ) : ‖(ArithmeticFunction.liouville m : ℂ)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [ArithmeticFunction.liouville_apply hm.ne']
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]

end

end GaloisForLFunctions.LogarithmicChowla
