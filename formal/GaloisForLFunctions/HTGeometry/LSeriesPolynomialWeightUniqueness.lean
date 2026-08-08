import Mathlib

/-!
# Polynomial-weighted L-series families vanish coefficientwise

If finitely many L-series with polynomial weights sum to zero along the real ray,
`∑_{a ≤ A} x^a · L(g_a)(x) = 0` for all real `x ≥ x₀`, then every coefficient `g a n` with
`n ≥ 1` vanishes.  The mechanism is a two-level induction: the least surviving index `n` is
peeled with the exponential domination `‖n^x·L(g)(x) − g n‖ ≤ C·(n/(n+1))^x`, which beats every
polynomial weight, and the polynomial coefficients are then read off from a complex polynomial
expression tending to zero along the real ray.

This is the uniqueness backbone for coefficientwise identification of algebraic-differential
expressions in ordinary Dirichlet series.
-/

namespace GaloisForLFunctions

open Filter Topology LSeries

noncomputable section

/-- A complex polynomial expression tending to zero along the real ray has zero coefficients. -/
theorem coeff_eq_zero_of_tendsto_zero :
    ∀ (A : ℕ) (c : ℕ → ℂ),
      Tendsto (fun x : ℝ => ∑ a ∈ Finset.range (A + 1), c a * (x : ℂ) ^ a)
        atTop (𝓝 0) →
      ∀ a ≤ A, c a = 0 := by
  intro A
  induction A with
  | zero =>
      intro c h a ha
      interval_cases a
      have hconst : Tendsto (fun _ : ℝ => c 0) atTop (𝓝 (c 0)) := tendsto_const_nhds
      have heq : (fun x : ℝ => ∑ a ∈ Finset.range 1, c a * (x : ℂ) ^ a) =
          fun _ : ℝ => c 0 := by
        funext x
        simp
      rw [heq] at h
      exact tendsto_nhds_unique hconst h
  | succ A ih =>
      intro c h
      have hcastfun : ∀ k : ℕ, (Complex.ofReal ∘ fun x : ℝ => ((x : ℝ) ^ k)⁻¹) =
          fun x : ℝ => ((x : ℂ) ^ k)⁻¹ := by
        intro k
        funext x
        simp only [Function.comp_apply]
        push_cast
        rfl
      have hinvk : ∀ k : ℕ, k ≠ 0 →
          Tendsto (fun x : ℝ => ((x : ℂ) ^ k)⁻¹) atTop (𝓝 0) := by
        intro k hk
        have hreal : Tendsto (fun x : ℝ => ((x : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
          (tendsto_pow_atTop hk).inv_tendsto_atTop
        have hcast := (Complex.continuous_ofReal.tendsto 0).comp hreal
        rw [hcastfun k] at hcast
        simpa using hcast
      have htop : Tendsto
          (fun x : ℝ => (∑ a ∈ Finset.range (A + 2), c a * (x : ℂ) ^ a) *
            ((x : ℂ) ^ (A + 1))⁻¹) atTop (𝓝 0) := by
        simpa using h.mul (hinvk (A + 1) (Nat.succ_ne_zero A))
      have hsum : Tendsto
          (fun x : ℝ => (∑ a ∈ Finset.range (A + 2), c a * (x : ℂ) ^ a) *
            ((x : ℂ) ^ (A + 1))⁻¹) atTop (𝓝 (c (A + 1))) := by
        have hterm : ∀ a ∈ Finset.range (A + 2),
            Tendsto (fun x : ℝ => c a * ((x : ℂ) ^ (A + 1 - a))⁻¹) atTop
              (𝓝 (if a = A + 1 then c a else 0)) := by
          intro a ha
          rw [Finset.mem_range] at ha
          by_cases hcase : a = A + 1
          · subst hcase
            simp only [Nat.sub_self, pow_zero, inv_one, mul_one, if_pos]
            exact tendsto_const_nhds
          · rw [if_neg hcase]
            have hinv' := hinvk (A + 1 - a) (by omega)
            simpa using (tendsto_const_nhds (x := c a)).mul hinv'
        have hlim := tendsto_finsetSum (Finset.range (A + 2)) hterm
        have hval : (∑ a ∈ Finset.range (A + 2),
            if a = A + 1 then c a else 0) = c (A + 1) := by
          rw [Finset.sum_ite_eq' (Finset.range (A + 2))]
          simp
        rw [hval] at hlim
        apply hlim.congr'
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        have hx0 : (x : ℂ) ≠ 0 := by
          exact_mod_cast (by linarith : x ≠ 0)
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_range] at ha
        have hsplit : (x : ℂ) ^ (A + 1) = (x : ℂ) ^ (A + 1 - a) * (x : ℂ) ^ a := by
          rw [← pow_add]
          congr 1
          omega
        rw [mul_assoc]
        congr 1
        rw [hsplit, mul_inv]
        rw [mul_comm (((x : ℂ) ^ (A + 1 - a))⁻¹), ← mul_assoc]
        rw [mul_inv_cancel₀ (pow_ne_zero _ hx0), one_mul]
      have hc : c (A + 1) = 0 := tendsto_nhds_unique hsum htop
      have hred : Tendsto (fun x : ℝ => ∑ a ∈ Finset.range (A + 1), c a * (x : ℂ) ^ a)
          atTop (𝓝 0) := by
        apply h.congr'
        filter_upwards with x
        rw [Finset.sum_range_succ, hc]
        simp
      intro a ha
      rcases Nat.lt_or_ge a (A + 1) with hlt | hge
      · exact ih c hred a (by omega)
      · have haeq : a = A + 1 := by omega
        rw [haeq]
        exact hc

/-- **Exponential domination of the pinned tail.**  If the coefficients of `g` vanish strictly
below `n ≥ 1`, then `n^x · L(g)(x)` approaches `g n` at a geometric rate that beats every
polynomial weight. -/
theorem exists_norm_pow_mul_LSeries_sub_le {g : ℕ → ℂ} {n : ℕ} (hn : 1 ≤ n) {x₁ : ℝ}
    (hsum : LSeriesSummable g (x₁ : ℂ))
    (hvan : ∀ m, 1 ≤ m → m < n → g m = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₁ ≤ x →
      ‖(((n : ℝ) ^ x : ℝ) : ℂ) * LSeries g (x : ℂ) - g n‖ ≤
        C * ((n : ℝ) / (n + 1)) ^ x := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hθpos : (0 : ℝ) < (n : ℝ) / (n + 1) := by positivity
  set θ : ℝ := (n : ℝ) / (n + 1) with hθ
  -- dominating coefficients at exponent x₁
  set c : ℕ → ℝ := fun m => if m ≤ n then 0 else ‖g m‖ * ((n : ℝ) ^ x₁ / (m : ℝ) ^ x₁)
    with hcdef
  have hcnonneg : ∀ m, 0 ≤ c m := by
    intro m
    rw [hcdef]
    by_cases hm : m ≤ n
    · simp [hm]
    · simp only [if_neg hm]
      positivity
  have hceq : ∀ m, n < m →
      c m = (n : ℝ) ^ x₁ * ‖term g (x₁ : ℂ) m‖ := by
    intro m hm
    rw [hcdef]
    simp only [if_neg (by omega : ¬ m ≤ n)]
    rw [LSeries.term_def, if_neg (by omega : m ≠ 0), norm_div,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < m)]
    simp only [Complex.ofReal_re]
    ring
  have hcsum : Summable c := by
    apply Summable.of_nonneg_of_le hcnonneg _ (hsum.norm.mul_left ((n : ℝ) ^ x₁))
    intro m
    by_cases hm : m ≤ n
    · rw [hcdef]
      simp only [if_pos hm]
      positivity
    · rw [hceq m (by omega)]
  set C₀ : ℝ := ∑' m, c m with hC₀def
  have hC₀nonneg : 0 ≤ C₀ := tsum_nonneg hcnonneg
  refine ⟨C₀ * θ ^ (-x₁), by positivity, ?_⟩
  intro x hx
  have hsumx : LSeriesSummable g (x : ℂ) := hsum.of_re_le_re (by simpa using hx)
  have hscaled : Summable fun m => (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) m :=
    hsumx.mul_left _
  have hnc_ne : ((n : ℂ)) ^ ((x : ℂ)) ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
    simp only [Complex.ofReal_re]
    positivity
  have hterm_n : (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) n = g n := by
    rw [LSeries.term_def, if_neg (by omega : n ≠ 0), Complex.ofReal_cpow hn0.le]
    push_cast
    field_simp
  have hLmul : (((n : ℝ) ^ x : ℝ) : ℂ) * LSeries g (x : ℂ) =
      ∑' m, (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) m := by
    rw [LSeries, tsum_mul_left]
  -- pointwise domination of the off-pin terms
  have hpoint : ∀ m : ℕ,
      ‖if m = n then 0 else (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) m‖ ≤
        c m * θ ^ (x - x₁) := by
    intro m
    by_cases hmn : m = n
    · simp only [if_pos hmn, norm_zero]
      positivity
    rw [if_neg hmn]
    rcases Nat.lt_or_ge m (n + 1) with hml | hmg
    · -- below or at the pin: the term vanishes
      have hterm0 : term g (x : ℂ) m = 0 := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm1
        · rw [hm0]
          exact LSeries.term_zero g _
        · rw [LSeries.term_def, if_neg (by omega : m ≠ 0),
            hvan m hm1 (by omega), zero_div]
      rw [hterm0, mul_zero, norm_zero]
      positivity
    · -- above the pin: geometric decay
      have hm0 : 0 < m := by omega
      have hnm : (n : ℝ) < m := by exact_mod_cast (by omega : n < m)
      rw [norm_mul, LSeries.term_def, if_neg (by omega : m ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hm0]
      simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hn0 x)]
      have hratio : (n : ℝ) ^ x * (‖g m‖ / (m : ℝ) ^ x) =
          (‖g m‖ * ((n : ℝ) ^ x₁ / (m : ℝ) ^ x₁)) * ((n : ℝ) / (m : ℝ)) ^ (x - x₁) := by
        rw [Real.div_rpow hn0.le (by positivity : (0:ℝ) ≤ (m:ℝ))]
        rw [Real.rpow_sub hn0, Real.rpow_sub (by positivity : (0:ℝ) < (m:ℝ))]
        field_simp
      have hcm : ‖g m‖ * ((n : ℝ) ^ x₁ / (m : ℝ) ^ x₁) = c m := by
        rw [hcdef]
        simp only [if_neg (by omega : ¬ m ≤ n)]
      rw [hratio, hcm]
      apply mul_le_mul_of_nonneg_left _ (hcnonneg m)
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      rw [hθ, div_le_div_iff₀ (by positivity) (by positivity)]
      have hm1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : n + 1 ≤ m)
      nlinarith
  -- assemble the tail bound
  have hdom_sum : Summable fun m => c m * θ ^ (x - x₁) := hcsum.mul_right _
  have hnorm_sum : Summable fun m =>
      ‖if m = n then 0 else (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) m‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hpoint hdom_sum
  have hsplit := hscaled.tsum_eq_add_tsum_ite n
  rw [hLmul, hsplit, hterm_n, add_sub_cancel_left]
  calc ‖∑' m, if m = n then 0 else (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) m‖
      ≤ ∑' m, ‖if m = n then 0 else (((n : ℝ) ^ x : ℝ) : ℂ) * term g (x : ℂ) m‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' m, c m * θ ^ (x - x₁) := Summable.tsum_le_tsum hpoint hnorm_sum hdom_sum
    _ = C₀ * θ ^ (x - x₁) := by rw [tsum_mul_right]
    _ = C₀ * θ ^ (-x₁) * θ ^ x := by
        rw [show x - x₁ = -x₁ + x by ring, Real.rpow_add hθpos, ← mul_assoc]

/-- **Polynomial-weighted L-series uniqueness.**  A finite polynomially weighted family of
L-series vanishing along a real ray has identically zero coefficients at every positive index. -/
theorem lseries_polyWeightFamily_coeff_eq_zero
    {A : ℕ} (g : ℕ → ℕ → ℂ) {x₀ : ℝ}
    (hsum : ∀ a, a ≤ A → LSeriesSummable (g a) ((x₀ : ℝ) : ℂ))
    (hzero : ∀ x : ℝ, x₀ ≤ x →
      ∑ a ∈ Finset.range (A + 1), (x : ℂ) ^ a * LSeries (g a) (x : ℂ) = 0) :
    ∀ n, 1 ≤ n → ∀ a, a ≤ A → g a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn a ha
    have hvan : ∀ b, b ≤ A → ∀ m, 1 ≤ m → m < n → g b m = 0 := by
      intro b hb m hm1 hmn
      exact IH m hmn hm1 b hb
    have hCex : ∀ b, b ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
        ‖(((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n‖ ≤
          C * ((n : ℝ) / (n + 1)) ^ x := by
      intro b hb
      exact exists_norm_pow_mul_LSeries_sub_le hn (hsum b hb) (hvan b hb)
    choose! C hC0 hCle using hCex
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set θ : ℝ := (n : ℝ) / (n + 1) with hθ
    have hθpos : (0 : ℝ) < θ := by positivity
    have hθlt : θ < 1 := by
      rw [hθ, div_lt_one (by positivity)]
      linarith
    have hdomtend : Tendsto (fun x : ℝ =>
        (∑ b ∈ Finset.range (A + 1), C b) * (x ^ A * θ ^ x)) atTop (𝓝 0) := by
      have hb0 : 0 < -Real.log θ := by
        have := Real.log_neg hθpos hθlt
        linarith
      have hcomp : Tendsto (fun x : ℝ => -Real.log θ * x) atTop atTop :=
        Tendsto.const_mul_atTop hb0 tendsto_id
      have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp hcomp
      have hmul := hbase.const_mul (((-Real.log θ) ^ A)⁻¹)
      have hfun : (fun x : ℝ => ((-Real.log θ) ^ A)⁻¹ *
          ((fun t : ℝ => t ^ A * Real.exp (-t)) ∘ fun x : ℝ => -Real.log θ * x) x) =
          fun x : ℝ => x ^ A * θ ^ x := by
        funext x
        simp only [Function.comp_apply]
        rw [mul_pow, Real.rpow_def_of_pos hθpos]
        have hbA : ((-Real.log θ) ^ A) ≠ 0 := by positivity
        field_simp
      rw [hfun] at hmul
      have := hmul.const_mul (∑ b ∈ Finset.range (A + 1), C b)
      simpa using this
    have hq : Tendsto (fun x : ℝ =>
        ∑ b ∈ Finset.range (A + 1), g b n * (x : ℂ) ^ b) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ hdomtend
      filter_upwards [eventually_ge_atTop (max x₀ 1)] with x hx
      have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
      have hkey : (∑ b ∈ Finset.range (A + 1), g b n * (x : ℂ) ^ b) =
          -(∑ b ∈ Finset.range (A + 1), (x : ℂ) ^ b *
            ((((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n)) := by
        have h0 := hzero x hx₀
        calc (∑ b ∈ Finset.range (A + 1), g b n * (x : ℂ) ^ b)
            = (((n : ℝ) ^ x : ℝ) : ℂ) *
                (∑ b ∈ Finset.range (A + 1), (x : ℂ) ^ b * LSeries (g b) (x : ℂ)) -
              (∑ b ∈ Finset.range (A + 1), (x : ℂ) ^ b *
                ((((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n)) := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro b _
              ring
          _ = -(∑ b ∈ Finset.range (A + 1), (x : ℂ) ^ b *
                ((((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n)) := by
              rw [h0, mul_zero, zero_sub]
      rw [hkey, norm_neg]
      calc ‖∑ b ∈ Finset.range (A + 1), (x : ℂ) ^ b *
            ((((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n)‖
          ≤ ∑ b ∈ Finset.range (A + 1), ‖(x : ℂ) ^ b *
            ((((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ b ∈ Finset.range (A + 1), C b * (x ^ A * θ ^ x) := by
            apply Finset.sum_le_sum
            intro b hb
            rw [Finset.mem_range] at hb
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by linarith : (0 : ℝ) < x)]
            calc x ^ b * ‖(((n : ℝ) ^ x : ℝ) : ℂ) * LSeries (g b) (x : ℂ) - g b n‖
                ≤ x ^ A * (C b * θ ^ x) := by
                  apply mul_le_mul (pow_le_pow_right₀ hx1 (by omega))
                    (hCle b (by omega) x hx₀) (norm_nonneg _) (by positivity)
              _ = C b * (x ^ A * θ ^ x) := by ring
        _ = (∑ b ∈ Finset.range (A + 1), C b) * (x ^ A * θ ^ x) := by
            rw [← Finset.sum_mul]
    exact coeff_eq_zero_of_tendsto_zero A (fun b => g b n) hq a ha

end

end GaloisForLFunctions
