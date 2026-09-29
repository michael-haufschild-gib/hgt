import GaloisForLFunctions.RHTower.PrimeDeletionWindowedMeanSquare

/-!
# Integer-supported perturbations of the primes have integer error `Ω(x^{κ/2-ε})`

Let an integer-supported Beurling system have integer masses `a` (`|a n| ≤ 1`, `a 1 = 1`) and
generator von Mangoldt function `Λ - e`, so `(Λ - e) ⋆ a = a · log`.  Suppose every nonzero value of
the perturbation has size at least `log 2`, as holds for deleted primes and for added integer
generators, and that its Chebyshev function has a regular expansion
`Σ_{ρ∈J} c_ρ x^ρ + O(x^η)` with leading term `c_κ x^κ`, `Re c_κ ≠ 0` of either sign,
`Re ρ < κ ≤ 1` otherwise, `0 ≤ η < κ/2`.  Then `Σ_{n ≤ x} a n - A x ≠ O(x^θ)` for every `θ < κ/2`
(`IntegerBeurling.not_isBigO_count_of_leading_chebyshev`).

The floor is an `ℓ²` phenomenon on integer atoms: `Σ_{n ≤ N} e(n)² n^{-2σ}` diverges for
`σ < κ/2`, because each nonzero `e(n)` carries mass at least `log 2 · |e(n)|` and
`Σ_{n ≤ N} |e n| ≥ |Σ_{n ≤ N} e n| ≍ N^κ`.  If the count were regular below `x^{κ/2}`, the continued
`L(e)` would be `O(log t)` on some `Re s = σ < κ/2` (`exists_norm_pertLogDeriv_le_log`), capping every
Gaussian-windowed mean square by `O(log² t)` (`head_mass_le_of_log_bound`).  The linearized pairing
with the head `Σ_{n≤u} e(n) n^{-σ-it}`, whose frequencies are separated because distinct integers
are, forces the mean square to be `≫ u^{κ-2σ}` (`eventually_head_mass_ge`).

For a set `Q` of deleted primes (`e = Λ_Q`) this gives
`PrimeDeletion.not_isBigO_qFreeCount_of_leading_chebyshev_complex` and its real and
multiplicity forms: discrete multiplicative uncertainty holds on all regular deletions.
-/

open Filter Topology Complex Asymptotics MeasureTheory Set Metric
open scoped Interval

namespace RHTower

noncomputable section

namespace IntegerBeurling

variable {a e : ℕ → ℝ}

/-- The leading term of the perturbation's Chebyshev function dominates eventually. -/
theorem eventually_half_mul_rpow_le_abs_pertChebyshev {η κ : ℝ} {J : Finset ℂ} {c : ℂ → ℂ}
    (hηκ : η < κ) (hκJ : (κ : ℂ) ∈ J) (hcκ : (c κ).re ≠ 0) (hJκ : ∀ ρ ∈ J, ρ ≠ κ → ρ.re < κ)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η) :
    ∀ᶠ x : ℝ in atTop, |(c κ).re| / 2 * x ^ κ ≤ |pertChebyshev e x| := by
  classical
  have hcκ' : 0 < |(c κ).re| := abs_pos.mpr hcκ
  obtain ⟨m, hmκ, hηm, hJm⟩ : ∃ m : ℝ, m < κ ∧ η ≤ m ∧ ∀ ρ ∈ J.erase (κ : ℂ), ρ.re ≤ m := by
    by_cases hne : (J.erase (κ : ℂ)).Nonempty
    · refine ⟨max η ((J.erase (κ : ℂ)).sup' hne Complex.re), max_lt hηκ ?_, le_max_left _ _,
        fun ρ hρ => le_trans (Finset.le_sup' Complex.re hρ) (le_max_right _ _)⟩
      rw [Finset.sup'_lt_iff]
      intro ρ hρ
      exact hJκ ρ (Finset.mem_of_mem_erase hρ) (Finset.ne_of_mem_erase hρ)
    · exact ⟨η, hηκ, le_rfl, fun ρ hρ => absurd ⟨ρ, hρ⟩ hne⟩
  obtain ⟨CD, hCD⟩ := hψ.bound
  set K : ℝ := ∑ ρ ∈ J.erase (κ : ℂ), ‖c ρ‖ + |CD| with hK
  have htend : Tendsto (fun x : ℝ => K * x ^ (m - κ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < κ - m by linarith)).const_mul K
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    congr 2; ring
  have hsmall : ∀ᶠ x : ℝ in atTop, K * x ^ (m - κ) ≤ |(c κ).re| / 2 :=
    htend.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hCD, hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hxs hx1
  have hx0 : 0 < x := by linarith
  have hsplit : ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ =
      c κ * (x : ℂ) ^ (κ : ℂ) + ∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ :=
    (Finset.add_sum_erase J _ hκJ).symm
  have hκpow : (x : ℂ) ^ (κ : ℂ) = ((x ^ κ : ℝ) : ℂ) := (Complex.ofReal_cpow hx0.le κ).symm
  have hrest : ‖∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ‖ ≤
      (∑ ρ ∈ J.erase (κ : ℂ), ‖c ρ‖) * x ^ m := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (hJm ρ hρ))
      (norm_nonneg _)
  have hD : ‖(pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ‖ ≤ |CD| * x ^ m := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx
    exact hx.trans (mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hx1 hηm)
      (Real.rpow_pos_of_pos hx0 _).le (abs_nonneg _))
  have hreeq : ((∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) - (pertChebyshev e x : ℂ)).re =
      (c κ).re * x ^ κ + (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ).re - pertChebyshev e x := by
    rw [Complex.sub_re, hsplit, Complex.add_re, hκpow, Complex.re_mul_ofReal, Complex.ofReal_re]
  have h1 := Complex.abs_re_le_norm ((∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) - (pertChebyshev e x : ℂ))
  rw [norm_sub_rev, hreeq] at h1
  have h3 := Complex.abs_re_le_norm (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ)
  have hxm : K * x ^ m ≤ |(c κ).re| / 2 * x ^ κ := by
    have := mul_le_mul_of_nonneg_right hxs (Real.rpow_pos_of_pos hx0 κ).le
    rw [mul_assoc, ← Real.rpow_add hx0, show m - κ + κ = m by ring] at this
    exact this
  have hKx : K * x ^ m = (∑ ρ ∈ J.erase (κ : ℂ), ‖c ρ‖) * x ^ m + |CD| * x ^ m := by
    rw [hK]; ring
  have hlead : |(c κ).re * x ^ κ| = |(c κ).re| * x ^ κ := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 κ)]
  have htri := abs_sub_abs_le_abs_sub ((c κ).re * x ^ κ)
    (pertChebyshev e x - (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ).re)
  have habs1 : |(c κ).re * x ^ κ - (pertChebyshev e x -
      (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ).re)| ≤ |CD| * x ^ m := by
    have : (c κ).re * x ^ κ - (pertChebyshev e x -
        (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ).re) =
        (c κ).re * x ^ κ + (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ).re - pertChebyshev e x := by
      ring
    rw [this]; linarith
  have habs2 : |pertChebyshev e x - (∑ ρ ∈ J.erase (κ : ℂ), c ρ * (x : ℂ) ^ ρ).re| ≤
      |pertChebyshev e x| + (∑ ρ ∈ J.erase (κ : ℂ), ‖c ρ‖) * x ^ m := by
    refine (abs_sub _ _).trans ?_
    linarith
  rw [hlead] at htri
  linarith

/-- **Head mass.**  Eventually `Σ_{n ≤ N} (e(n) n^{-σ})² ≥ (log 2 · |Re c_κ|/2) N^{κ-2σ}`. -/
theorem eventually_head_mass_ge (hint : ∀ n, e n = 0 ∨ Real.log 2 ≤ |e n|) {η κ σ : ℝ}
    {J : Finset ℂ} {c : ℂ → ℂ} (hσ : 0 ≤ σ) (hηκ : η < κ) (hκJ : (κ : ℂ) ∈ J)
    (hcκ : (c κ).re ≠ 0) (hJκ : ∀ ρ ∈ J, ρ ≠ κ → ρ.re < κ)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η) :
    ∀ᶠ N : ℕ in atTop, Real.log 2 * (|(c κ).re| / 2) * (N : ℝ) ^ (κ - 2 * σ) ≤
      ∑ n ∈ Finset.Icc 1 N, (e n * (n : ℝ) ^ (-σ)) ^ 2 := by
  have h := (eventually_half_mul_rpow_le_abs_pertChebyshev hηκ hκJ hcκ hJκ hψ).natCast_atTop
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hψN : pertChebyshev e N = ∑ n ∈ Finset.Icc 1 N, e n := by
    unfold pertChebyshev; rw [Nat.floor_natCast]
  rw [hψN] at hN
  have hNabs := hN.trans (Finset.abs_sum_le_sum_abs _ _)
  have hterm : ∀ n ∈ Finset.Icc 1 N, Real.log 2 * (N : ℝ) ^ (-2 * σ) * |e n| ≤
      (e n * (n : ℝ) ^ (-σ)) ^ 2 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : (N : ℝ) ^ (-2 * σ) ≤ (n : ℝ) ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hn0 hnN (by linarith)
    have hsq : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
    rw [mul_pow, hsq, ← sq_abs (e n)]
    rcases hint n with h0 | h2
    · rw [h0]; simp
    · have : Real.log 2 * |e n| ≤ |e n| ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      have hNp : 0 ≤ (N : ℝ) ^ (-2 * σ) := Real.rpow_nonneg hN0.le _
      calc Real.log 2 * (N : ℝ) ^ (-2 * σ) * |e n|
          = (N : ℝ) ^ (-2 * σ) * (Real.log 2 * |e n|) := by ring
        _ ≤ (n : ℝ) ^ (-2 * σ) * |e n| ^ 2 :=
            mul_le_mul hpow this (by positivity) (Real.rpow_nonneg hn0.le _)
        _ = |e n| ^ 2 * (n : ℝ) ^ (-2 * σ) := by ring
  calc Real.log 2 * (|(c κ).re| / 2) * (N : ℝ) ^ (κ - 2 * σ)
      = Real.log 2 * (N : ℝ) ^ (-2 * σ) * (|(c κ).re| / 2 * (N : ℝ) ^ κ) := by
        rw [show κ - 2 * σ = -2 * σ + κ by ring, Real.rpow_add hN0]; ring
    _ ≤ Real.log 2 * (N : ℝ) ^ (-2 * σ) * ∑ n ∈ Finset.Icc 1 N, |e n| := by
        apply mul_le_mul_of_nonneg_left hNabs
        exact mul_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg hN0.le _)
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log 2 * (N : ℝ) ^ (-2 * σ) * |e n| := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- `u^k e^{-u²/c} → 0`. -/
theorem tendsto_pow_mul_exp_neg_sq_div {k : ℕ} {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => u ^ k * Real.exp (-(u ^ 2 / c))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ 2 / c) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).atTop_div_const hc
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp h1
  have h3 := h2.const_mul (c ^ k)
  rw [mul_zero] at h3
  refine squeeze_zero' ?_ ?_ h3
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    simp only [Function.comp]
    have hpow : u ^ k ≤ c ^ k * (u ^ 2 / c) ^ k := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero k hc.ne'), ← pow_mul]
      exact pow_le_pow_right₀ hu (by omega)
    calc u ^ k * Real.exp (-(u ^ 2 / c)) ≤ c ^ k * (u ^ 2 / c) ^ k * Real.exp (-(u ^ 2 / c)) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = c ^ k * ((u ^ 2 / c) ^ k * Real.exp (-(u ^ 2 / c))) := by ring

/-- A power of `⌊u⌋` beats the square of a logarithm. -/
theorem eventually_sq_log_add_lt {K A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, (K * Real.log (3 * u ^ 4 / 2)) ^ 2 + 2 < A * (⌊u⌋₊ : ℝ) ^ δ := by
  set K' : ℝ := K ^ 2 * 25 * (4 / δ) ^ 2 with hK'
  set A' : ℝ := A * (2 : ℝ) ^ (-δ) with hA'
  have hA'0 : 0 < A' := by rw [hA']; positivity
  have ht : Tendsto (fun u : ℝ => K' * u ^ (-(δ / 2)) + 2 * u ^ (-δ)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop (show 0 < δ / 2 by linarith)).const_mul K'
    have h2 := (tendsto_rpow_neg_atTop hδ).const_mul 2
    rw [mul_zero] at h1 h2
    simpa using h1.add h2
  filter_upwards [ht.eventually (gt_mem_nhds hA'0), eventually_ge_atTop (2 : ℝ)] with u hu hu2
  have hu0 : 0 < u := by linarith
  have hfl : u / 2 ≤ (⌊u⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one u
    linarith
  have hN : A' * u ^ δ ≤ A * (⌊u⌋₊ : ℝ) ^ δ := by
    rw [hA', mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA.le
    calc (2 : ℝ) ^ (-δ) * u ^ δ = (u / 2) ^ δ := by
          rw [Real.div_rpow hu0.le (by norm_num), Real.rpow_neg (by norm_num)]; ring
      _ ≤ (⌊u⌋₊ : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) hfl hδ.le
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (3 * u ^ 4 / 2) ≤ 5 * Real.log u := by
    have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu2
    calc Real.log (3 * u ^ 4 / 2) ≤ Real.log (2 * u ^ 4) :=
          Real.log_le_log (by positivity) (by have := pow_pos hu0 4; linarith)
      _ = Real.log 2 + 4 * Real.log u := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 5 * Real.log u := by linarith
  have hlog0 : 0 ≤ Real.log (3 * u ^ 4 / 2) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ (by linarith)
    linarith
  have hlog2 : Real.log u ≤ 4 / δ * u ^ (δ / 4) := by
    have := Real.log_le_rpow_div hu0.le (show 0 < δ / 4 by linarith)
    calc Real.log u ≤ u ^ (δ / 4) / (δ / 4) := this
      _ = 4 / δ * u ^ (δ / 4) := by field_simp
  have hsq : (K * Real.log (3 * u ^ 4 / 2)) ^ 2 ≤ K' * u ^ (δ / 2) := by
    have hb : Real.log (3 * u ^ 4 / 2) ≤ 5 * (4 / δ * u ^ (δ / 4)) := by nlinarith
    have hb0 : 0 ≤ 5 * (4 / δ * u ^ (δ / 4)) := by positivity
    calc (K * Real.log (3 * u ^ 4 / 2)) ^ 2 = K ^ 2 * Real.log (3 * u ^ 4 / 2) ^ 2 := by ring
      _ ≤ K ^ 2 * (5 * (4 / δ * u ^ (δ / 4))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hb 2) (sq_nonneg K)
      _ = K' * u ^ (δ / 2) := by
          rw [hK', mul_pow, mul_pow, ← Real.rpow_natCast (u ^ (δ / 4)), ← Real.rpow_mul hu0.le]
          ring_nf
  have hkey : K' * u ^ (δ / 2) + 2 < A' * u ^ δ := by
    have hud : 0 < u ^ δ := Real.rpow_pos_of_pos hu0 δ
    have h1 : K' * u ^ (-(δ / 2)) * u ^ δ = K' * u ^ (δ / 2) := by
      rw [mul_assoc, ← Real.rpow_add hu0]; ring_nf
    have h2 : 2 * u ^ (-δ) * u ^ δ = 2 := by
      rw [mul_assoc, ← Real.rpow_add hu0]; simp
    have := mul_lt_mul_of_pos_right hu hud
    rw [add_mul, h1, h2] at this
    exact this
  linarith

/-- **The windowed errors collapse.**  With `T = u⁴`, `W = u²` and `n ≤ N ≤ u`, the three errors of
`norm_windowed_line_integral_sub_le` are at most `M u⁷ e^{-u²/32}`. -/
theorem windowed_error_le {u σ CF Z₂ Zσ : ℝ} (hu : 1 ≤ u) (hσ0 : 0 < σ) (hσ3 : σ ≤ 3)
    (hCF : 0 ≤ CF) (hZ₂ : 0 ≤ Z₂) (hZσ : 0 ≤ Zσ) {n N : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hNu : (N : ℝ) ≤ u) :
    2 * (3 - σ) * (Real.exp ((9 - (u ^ 4) ^ 2 / 4) / (u ^ 2) ^ 2) * (n : ℝ) ^ (3 : ℝ) *
        ((3 + 2 * u ^ 4) * CF)) +
      Real.exp ((3 - σ) ^ 2 / (u ^ 2) ^ 2) * (n : ℝ) ^ (3 - σ) * Z₂ *
        Real.exp (-((u ^ 4) ^ 2 / (8 * (u ^ 2) ^ 2))) * (Real.sqrt Real.pi * (Real.sqrt 2 * u ^ 2)) +
      Real.sqrt Real.pi * u ^ 2 * (4 * (N : ℝ) ^ 2 * Real.exp (-((u ^ 2) ^ 2 / (32 * (N : ℝ) ^ 2)))) *
        Zσ ≤
      (30 * Real.exp 9 * CF + 4 * Real.exp 9 * Z₂ + 8 * Zσ) * (u ^ 7 * Real.exp (-(u ^ 2 / 32))) := by
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hnN) hNu
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (le_trans hn1 hnN)
  have hu2 : 0 < u ^ 2 := by positivity
  set g : ℝ := Real.exp (-(u ^ 2 / 32)) with hg
  have hg0 : 0 < g := Real.exp_pos _
  have hsqpi : Real.sqrt Real.pi ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt Real.pi_lt_four.le
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hu4 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have hu7 : ∀ k ≤ 7, u ^ k ≤ u ^ 7 := fun k hk => pow_le_pow_right₀ hu hk
  -- term 1
  have e1 : Real.exp ((9 - (u ^ 4) ^ 2 / 4) / (u ^ 2) ^ 2) ≤ Real.exp 9 * g := by
    rw [hg, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h : (9 - (u ^ 4) ^ 2 / 4) / (u ^ 2) ^ 2 = 9 / u ^ 4 - u ^ 4 / 4 := by field_simp
    rw [h]
    have : 9 / u ^ 4 ≤ 9 := div_le_self (by norm_num) (one_le_pow₀ hu)
    nlinarith
  have n3 : (n : ℝ) ^ (3 : ℝ) ≤ u ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hn0.le hnu 3
  have t1 : 2 * (3 - σ) * (Real.exp ((9 - (u ^ 4) ^ 2 / 4) / (u ^ 2) ^ 2) * (n : ℝ) ^ (3 : ℝ) *
      ((3 + 2 * u ^ 4) * CF)) ≤ 30 * Real.exp 9 * CF * (u ^ 7 * g) := by
    have h34 : 3 + 2 * u ^ 4 ≤ 5 * u ^ 4 := by nlinarith [one_le_pow₀ (n := 4) hu]
    calc 2 * (3 - σ) * (Real.exp ((9 - (u ^ 4) ^ 2 / 4) / (u ^ 2) ^ 2) * (n : ℝ) ^ (3 : ℝ) *
          ((3 + 2 * u ^ 4) * CF))
        ≤ 6 * ((Real.exp 9 * g) * u ^ 3 * ((5 * u ^ 4) * CF)) := by
          apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
          apply mul_le_mul (mul_le_mul e1 n3 (by positivity) (by positivity))
            (mul_le_mul_of_nonneg_right h34 hCF) (by positivity) (by positivity)
      _ = 30 * Real.exp 9 * CF * (u ^ 3 * u ^ 4 * g) := by ring
      _ = 30 * Real.exp 9 * CF * (u ^ 7 * g) := by rw [← pow_add]
  -- term 2
  have e2 : Real.exp ((3 - σ) ^ 2 / (u ^ 2) ^ 2) ≤ Real.exp 9 := by
    apply Real.exp_le_exp.mpr
    have h1 : (3 - σ) ^ 2 ≤ 9 := by nlinarith
    have h2 : (1 : ℝ) ≤ (u ^ 2) ^ 2 := one_le_pow₀ (one_le_pow₀ hu)
    calc (3 - σ) ^ 2 / (u ^ 2) ^ 2 ≤ (3 - σ) ^ 2 := div_le_self (sq_nonneg _) h2
      _ ≤ 9 := h1
  have n3σ : (n : ℝ) ^ (3 - σ) ≤ u ^ 3 := by
    calc (n : ℝ) ^ (3 - σ) ≤ u ^ (3 - σ) := Real.rpow_le_rpow hn0.le hnu (by linarith)
      _ ≤ u ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (by linarith)
      _ = u ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e3 : Real.exp (-((u ^ 4) ^ 2 / (8 * (u ^ 2) ^ 2))) ≤ g := by
    rw [hg]
    apply Real.exp_le_exp.mpr
    have h : (u ^ 4) ^ 2 / (8 * (u ^ 2) ^ 2) = u ^ 4 / 8 := by field_simp
    rw [h]
    nlinarith
  have t2 : Real.exp ((3 - σ) ^ 2 / (u ^ 2) ^ 2) * (n : ℝ) ^ (3 - σ) * Z₂ *
      Real.exp (-((u ^ 4) ^ 2 / (8 * (u ^ 2) ^ 2))) * (Real.sqrt Real.pi * (Real.sqrt 2 * u ^ 2)) ≤
      4 * Real.exp 9 * Z₂ * (u ^ 7 * g) := by
    have hs : Real.sqrt Real.pi * (Real.sqrt 2 * u ^ 2) ≤ 4 * u ^ 2 := by
      have := mul_le_mul hsqpi (mul_le_mul_of_nonneg_right hsq2 hu2.le) (by positivity)
        (by norm_num)
      linarith
    calc Real.exp ((3 - σ) ^ 2 / (u ^ 2) ^ 2) * (n : ℝ) ^ (3 - σ) * Z₂ *
          Real.exp (-((u ^ 4) ^ 2 / (8 * (u ^ 2) ^ 2))) * (Real.sqrt Real.pi * (Real.sqrt 2 * u ^ 2))
        ≤ Real.exp 9 * u ^ 3 * Z₂ * g * (4 * u ^ 2) := by gcongr
      _ = 4 * Real.exp 9 * Z₂ * (u ^ 5 * g) := by ring
      _ ≤ 4 * Real.exp 9 * Z₂ * (u ^ 7 * g) := by gcongr; norm_num
  -- term 3
  have e4 : Real.exp (-((u ^ 2) ^ 2 / (32 * (N : ℝ) ^ 2))) ≤ g := by
    rw [hg]
    apply Real.exp_le_exp.mpr
    have hN2 : (N : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hN0.le hNu 2
    have : u ^ 2 / 32 ≤ (u ^ 2) ^ 2 / (32 * (N : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith
  have t3 : Real.sqrt Real.pi * u ^ 2 * (4 * (N : ℝ) ^ 2 *
      Real.exp (-((u ^ 2) ^ 2 / (32 * (N : ℝ) ^ 2)))) * Zσ ≤ 8 * Zσ * (u ^ 7 * g) := by
    have hN2 : (N : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hN0.le hNu 2
    calc Real.sqrt Real.pi * u ^ 2 * (4 * (N : ℝ) ^ 2 *
          Real.exp (-((u ^ 2) ^ 2 / (32 * (N : ℝ) ^ 2)))) * Zσ
        ≤ 2 * u ^ 2 * (4 * u ^ 2 * g) * Zσ := by gcongr
      _ = 8 * Zσ * (u ^ 4 * g) := by ring
      _ ≤ 8 * Zσ * (u ^ 7 * g) := by gcongr; norm_num
  calc _ ≤ 30 * Real.exp 9 * CF * (u ^ 7 * g) + 4 * Real.exp 9 * Z₂ * (u ^ 7 * g) +
        8 * Zσ * (u ^ 7 * g) := add_le_add (add_le_add t1 t2) t3
    _ = _ := by ring

/-- A pointwise logarithmic bound gives the windowed upper bound. -/
theorem windowed_integral_le_of_log_bound {F : ℂ → ℂ} {σ C t₀ T W : ℝ} (hW : 0 < W)
    (hT : 2 ≤ T) (ht₀ : t₀ ≤ T / 2)
    (hC : ∀ t : ℝ, t₀ ≤ t → ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log t)
    (hFc : ContinuousOn (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I)) (uIcc (T / 2) (3 * T / 2))) :
    ∫ t in (T / 2)..(3 * T / 2), Real.exp (-(t - T) ^ 2 / W ^ 2) *
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (max C 0 * Real.log (3 * T / 2)) ^ 2 * (Real.sqrt Real.pi * W) := by
  have hle : T / 2 ≤ 3 * T / 2 := by linarith
  have hpt : ∀ t ∈ Icc (T / 2) (3 * T / 2), Real.exp (-(t - T) ^ 2 / W ^ 2) *
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Real.exp (-(t - T) ^ 2 / W ^ 2) * (max C 0 * Real.log (3 * T / 2)) ^ 2 := by
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hlogt : Real.log t ≤ Real.log (3 * T / 2) := Real.log_le_log (by linarith) ht.2
    have h2 : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C 0 * Real.log (3 * T / 2) :=
      (hC t (le_trans ht₀ ht.1)).trans
        (mul_le_mul (le_max_left _ _) hlogt (Real.log_nonneg ht1) (le_max_right _ _))
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hKint : IntervalIntegrable (fun t => Real.exp (-(t - T) ^ 2 / W ^ 2) *
      (max C 0 * Real.log (3 * T / 2)) ^ 2) volume (T / 2) (3 * T / 2) :=
    ((Real.continuous_exp.comp (by fun_prop)).mul continuous_const).intervalIntegrable _ _
  have hFint : IntervalIntegrable (fun t => Real.exp (-(t - T) ^ 2 / W ^ 2) *
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume (T / 2) (3 * T / 2) :=
    ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
      ((continuous_norm.comp_continuousOn hFc).pow 2)).intervalIntegrable
  refine (intervalIntegral.integral_mono_on hle hFint hKint hpt).trans ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le hle]
  have hKle : ∫ t in Ioc (T / 2) (3 * T / 2), Real.exp (-(t - T) ^ 2 / W ^ 2) ≤
      Real.sqrt Real.pi * W := by
    rw [← integral_exp_gauss_shift T hW]
    exact setIntegral_le_integral (integrable_exp_gauss_shift T hW)
      (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
  have h0 : 0 ≤ (max C 0 * Real.log (3 * T / 2)) ^ 2 := sq_nonneg _
  calc (∫ t in Ioc (T / 2) (3 * T / 2), Real.exp (-(t - T) ^ 2 / W ^ 2)) *
        (max C 0 * Real.log (3 * T / 2)) ^ 2
      ≤ (Real.sqrt Real.pi * W) * (max C 0 * Real.log (3 * T / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right hKle h0
    _ = _ := by ring


/-- The head `Σ_{n ≤ N} |e(n)| n^{-σ}` is at most `N²`. -/
theorem sum_abs_head_le (he : ∀ n, |e n| ≤ Real.log n) (σ : ℝ) (hσ : 0 ≤ σ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |e n * (n : ℝ) ^ (-σ)| ≤ (N : ℝ) ^ 2 := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, |e n * (n : ℝ) ^ (-σ)| ≤ N := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    calc |e n| * (n : ℝ) ^ (-σ) ≤ (n : ℝ) * 1 :=
          mul_le_mul (abs_le_self_of_abs_le_log he n)
            (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
            (Real.rpow_nonneg (by linarith) _) (by linarith)
      _ ≤ N := by rw [mul_one]; exact hnN
  calc ∑ n ∈ Finset.Icc 1 N, |e n * (n : ℝ) ^ (-σ)|
      ≤ ∑ _n ∈ Finset.Icc 1 N, (N : ℝ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) * N := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = (N : ℝ) ^ 2 := by ring

/-- The off-diagonal Gaussian is negligible: `e^{-u⁴/(4N²)} (Σ b)² ≤ u⁴ e^{-u²/4}` for `N ≤ u`. -/
theorem gaussian_offdiag_head_le {u : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hNu : (N : ℝ) ≤ u) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : B ≤ (N : ℝ) ^ 2) :
    Real.exp (-((u ^ 2) ^ 2 / (4 * (N : ℝ) ^ 2))) * B ^ 2 ≤ u ^ 4 * Real.exp (-(u ^ 2 / 4)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN2 : (N : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hN0.le hNu 2
  have he : Real.exp (-((u ^ 2) ^ 2 / (4 * (N : ℝ) ^ 2))) ≤ Real.exp (-(u ^ 2 / 4)) := by
    apply Real.exp_le_exp.mpr
    have : u ^ 2 / 4 ≤ (u ^ 2) ^ 2 / (4 * (N : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
    linarith
  have hB2 : B ^ 2 ≤ u ^ 4 := by
    have := pow_le_pow_left₀ hB0 (hB.trans hN2) 2
    rw [← pow_mul] at this; exact this
  calc Real.exp (-((u ^ 2) ^ 2 / (4 * (N : ℝ) ^ 2))) * B ^ 2
      ≤ Real.exp (-(u ^ 2 / 4)) * u ^ 4 := mul_le_mul he hB2 (sq_nonneg _) (Real.exp_pos _).le
    _ = u ^ 4 * Real.exp (-(u ^ 2 / 4)) := by ring


/-- **The fixed-height core.**  At `T = u⁴`, `W = u²`, `N = ⌊u⌋`, a logarithmic bound for the
continued `L(e)` on `Re s = σ` caps the head mass by `(C log(3u⁴/2))² + 2`. -/
theorem head_mass_le_of_log_bound (he : ∀ n, |e n| ≤ Real.log n) {J : Finset ℂ} {c : ℂ → ℂ}
    {η σ CR C t₀ u B : ℝ}
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    (hCR : ∀ x : ℝ, 1 ≤ x → ‖remainder e J c x‖ ≤ CR * x ^ η) (hCR0 : 0 ≤ CR)
    (hJ : ∀ ρ ∈ J, ρ.re < 2 ∧ |ρ.im| ≤ B) (hησ : η < σ) (hσ0 : 0 < σ) (hσ3 : σ ≤ 3)
    (hC : ∀ t : ℝ, t₀ ≤ t → ‖pertLogDeriv e J c ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log t)
    (hu3 : 3 ≤ u) (hut : t₀ ≤ u ^ 4 / 2) (huB : B + 1 ≤ u ^ 4 / 2)
    (herr : (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
      4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ))) *
        (u ^ 7 * Real.exp (-(u ^ 2 / 32))) ≤ Real.sqrt Real.pi / 2)
    (hud : u ^ 4 * Real.exp (-(u ^ 2 / 4)) ≤ 1) :
    ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (e n * (n : ℝ) ^ (-σ)) ^ 2 ≤
      (max C 0 * Real.log (3 * u ^ 4 / 2)) ^ 2 + 2 := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hNu : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
  have hN1 : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu1)
  have hu81 : (81 : ℝ) ≤ u ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hu3 4
    norm_num at this; exact this
  have hW0 : 0 < u ^ 2 := by positivity
  have hT2 : 2 ≤ u ^ 4 := by linarith
  have hW24 : 24 ≤ (u ^ 2) ^ 2 := by rw [← pow_mul]; norm_num; linarith
  have hCF0 : 0 ≤ ∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η) :=
    add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (div_nonneg hCR0 (by linarith))
  have hZ₂0 : 0 ≤ ∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ) :=
    tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hZσ0 : 0 ≤ ∑' m : ℕ, (m : ℝ) ^ (-1 - σ) :=
    tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  set b : ℕ → ℝ := fun n => e n * (n : ℝ) ^ (-σ) with hb
  have hI : ∀ n ∈ Finset.Icc 1 ⌊u⌋₊,
      ‖(∫ t in (u ^ 4 / 2)..(3 * u ^ 4 / 2), deletionGaussWindow σ (u ^ 4) (u ^ 2)
          ((σ : ℂ) + (t : ℂ) * I) *
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * pertLogDeriv e J c ((σ : ℂ) + (t : ℂ) * I))) -
        ((Real.sqrt Real.pi * u ^ 2 : ℝ) : ℂ) * (b n : ℂ)‖ ≤
      (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
        4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ))) *
        (u ^ 7 * Real.exp (-(u ^ 2 / 32))) := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN := (Finset.mem_Icc.mp hn).2
    exact (norm_windowed_line_integral_sub_le e he (X := ⌊u⌋₊) hψ hCR hJ hησ hσ0 hσ3 hW0 hW24 hT2
      huB hn1 (by exact_mod_cast hnN)).trans
      (windowed_error_le hu1 hσ0 hσ3 hCF0 hZ₂0 hZσ0 hn1 hnN hNu)
  have hFc : ContinuousOn (fun t : ℝ => pertLogDeriv e J c ((σ : ℂ) + (t : ℂ) * I))
      (uIcc (u ^ 4 / 2) (3 * u ^ 4 / 2)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hre : η < ((σ : ℂ) + (t : ℂ) * I).re := by simp; exact hησ
    have hdiff : DifferentiableAt ℂ (pertLogDeriv e J c) ((σ : ℂ) + (t : ℂ) * I) := by
      refine differentiableAt_pertLogDeriv hψ hre fun ρ hρ hzρ => ?_
      have h := (hJ ρ hρ).2
      rw [← hzρ] at h
      simp at h
      linarith [ht.1, le_abs_self t]
    exact (ContinuousAt.comp (g := pertLogDeriv e J c)
      (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) hdiff.continuousAt
      (by fun_prop)).continuousWithinAt
  have hlow := windowed_meanSquare_ge hW0 (by linarith) hFc b ⌊u⌋₊ hI
  have hup := windowed_integral_le_of_log_bound (F := pertLogDeriv e J c) hW0 hT2 hut hC hFc
  have hsumb := sum_abs_head_le he σ hσ0.le ⌊u⌋₊
  have hsumb0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, |b n| := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hoff := gaussian_offdiag_head_le hN1 hNu hsumb0 hsumb
  have hpiW : 0 < Real.sqrt Real.pi * u ^ 2 := by positivity
  have hsumu : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, |b n| ≤ u ^ 2 :=
    hsumb.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hNu 2)
  set ε : ℝ := (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
    4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ))) *
      (u ^ 7 * Real.exp (-(u ^ 2 / 32))) with hε
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hI 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩))
  have hlin : 2 * ε * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, |b n| ≤ Real.sqrt Real.pi * u ^ 2 := by
    calc 2 * ε * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, |b n| ≤ 2 * (Real.sqrt Real.pi / 2) * u ^ 2 :=
          mul_le_mul (by linarith) hsumu hsumb0 (by positivity)
      _ = Real.sqrt Real.pi * u ^ 2 := by ring
  set S : ℝ := ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, b n ^ 2 with hS
  set P : ℝ := (max C 0 * Real.log (3 * u ^ 4 / 2)) ^ 2 with hP
  have hoff' : Real.exp (-((u ^ 2) ^ 2 / (4 * (⌊u⌋₊ : ℝ) ^ 2))) *
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, |b n|) ^ 2 ≤ 1 := hoff.trans hud
  have key : Real.sqrt Real.pi * u ^ 2 * S ≤ Real.sqrt Real.pi * u ^ 2 * (P + 2) := by
    have h1 := hlow.trans hup
    have h2 : Real.sqrt Real.pi * u ^ 2 * (Real.exp (-((u ^ 2) ^ 2 / (4 * (⌊u⌋₊ : ℝ) ^ 2))) *
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, |b n|) ^ 2) ≤ Real.sqrt Real.pi * u ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hoff' hpiW.le
    have h3 : P * (Real.sqrt Real.pi * u ^ 2) = Real.sqrt Real.pi * u ^ 2 * P := by ring
    linarith
  exact le_of_mul_le_mul_left key hpiW


/-- **Discrete multiplicative uncertainty for integer-supported perturbations.**  Let a Beurling
system of positive integers have masses `a` (`|a n| ≤ 1`, `a 1 = 1`) and generator von Mangoldt
function `Λ - e` (`(Λ - e) ⋆ a = a · log`, `|e n| ≤ log n`), where every nonzero `e n` has size at
least `log 2`.  If `Σ_{n ≤ x} e n = Σ_{ρ∈J} c_ρ x^ρ + O(x^η)` over finitely many complex exponents
with `Re ρ < κ ≤ 1` for `ρ ≠ κ`, `Re c_κ ≠ 0` and `0 ≤ η < κ/2`, then
`Σ_{n ≤ x} a n - A x ≠ O(x^θ)` for every `θ < κ/2`.  Deleting primes and adding integer generators
are both allowed, and the leading term may have either sign. -/
theorem not_isBigO_count_of_leading_chebyshev (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((ArithmeticFunction.vonMangoldt n - e n : ℝ) : ℂ))
      (countSeq a) = LSeries.logMul (countSeq a))
    (hint : ∀ n, e n = 0 ∨ Real.log 2 ≤ |e n|) {A θ η κ : ℝ} {J : Finset ℂ} {c : ℂ → ℂ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθκ : θ < κ / 2) (hηκ : η < κ / 2) (hκ1 : κ ≤ 1)
    (hκJ : (κ : ℂ) ∈ J) (hcκ : (c κ).re ≠ 0) (hJκ : ∀ ρ ∈ J, ρ ≠ κ → ρ.re < κ)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η) :
    ¬(fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ := by
  classical
  intro hN
  set B : ℝ := ∑ ρ ∈ J, |ρ.im| with hB
  have hJ' : ∀ ρ ∈ J, ρ.re < 2 ∧ |ρ.im| ≤ B := by
    intro ρ hρ
    refine ⟨?_, Finset.single_le_sum (f := fun ρ : ℂ => |ρ.im|) (fun _ _ => abs_nonneg _) hρ⟩
    rcases eq_or_ne ρ κ with h | h
    · rw [h, Complex.ofReal_re]; linarith
    · linarith [hJκ ρ hρ h]
  -- the line `Re s = σ`
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = (max θ η + κ / 2) / 2 := ⟨_, rfl⟩
  have hmax : max θ η < κ / 2 := max_lt hθκ hηκ
  have hσθ : θ < σ := by rw [hσdef]; linarith [le_max_left θ η]
  have hση : η < σ := by rw [hσdef]; linarith [le_max_right θ η]
  have hσκ : σ < κ / 2 := by rw [hσdef]; linarith
  have hσ0 : 0 < σ := by linarith
  obtain ⟨C, t₀, hC⟩ := exists_norm_pertLogDeriv_le_log ha ha1 he hconv hθ hN hψ hJ' hσθ hση
    (by linarith)
  obtain ⟨CR, hCR0, hCR⟩ := exists_forall_norm_remainder_le e he hη hψ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.log 2 * (|(c κ).re| / 2) := ⟨_, rfl⟩
  have hM0 : 0 < M := by
    rw [hM]; exact mul_pos (Real.log_pos (by norm_num)) (by positivity)
  have hδ0 : 0 < κ - 2 * σ := by linarith
  -- eventual conditions in the parameter `u`
  have hmass : ∀ᶠ u : ℝ in atTop, M * (⌊u⌋₊ : ℝ) ^ (κ - 2 * σ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (e n * (n : ℝ) ^ (-σ)) ^ 2 := by
    rw [hM]
    exact tendsto_nat_floor_atTop.eventually
      (eventually_head_mass_ge hint hσ0.le (by linarith) hκJ hcκ hJκ hψ)
  have herr : ∀ᶠ u : ℝ in atTop, (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
      4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ))) *
        (u ^ 7 * Real.exp (-(u ^ 2 / 32))) ≤ Real.sqrt Real.pi / 2 := by
    have h := (tendsto_pow_mul_exp_neg_sq_div (k := 7) (c := 32) (by norm_num)).const_mul
      (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
        4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ)))
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by positivity))
  have hdiag : ∀ᶠ u : ℝ in atTop, u ^ 4 * Real.exp (-(u ^ 2 / 4)) ≤ 1 :=
    (tendsto_pow_mul_exp_neg_sq_div (k := 4) (c := 4) (by norm_num)).eventually
      (ge_mem_nhds (by norm_num))
  have hlog := eventually_sq_log_add_lt (K := max C 0) hM0 hδ0
  have hu4 : Tendsto (fun u : ℝ => u ^ 4 / 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
  obtain ⟨u, hum, hue, hud, hul, hut, huB, hu3⟩ :=
    (hmass.and (herr.and (hdiag.and (hlog.and ((hu4.eventually_ge_atTop t₀).and
      ((hu4.eventually_ge_atTop (B + 1)).and (eventually_ge_atTop (3 : ℝ)))))))).exists
  have hcap := head_mass_le_of_log_bound he hψ hCR hCR0 hJ' hση hσ0 (by linarith) hC hu3 hut huB
    hue hud
  linarith

end IntegerBeurling

namespace PrimeDeletion

variable (Q : Set ℕ)

theorem deletedVonMangoldt_eq_zero_or_log_two_le (n : ℕ) :
    deletedVonMangoldt Q n = 0 ∨ Real.log 2 ≤ deletedVonMangoldt Q n := by
  unfold deletedVonMangoldt qFreeIndicator
  split_ifs with h
  · left; ring
  · rw [sub_zero, mul_one]
    rcases eq_or_ne (ArithmeticFunction.vonMangoldt n) 0 with h0 | h0
    · left; exact h0
    · right
      have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
      rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
      apply Real.log_le_log (by norm_num)
      have hn1 : n ≠ 1 := hpp.ne_one
      exact_mod_cast (Nat.minFac_prime hn1).two_le


theorem abs_deletedVonMangoldt_le_log (n : ℕ) : |deletedVonMangoldt Q n| ≤ Real.log n := by
  rw [abs_of_nonneg (deletedVonMangoldt_nonneg Q n)]
  have h1 : deletedVonMangoldt Q n ≤ ArithmeticFunction.vonMangoldt n := by
    have := qFreeIndicator_nonneg Q n
    unfold deletedVonMangoldt
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
  exact h1.trans ArithmeticFunction.vonMangoldt_le_log

theorem abs_qFreeIndicator_le_one (n : ℕ) : |qFreeIndicator Q n| ≤ 1 := by
  rw [abs_of_nonneg (qFreeIndicator_nonneg Q n)]
  exact qFreeIndicator_le_one Q n

/-- The deletion as an integer-supported Beurling perturbation: `(Λ - Λ_Q) ⋆ 1_S = log · 1_S`. -/
theorem convolution_sub_deletedVonMangoldt :
    LSeries.convolution (fun n => ((ArithmeticFunction.vonMangoldt n - deletedVonMangoldt Q n : ℝ) : ℂ))
      (IntegerBeurling.countSeq (qFreeIndicator Q)) =
      LSeries.logMul (IntegerBeurling.countSeq (qFreeIndicator Q)) := by
  have h : (fun n => ((ArithmeticFunction.vonMangoldt n - deletedVonMangoldt Q n : ℝ) : ℂ)) =
      fun n => qFreeSeq Q n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
    funext n
    simp only [deletedVonMangoldt, qFreeSeq]
    push_cast
    ring
  rw [h]
  exact convolution_twist_vonMangoldt Q

/-- **Discrete multiplicative uncertainty on regular prime deletions.**  Let the deleted Chebyshev
function be `Σ_{ρ∈J} c_ρ x^ρ + O(x^η)` over finitely many complex exponents with `Re ρ < κ ≤ 1` for
`ρ ≠ κ`, leading coefficient `Re c_κ > 0` and `0 ≤ η < κ/2`.  Then the integers free of the deleted
primes admit no power saving below `x^{κ/2}`: `#S ∩ [1,x] - a x ≠ O(x^θ)` for every `θ < κ/2`.
Every secondary term is allowed, whatever its multiplicity: in particular, a deletion imitating
off-line zeros never beats half its leading dimension. -/
theorem not_isBigO_qFreeCount_of_leading_chebyshev_complex {a θ η κ : ℝ} {J : Finset ℂ}
    {c : ℂ → ℂ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθκ : θ < κ / 2) (hηκ : η < κ / 2) (hκ1 : κ ≤ 1)
    (hκJ : (κ : ℂ) ∈ J) (hcκ : 0 < (c κ).re) (hJκ : ∀ ρ ∈ J, ρ ≠ κ → ρ.re < κ)
    (hψ : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η) :
    ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ :=
  IntegerBeurling.not_isBigO_count_of_leading_chebyshev (abs_qFreeIndicator_le_one Q)
    (qFreeIndicator_one Q) (abs_deletedVonMangoldt_le_log Q) (convolution_sub_deletedVonMangoldt Q)
    (fun n => (deletedVonMangoldt_eq_zero_or_log_two_le Q n).imp id fun h => h.trans (le_abs_self _))
    hθ hη hθκ hηκ hκ1 hκJ hcκ.ne' hJκ hψ

/-- **Discrete multiplicative uncertainty on regular prime deletions, real exponents.**  If the
deleted Chebyshev function is `Σ_{ρ∈J} c_ρ x^ρ + O(x^η)` over finitely many real exponents
`ρ ≤ κ ≤ 1`, with leading coefficient `c_κ > 0` and `0 ≤ η < κ/2`, then
`#S ∩ [1,x] - a x ≠ O(x^θ)` for every `θ < κ/2`, whatever the multiplicity `λ = κ c_κ`. -/
theorem not_isBigO_qFreeCount_of_leading_chebyshev {a θ η κ : ℝ} {J : Finset ℝ} {c : ℝ → ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθκ : θ < κ / 2) (hηκ : η < κ / 2) (hκ1 : κ ≤ 1)
    (hκJ : κ ∈ J) (hcκ : 0 < c κ) (hJκ : ∀ ρ ∈ J, ρ ≠ κ → ρ < κ)
    (hψ : (fun x : ℝ => deletedChebyshev Q x - ∑ ρ ∈ J, c ρ * x ^ ρ) =O[atTop]
      fun x => x ^ η) :
    ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  classical
  have hinj : Set.InjOn (fun ρ : ℝ => (ρ : ℂ)) (J : Set ℝ) :=
    fun _ _ _ _ h => Complex.ofReal_injective h
  set J' : Finset ℂ := J.image fun ρ : ℝ => (ρ : ℂ) with hJ'def
  set c' : ℂ → ℂ := fun z => (c z.re : ℂ) with hc'
  have hψ' : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J', c' ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η := by
    refine IsBigO.of_norm_left ?_
    refine hψ.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [hJ'def, Finset.sum_image hinj, ← Complex.norm_real]
    congr 1
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hc', Complex.ofReal_re]
    rw [Complex.ofReal_cpow hx]
  refine not_isBigO_qFreeCount_of_leading_chebyshev_complex Q hθ hη hθκ hηκ hκ1
    (Finset.mem_image_of_mem _ hκJ) (by simpa [hc'] using hcκ) ?_ hψ'
  intro ρ hρ hρκ
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hρ
  have hrκ : r ≠ κ := fun h => hρκ (by rw [h])
  simpa using hJκ r hr hrκ

/-- **Every multiplicity obeys the half-dimension floor.**  If the deleted Chebyshev function is
`(λ/κ)(x^κ + x^{κ/2}) + O(x^η)` with `λ > 0`, `0 ≤ η < κ/2` and `0 < κ ≤ 1`, the `Q`-free integers
admit no power saving below `x^{κ/2}`.  For odd `λ` this is `not_isBigO_qFreeCount_of_odd`; the
even case, where no branch point at `κ/2` exists, is new. -/
theorem not_isBigO_qFreeCount_of_multiplicity {a θ η κ l : ℝ} (hl : 0 < l) (hθ : 0 ≤ θ)
    (hθκ : θ < κ / 2) (hη : 0 ≤ η) (hηκ : η < κ / 2) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hψ : (fun x : ℝ => deletedChebyshev Q x - l / κ * (x ^ κ + x ^ (κ / 2))) =O[atTop]
      fun x => x ^ η) :
    ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  have hne : κ ≠ κ / 2 := by intro h; linarith
  refine not_isBigO_qFreeCount_of_leading_chebyshev Q (J := {κ, κ / 2}) (c := fun _ => l / κ)
    hθ hη hθκ hηκ hκ1 (Finset.mem_insert_self _ _) (div_pos hl hκ0) ?_ ?_
  · intro ρ hρ hρκ
    rcases Finset.mem_insert.mp hρ with h | h
    · exact absurd h hρκ
    · rw [Finset.mem_singleton.mp h]; linarith
  · refine hψ.congr_left fun x => ?_
    rw [Finset.sum_pair hne]
    ring

end PrimeDeletion

