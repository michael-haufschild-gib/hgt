import GaloisForLFunctions.RHTower.PrimeShortIntervalsHuxleyAsymptotic
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThirteenths

/-!
# Primes in short intervals of length `x^{17/30 + ε}`

Guth–Maynard, Corollary 1.3, in the form `ψ(x + x^α) - ψ(x) ∼ x^α` for `17/30 < α < 1`.

Under the large values estimate `GuthMaynardLargeValuesBound` the density exponent `30/13 + ε`
(`exists_zeroHeightBox_ncard_le_thirty_thirteenths`) makes the weighted zero sum
`Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|))` vanish for every `u < 13/30`
(`tendsto_tsum_zeroShortWeight_of_density`, with `ε = min(1, (1/u - 30/13)/2)`, so that
`u(30/13 + ε) ≤ (1 + 30u/13)/2 < 1`).  With `u = 1 - α`:

* `(ψ(x + x^α) - ψ(x))/x^α → 1` (`tendsto_psi_short_window_div_seventeen_thirtieths`), from the
  two explicit-formula window bounds; the step from vanishing to the asymptotic holds for every
  `0 < α < 1` (`tendsto_psi_short_window_div_of_tendsto`);
* `θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2` for `y ≥ X`, `L ≥ 0`, and a prime in `(x, x + x^α]` for all
  large `x` (`eventually_exists_prime_short_interval_seventeen_thirtieths`).
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Filter Topology RHTower.Sieve RHTower.GuthMaynard

/-- **The weighted zero sum vanishes below the exponent `13/30`.** -/
theorem tendsto_tsum_zeroShortWeight_seventeen_thirtieths (hGM : GuthMaynardLargeValuesBound)
    {u c : ℝ} (hu : 0 < u) (hu' : u < 13 / 30) (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min 1 ((1 / u - 30 / 13) / 2) := ⟨_, rfl⟩
  have hgap : 0 < 1 / u - 30 / 13 := by
    rw [sub_pos, lt_div_iff₀ hu]
    linarith
  have hε0 : 0 < ε := hεdef ▸ lt_min one_pos (by linarith)
  have hε1 : ε ≤ 1 := hεdef ▸ min_le_left _ _
  have hεle : ε ≤ (1 / u - 30 / 13) / 2 := hεdef ▸ min_le_right _ _
  obtain ⟨D, hD, B, T₀, -, hdens⟩ := exists_zeroHeightBox_ncard_le_thirty_thirteenths hGM hε0 hε1
  have huA : u * (30 / 13 + ε) < 1 := by
    have h1 : u * (30 / 13 + ε) ≤ u * (30 / 13 + (1 / u - 30 / 13) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hu.le
    have h2 : u * (30 / 13 + (1 / u - 30 / 13) / 2) = (1 + 30 * u / 13) / 2 := by
      field_simp
      ring
    linarith
  exact tendsto_tsum_zeroShortWeight_of_density (by positivity) (by linarith) hu (by linarith)
    huA hc hD hdens

/-- **From a vanishing zero sum to the prime number theorem in short windows.**  If for
`u = 1 - α` and every `c ≥ 1` the weighted zero sum at `c x^{2u}` tends to `0`, then
`(ψ(x + x^α) - ψ(x))/x^α → 1`.  With `h = x^α`, `h' = h/M` the two window bounds read
`h(1 - 2/M) - 4/(x h') - 2hΣ ≤ ψ(x + h) - ψ(x) ≤ h(1 + 2/M) + 4/(x h') + 8hΣ'`. -/
theorem tendsto_psi_short_window_div_of_tendsto {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hzero : ∀ c : ℝ, 1 ≤ c → Tendsto (fun x : ℝ =>
      ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * (1 - α))) (q.1 : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => (Chebyshev.psi (x + x ^ α) - Chebyshev.psi x) / x ^ α) atTop (𝓝 1) := by
  have hsmall4 : Tendsto (fun x : ℝ => x ^ (-(1 + 2 * α))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  -- the size facts at height `x`
  have hfacts : ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ x ^ α ≤ x / 2 := by
    have h := (tendsto_rpow_atTop (show 0 < 1 - α by linarith)).eventually_ge_atTop 2
    filter_upwards [h, eventually_ge_atTop (4 : ℝ)] with x hx hx4
    refine ⟨hx4, ?_⟩
    have hx0 : 0 < x := by linarith
    have hsplit : x = x ^ α * x ^ (1 - α) := by
      rw [← Real.rpow_add hx0]; simp
    have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    nlinarith
  -- `4/(x (h/M))/h = 4M x^{-(1+2α)}`
  have hterm : ∀ {x M : ℝ}, 0 < x → 0 < M →
      4 / (x * (x ^ α / M)) / x ^ α = 4 * M * x ^ (-(1 + 2 * α)) := by
    intro x M hx0 hM0
    rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le]
    rw [show (x ^ (2 : ℝ)) ^ α = x ^ α * x ^ α by
      rw [← Real.rpow_mul hx0.le, mul_comm, Real.rpow_mul hx0.le, Real.rpow_two]; ring]
    field_simp
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 6 / (1 - a) < M ∧ 4 ≤ M := by
      obtain ⟨M, hM⟩ := exists_nat_gt (max (6 / (1 - a)) 4)
      exact ⟨M, lt_of_le_of_lt (le_max_left _ _) hM,
        by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hM).le⟩
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM.2
    have hM0 : (0 : ℝ) < M := by linarith
    have hMa : 2 / (M : ℝ) < (1 - a) / 3 := by
      rw [div_lt_iff₀ hM0]
      have := hM.1
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    have hz := (hzero (8 * M) (by linarith)).eventually
      (gt_mem_nhds (show (0 : ℝ) < (1 - a) / 6 by linarith))
    have h4t : Tendsto (fun x : ℝ => 4 * (M : ℝ) * x ^ (-(1 + 2 * α))) atTop (𝓝 0) := by
      simpa using hsmall4.const_mul (4 * (M : ℝ))
    have h4 := h4t.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - a) / 6 by linarith))
    filter_upwards [hfacts, hz, h4] with x ⟨hx4, hxα⟩ hzx h4x
    have hx0 : 0 < x := by linarith
    have hh0 : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    have hh' : 0 < x ^ α / M := div_pos hh0 hM0
    have hmain := psi_window_ge_sub_zeroShortWeight (x := x) (h := x ^ α) (h' := x ^ α / M)
      (by linarith) hh' (by rw [mul_div_assoc']; rw [div_le_iff₀ hM0]; nlinarith) (by linarith)
    rw [sq_div_rpow_mul_rpow_div_eq hx0 hM0] at hmain
    have h4' : 4 / (x * (x ^ α / M)) < (1 - a) / 6 * x ^ α := by
      rw [← div_lt_iff₀ hh0, hterm hx0 hM0]
      exact h4x
    obtain ⟨h, hh⟩ : ∃ h : ℝ, h = x ^ α := ⟨_, rfl⟩
    rw [← hh] at hmain hh0 hh' h4' ⊢
    rw [lt_div_iff₀ hh0]
    have hzx' : 2 * h * ∑' q : XiZeroCopy, zeroShortWeight x (8 * M * x ^ (2 * (1 - α))) (q.1 : ℂ)
        ≤ 2 * h * ((1 - a) / 6) := mul_le_mul_of_nonneg_left hzx.le (by positivity)
    have h2M : 2 * (h / M) = 2 / M * h := by ring
    have h2Mle : 2 / (M : ℝ) * h ≤ (1 - a) / 3 * h := mul_le_mul_of_nonneg_right hMa.le hh0.le
    nlinarith
  · intro b hb
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 6 / (b - 1) < M ∧ 4 ≤ M := by
      obtain ⟨M, hM⟩ := exists_nat_gt (max (6 / (b - 1)) 4)
      exact ⟨M, lt_of_le_of_lt (le_max_left _ _) hM,
        by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hM).le⟩
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM.2
    have hM0 : (0 : ℝ) < M := by linarith
    have hMb : 2 / (M : ℝ) < (b - 1) / 3 := by
      rw [div_lt_iff₀ hM0]
      have := hM.1
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    have hz := (hzero (4 * M) (by linarith)).eventually
      (gt_mem_nhds (show (0 : ℝ) < (b - 1) / 24 by linarith))
    have h4t : Tendsto (fun x : ℝ => 4 * (M : ℝ) * x ^ (-(1 + 2 * α))) atTop (𝓝 0) := by
      simpa using hsmall4.const_mul (4 * (M : ℝ))
    have h4 := h4t.eventually (gt_mem_nhds (show (0 : ℝ) < (b - 1) / 6 by linarith))
    filter_upwards [hfacts, hz, h4] with x ⟨hx4, hxα⟩ hzx h4x
    have hx0 : 0 < x := by linarith
    have hh0 : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    have hh' : 0 < x ^ α / M := div_pos hh0 hM0
    have hmain := psi_window_le_add_zeroShortWeight (x := x) (h := x ^ α) (h' := x ^ α / M) hx4
      hh' (by rw [mul_div_assoc']; rw [div_le_iff₀ hM0]; nlinarith) hxα
    rw [sq_div_rpow_mul_rpow_div_eq hx0 hM0] at hmain
    have h4' : 4 / (x * (x ^ α / M)) < (b - 1) / 6 * x ^ α := by
      rw [← div_lt_iff₀ hh0, hterm hx0 hM0]
      exact h4x
    obtain ⟨h, hh⟩ : ∃ h : ℝ, h = x ^ α := ⟨_, rfl⟩
    rw [← hh] at hmain hh0 hh' h4' ⊢
    rw [div_lt_iff₀ hh0]
    have hzx' : 8 * h * ∑' q : XiZeroCopy, zeroShortWeight x (4 * M * x ^ (2 * (1 - α))) (q.1 : ℂ)
        ≤ 8 * h * ((b - 1) / 24) := mul_le_mul_of_nonneg_left hzx.le (by positivity)
    have h2Mle : 2 / (M : ℝ) * h ≤ (b - 1) / 3 * h := mul_le_mul_of_nonneg_right hMb.le hh0.le
    have h2M : 2 * (h / M) = 2 / M * h := by ring
    nlinarith

/-- **The prime number theorem in short intervals, exponent `17/30`.**  Under the large values
estimate, for every `17/30 < α < 1`, `(ψ(x + x^α) - ψ(x))/x^α → 1`. -/
theorem tendsto_psi_short_window_div_seventeen_thirtieths (hGM : GuthMaynardLargeValuesBound)
    {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) :
    Tendsto (fun x : ℝ => (Chebyshev.psi (x + x ^ α) - Chebyshev.psi x) / x ^ α) atTop (𝓝 1) :=
  tendsto_psi_short_window_div_of_tendsto (by linarith) hα1 fun c hc =>
    tendsto_tsum_zeroShortWeight_seventeen_thirtieths hGM (by linarith) (by linarith) hc

/-- **Prime mass in every short window, exponent `17/30`.**  Under the large values estimate,
for every `17/30 < α < 1` there is `X ≥ 1` with `θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2` for all
`y ≥ X` and `L ≥ 0`. -/
theorem exists_theta_window_lower_seventeen_thirtieths (hGM : GuthMaynardLargeValuesBound)
    {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
  have hzero := tendsto_tsum_zeroShortWeight_seventeen_thirtieths hGM (u := 1 - α) (c := 512)
    (by linarith) (by linarith) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    (eventually_theta_short_window_of_tendsto (by linarith) hα1 hzero)
  refine ⟨max X₀ 1, le_max_right _ _, ?_⟩
  exact theta_window_lower_of_step (by linarith) (by norm_num) (le_max_right _ _)
    (fun z hz => hX₀ z (le_trans (le_max_left _ _) hz))

/-- **A prime in every short interval from a θ-window bound.**  If `0 ≤ α' < α < 1` and
`θ(y + L) - θ(y) ≥ (L - (y + L)^{α'})/2` for `y ≥ X ≥ 1`, `L ≥ 0`, then every large `x` has a
prime in `(x, x + x^α]`: at `L = x^α` the window carries `≥ (x^α - 2x^{α'})/2 > 0`. -/
theorem eventually_exists_prime_short_interval_of_theta_window {α α' X : ℝ} (hα'0 : 0 ≤ α')
    (hα' : α' < α) (hα1 : α < 1) (hX1 : 1 ≤ X)
    (hX : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α') / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ α := by
  have hgap : ∀ᶠ x : ℝ in atTop, 2 * x ^ α' < x ^ α := by
    filter_upwards [(tendsto_rpow_atTop (show 0 < α - α' by linarith)).eventually_gt_atTop 2,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hsplit : x ^ α = x ^ α' * x ^ (α - α') := by rw [← Real.rpow_add hx0]; ring_nf
    rw [hsplit]
    have hpos : 0 < x ^ α' := Real.rpow_pos_of_pos hx0 _
    nlinarith
  filter_upwards [hgap, eventually_ge_atTop X] with x hgx hxX
  have hx1 : 1 ≤ x := le_trans hX1 hxX
  have hx0 : 0 < x := by linarith
  have hxa0 : 0 ≤ x ^ α := Real.rpow_nonneg hx0.le _
  have hle : x ^ α ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rwa [Real.rpow_one] at this
  have hθ := hX x (x ^ α) hxX hxa0
  have h2 : (2 : ℝ) ^ α' ≤ 2 := by
    calc (2 : ℝ) ^ α' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hpow : (x + x ^ α) ^ α' ≤ 2 * x ^ α' := by
    calc (x + x ^ α) ^ α' ≤ (2 * x) ^ α' :=
          Real.rpow_le_rpow (by positivity) (by linarith) hα'0
      _ = 2 ^ α' * x ^ α' := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ α' := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
  have hpos : 0 < Chebyshev.theta (x + x ^ α) - Chebyshev.theta x := by linarith
  rw [Sieve.theta_sub_eq_sum_Ioc (by linarith)] at hpos
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
    linarith [Nat.lt_floor_add_one x]
  · have h1 : (p : ℝ) ≤ (⌊x + x ^ α⌋₊ : ℝ) := by exact_mod_cast hp.1.2
    linarith [Nat.floor_le (show 0 ≤ x + x ^ α by linarith)]

/-- **Primes in short intervals, exponent `17/30`.**  Under the large values estimate, for every
`17/30 < α < 1` every large `x` has a prime in `(x, x + x^α]`. -/
theorem eventually_exists_prime_short_interval_seventeen_thirtieths
    (hGM : GuthMaynardLargeValuesBound) {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ α := by
  obtain ⟨X, hX1, hX⟩ := exists_theta_window_lower_seventeen_thirtieths hGM
    (α := (17 / 30 + α) / 2) (by linarith) (by linarith)
  exact eventually_exists_prime_short_interval_of_theta_window (by linarith) (by linarith) hα1
    hX1 hX

end RHTower

end
