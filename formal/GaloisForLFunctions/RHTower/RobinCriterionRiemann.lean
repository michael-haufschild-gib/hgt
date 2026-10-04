import GaloisForLFunctions.RHTower.RobinExtremalThresholds
import GaloisForLFunctions.RHTower.RobinLcmRiemannCriterion

/-!
# Robin's criterion

The Riemann hypothesis holds if and only if `σ(n) < e^γ n log log n` for all large `n`.

*Converse.*  The inequality for all large `n` contains Robin's inequality at `lcm(1, …, n)`.

*Forward.*  Fix `n`, put `ℓ = log n` and `ε = 1/(ℓ log ℓ)`, and choose `x` with
`ε = ε(x) = log(1 + 1/x)/log x`.  The extremal number `N = N_x = ∏_{p ≤ x} p^{a_p(ε)}` maximizes
`σ(m)/m^{1+ε}`, so `log(σ(n)/n) ≤ log(σ(N)/N) + ε(ℓ - log N)`.  By concavity of `log log`,
`log log log N + ε(ℓ - log N) ≤ log log ℓ` for this choice of `ε`, so Robin's inequality at `N`
implies it at `n`.  At `N_x` the Robin defect splits as
`Δ + G(log x) - E_N + (ψ(x) - log N)/(x log x) + O((log N - x)²/(x² log x))`, with `a_p ≥ 2` for
`p ≤ (5/4)√x` (so `log N ≥ θ(x) + θ((5/4)√x)`) and `a_p = 1` for `(3/2)√x < p ≤ x` (so
`E_N ≥ Σ_{(3/2)√x<p≤x} p^{-2} ~ (4/3)/(√x log x)`).  Under RH, `Δ √x log x → 1`,
`G(log x)√x log x - Φ(log x) → 0`, `(ψ - θ)/√x → 1` and `|Φ| ≤ a₁`, so the scaled defect is at most
`a₁ + 1 + 1 - 5/4 - 4/3 + o(1) < 0`.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (sigma)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The extremal numbers at `ε(x)` -/

/-- `log(σ(N)/N) = -log ∏_{p ≤ B}(1 - 1/p) - Σ_{p ≤ B} -log(1 - p^{-(a_p+1)})`. -/
theorem log_sigma_div_robinExtremal_eq (ε : ℝ) (B : ℕ) :
    Real.log ((sigma 1 (robinExtremal ε B) : ℝ) / (robinExtremal ε B : ℝ))
      = -Real.log (mertensPrimeProduct B)
        - ∑ p ∈ (Finset.Icc 0 B).filter Nat.Prime,
            -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent ε p + 1)) := by
  rw [sigma_div_robinExtremal, Real.log_prod (fun p hp =>
    (robinLocal_pos (Finset.mem_filter.mp hp).2 _).ne'), neg_log_mertensPrimeProduct_eq,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hq : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  have hnum : 0 < 1 - (1 / (p : ℝ)) ^ (robinExponent ε p + 1) := by
    have h1 : (1 / (p : ℝ)) ^ (robinExponent ε p + 1) < 1 :=
      pow_lt_one₀ (by positivity) (by rw [div_lt_one (by linarith)]; exact hp1)
        (Nat.succ_ne_zero _)
    linarith
  rw [robinLocal, Real.log_div hnum.ne' hq.ne']
  ring

/-- The extremal number at `ε(x)`, `N_x = ∏_{p ≤ x} p^{a_p(ε(x))}`. -/
def robinExtremalAt (x : ℝ) : ℕ := robinExtremal (robinParameter x) ⌊x⌋₊

theorem robinExponent_eq_zero_of_floor_lt {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (hpx : ⌊x⌋₊ < p) : robinExponent (robinParameter x) p = 0 :=
  robinExponent_eq_zero_of_lt hx hp ((Nat.floor_lt (by linarith)).mp hpx)

/-- The primes below `y ≤ x` among the primes below `x`. -/
theorem sum_filter_le_log_eq_theta {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => (p : ℝ) ≤ y), Real.log p
      = Chebyshev.theta y := by
  rw [Chebyshev.theta_eq_sum_Icc]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
  constructor
  · rintro ⟨⟨_, hp⟩, hpy⟩
    exact ⟨Nat.le_floor hpy, hp⟩
  · rintro ⟨hpy, hp⟩
    have h1 : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).mp hpy
    exact ⟨⟨Nat.le_floor (h1.trans hyx), hp⟩, h1⟩

/-- **The size of `N_x` from below.**  If `a_p ≥ 2` for all primes `p ≤ (5/4)√x ≤ x`, then
`log N_x ≥ θ(x) + θ((5/4)√x)`. -/
theorem log_robinExtremalAt_ge {x : ℝ} (hx : 1 < x) (hyx : 5 / 4 * Real.sqrt x ≤ x)
    (h2 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 5 / 4 * Real.sqrt x →
      2 ≤ robinExponent (robinParameter x) p) :
    Chebyshev.theta x + Chebyshev.theta (5 / 4 * Real.sqrt x)
      ≤ Real.log (robinExtremalAt x : ℝ) := by
  have hθx : Chebyshev.theta x
      = ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p := Chebyshev.theta_eq_sum_Icc x
  have hθy := (sum_filter_le_log_eq_theta (by positivity : (0 : ℝ) ≤ 5 / 4 * Real.sqrt x) hyx).symm
  rw [Finset.sum_filter] at hθy
  rw [robinExtremalAt, log_robinExtremal, hθx, hθy, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := (Finset.mem_filter.mp hp).2
  have hpx : (p : ℝ) ≤ x := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact (Nat.le_floor_iff (by linarith)).mp this
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : (1 : ℝ) ≤ robinExponent (robinParameter x) p := by
    exact_mod_cast (one_le_robinExponent_iff_le hx hpp).mpr hpx
  split_ifs with h
  · have h2' : (2 : ℝ) ≤ robinExponent (robinParameter x) p := by exact_mod_cast h2 p hpp h
    nlinarith
  · nlinarith

/-- **The size of `N_x` from above.**  For `x ≥ 100`, `log N_x - θ(x) ≤ 4√x log x`. -/
theorem log_robinExtremalAt_sub_theta_le {x : ℝ} (hx : 100 ≤ x) :
    Real.log (robinExtremalAt x : ℝ) - Chebyshev.theta x ≤ 4 * Real.sqrt x * Real.log x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlx := Real.log_pos hx1
  have hε := robinParameter_pos hx1
  have hsx : 10 ≤ Real.sqrt x := by
    rw [show (10 : ℝ) = Real.sqrt 100 by rw [show (100 : ℝ) = 10 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set F := (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime with hF
  have hdiff : Real.log (robinExtremalAt x : ℝ) - Chebyshev.theta x
      = ∑ p ∈ F, ((robinExponent (robinParameter x) p : ℝ) - 1) * Real.log p := by
    rw [robinExtremalAt, log_robinExtremal, Chebyshev.theta_eq_sum_Icc x, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  -- each term is at most `2 log x`, and vanishes beyond `(3/2)√x`
  have hterm : ∀ p ∈ F, ((robinExponent (robinParameter x) p : ℝ) - 1) * Real.log p
      ≤ if 3 / 2 * Real.sqrt x < p then 0 else 2 * Real.log x := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpx : (p : ℝ) ≤ x := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      exact (Nat.le_floor_iff (by linarith)).mp this
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlp := Real.log_pos hp1
    have h1 : (1 : ℝ) ≤ robinExponent (robinParameter x) p := by
      exact_mod_cast (one_le_robinExponent_iff_le hx1 hpp).mpr hpx
    split_ifs with h
    · have h3 := robinExponent_le_one_of_gt (by linarith) hpp h
      have : (robinExponent (robinParameter x) p : ℝ) = 1 := by
        have : robinExponent (robinParameter x) p = 1 := by
          have := (one_le_robinExponent_iff_le hx1 hpp).mpr hpx; omega
        exact_mod_cast this
      rw [this]; simp
    · -- `a_p log p ≤ log Q_p ≤ 2 log x`
      have hpow := (le_robinExponent_iff hε hpp _).mp le_rfl
      have hQ : robinThreshold (robinParameter x) p ≤ x ^ 2 := by
        unfold robinThreshold
        set ε := robinParameter x
        have hd : ε * Real.log p ≤ (p : ℝ) ^ ε - 1 := by
          rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log p) ε]
          have := Real.add_one_le_exp (ε * Real.log p); linarith
        have hd0 : 0 < ε * Real.log p := mul_pos hε hlp
        have h2 : (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1) ≤ 1 / (ε * Real.log p) := by
          rw [div_le_div_iff₀ (lt_of_lt_of_le hd0 hd) hd0]
          have : 0 ≤ 1 / (p : ℝ) := by positivity
          nlinarith
        have h3 : 1 / (ε * Real.log p) ≤ (x + 1) * Real.log x / Real.log 2 := by
          have hl2 : Real.log 2 ≤ Real.log p :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le)
          have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          have hεl := le_robinParameter hx1
          rw [div_le_div_iff₀ hd0 hl20]
          have := mul_le_mul hεl hl2 hl20.le hε.le
          have e : 1 / ((x + 1) * Real.log x) * Real.log 2 * ((x + 1) * Real.log x)
              = Real.log 2 := by field_simp
          nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ (x + 1) * Real.log x by positivity)]
        have h4 : (x + 1) * Real.log x / Real.log 2 ≤ 4 * (x + 1) * Real.sqrt x := by
          have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
          have hls := log_le_two_sqrt_of_pos hx0
          rw [div_le_iff₀ (by linarith)]
          calc (x + 1) * Real.log x ≤ (x + 1) * (2 * Real.sqrt x) :=
                mul_le_mul_of_nonneg_left hls (by linarith)
            _ = 4 * (x + 1) * Real.sqrt x * (1 / 2) := by ring
            _ ≤ 4 * (x + 1) * Real.sqrt x * Real.log 2 :=
                mul_le_mul_of_nonneg_left hl2.le (by positivity)
        have h5 : 1 + 4 * (x + 1) * Real.sqrt x ≤ x ^ 2 := by
          have key : ∀ s : ℝ, 10 ≤ s → 1 + 4 * (s * s + 1) * s ≤ (s * s) ^ 2 := by
            intro s hs
            have hs0 : 0 < s := by linarith
            have h3 : 0 < s ^ 3 := pow_pos hs0 3
            have h6 : 10 * s ^ 3 ≤ s ^ 4 := by
              have := mul_le_mul_of_nonneg_left hs h3.le
              nlinarith
            have h8 : 100 ≤ s * s := by nlinarith
            have h9 : 100 * s ≤ s ^ 3 := by
              have := mul_le_mul_of_nonneg_right h8 hs0.le
              calc 100 * s ≤ s * s * s := this
                _ = s ^ 3 := by ring
            have h7 : 4 * s + 1 ≤ 6 * s ^ 3 := by linarith
            have e : (s * s) ^ 2 = s ^ 4 := by ring
            have e2 : 1 + 4 * (s * s + 1) * s = 4 * s ^ 3 + 4 * s + 1 := by ring
            rw [e, e2]
            linarith
          have := key (Real.sqrt x) hsx
          rwa [hxx] at this
        linarith
      have hQ0 : 0 < robinThreshold (robinParameter x) p := by
        have := one_le_robinThreshold hε hpp; linarith
      have hlog : (robinExponent (robinParameter x) p : ℝ) * Real.log p ≤ 2 * Real.log x := by
        rw [← Real.log_pow, ← Real.log_rpow hx0]
        refine Real.log_le_log (by positivity) (hpow.trans (hQ.trans ?_))
        rw [show (x ^ (2 : ℝ)) = x ^ 2 by norm_cast]
      nlinarith
  have hcard : ((F.filter (fun p : ℕ => ¬ 3 / 2 * Real.sqrt x < p)).card : ℝ)
      ≤ 2 * Real.sqrt x := by
    have hsub : F.filter (fun p : ℕ => ¬ 3 / 2 * Real.sqrt x < p)
        ⊆ Finset.Icc 0 ⌊3 / 2 * Real.sqrt x⌋₊ := by
      intro p hp
      simp only [Finset.mem_filter, not_lt] at hp
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hp.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((⌊3 / 2 * Real.sqrt x⌋₊ + 1 - 0 : ℕ) : ℝ) ≤ 3 / 2 * Real.sqrt x + 1 := by
      rw [Nat.sub_zero]; push_cast
      linarith [Nat.floor_le (show 0 ≤ 3 / 2 * Real.sqrt x by positivity)]
    have h3 : ((F.filter (fun p : ℕ => ¬ 3 / 2 * Real.sqrt x < p)).card : ℝ)
        ≤ ((⌊3 / 2 * Real.sqrt x⌋₊ + 1 - 0 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  rw [hdiff]
  calc ∑ p ∈ F, ((robinExponent (robinParameter x) p : ℝ) - 1) * Real.log p
      ≤ ∑ p ∈ F, (if 3 / 2 * Real.sqrt x < p then 0 else 2 * Real.log x) :=
        Finset.sum_le_sum hterm
    _ = ((F.filter (fun p : ℕ => ¬ 3 / 2 * Real.sqrt x < p)).card : ℝ) * (2 * Real.log x) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.sqrt x * (2 * Real.log x) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * Real.sqrt x * Real.log x := by ring


/-- `θ((5/4)√x)/√x → 5/4`. -/
theorem tendsto_theta_five_fourths_sqrt_div :
    Tendsto (fun x : ℝ => Chebyshev.theta (5 / 4 * Real.sqrt x) / Real.sqrt x) atTop
      (𝓝 (5 / 4)) := by
  have hy : Tendsto (fun x : ℝ => 5 / 4 * Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by norm_num)
  have h := (tendsto_theta_div_self.comp hy).const_mul (5 / 4)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  simp only [Function.comp]
  field_simp

/-- The exponent deficit of `N_x` dominates the prime squares beyond `(3/2)√x`. -/
theorem sum_prime_inv_sq_le_robinDeficit {x : ℝ} (hx : 12 < x) :
    ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => 3 / 2 * Real.sqrt x < p),
        1 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
          -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) := by
  have hx1 : 1 < x := by linarith
  have hnn : ∀ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
      0 ≤ -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have h0 : 0 < (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1) := by positivity
    have h1 : (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1) < 1 :=
      pow_lt_one₀ (by positivity) (by rw [div_lt_one (by linarith)]; exact hp1)
        (Nat.succ_ne_zero _)
    have := Real.log_nonpos (by linarith) (by linarith :
      1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1) ≤ 1)
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime)
    (fun p : ℕ => 3 / 2 * Real.sqrt x < p)]
  have h2 : 0 ≤ ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
      (fun p : ℕ => ¬ 3 / 2 * Real.sqrt x < p),
        -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) :=
    Finset.sum_nonneg fun p hp => hnn p (Finset.mem_filter.mp hp).1
  have h1 : ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
        (fun p : ℕ => 3 / 2 * Real.sqrt x < p), 1 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
        (fun p : ℕ => 3 / 2 * Real.sqrt x < p),
        -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpF, hps⟩ := Finset.mem_filter.mp hp
    have hpp := (Finset.mem_filter.mp hpF).2
    have hpx : (p : ℝ) ≤ x := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpF).1).2
      exact (Nat.le_floor_iff (by linarith)).mp this
    have hone : robinExponent (robinParameter x) p = 1 := by
      have h3 := robinExponent_le_one_of_gt hx hpp hps
      have h4 := (one_le_robinExponent_iff_le hx1 hpp).mpr hpx
      omega
    rw [hone, show (1 : ℕ) + 1 = 2 from rfl]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hy : (1 / (p : ℝ)) ^ 2 ≤ 1 / 2 := by
      rw [div_pow, one_pow]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    have := (neg_log_one_sub_mem hy).1
    calc 1 / (p : ℝ) ^ 2 = (1 / (p : ℝ)) ^ 2 := (one_div_pow _ _).symm
      _ ≤ _ := this
  linarith

/-- The decomposition of `log(σ(N_x)/N_x)`. -/
theorem log_sigma_div_robinExtremalAt_eq {x : ℝ} (hx : 1 < x) :
    Real.log ((sigma 1 (robinExtremalAt x) : ℝ) / (robinExtremalAt x : ℝ))
      = (mertensProductError x - mertensError x) + mertensErrorRemainder (Real.log x)
        + (Chebyshev.psi x - x) / (x * Real.log x) + Real.log (Real.log x)
        + Real.eulerMascheroniConstant
        - ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
            -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) := by
  have hx0 : 0 < x := by linarith
  have h0 : Real.log ((sigma 1 (robinExtremalAt x) : ℝ) / (robinExtremalAt x : ℝ))
      = -Real.log (mertensPrimeProduct ⌊x⌋₊)
        - ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
            -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) :=
    log_sigma_div_robinExtremal_eq _ _
  have h1 : -Real.log (mertensPrimeProduct ⌊x⌋₊)
      = mertensProductError x + Real.log (Real.log x) + Real.eulerMascheroniConstant := by
    unfold mertensProductError; ring
  have h2 : mertensError x
      = mertensErrorRemainder (Real.log x) + (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [mertensErrorRemainder, Real.exp_log hx0]; ring
  rw [h0, h1]
  linarith

/-- **The scaled Robin defect at `N_x`, deterministic bound.**  For `x ≥ 10000` with `a_p ≥ 2` on
`p ≤ (5/4)√x`, `θ(x) ≥ 2x/5` and `|θ(x) - x| ≤ K√x log²x`:
`(log(σ(N)/N) - γ - log log log N) √x log x ≤ Δ√xL + G√xL - S√xL + (ψ - θ)/√x - θ((5/4)√x)/√x
+ (35/4)(K + 4)² log⁴x/√x`. -/
theorem robinDefect_robinExtremalAt_scaled_le {x K : ℝ} (hx : 10000 ≤ x)
    (h2 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 5 / 4 * Real.sqrt x →
      2 ≤ robinExponent (robinParameter x) p)
    (h25 : 2 / 5 * x ≤ Chebyshev.theta x)
    (hθ : |Chebyshev.theta x - x| ≤ K * Real.sqrt x * Real.log x ^ 2) :
    (Real.log ((sigma 1 (robinExtremalAt x) : ℝ) / (robinExtremalAt x : ℝ))
        - Real.eulerMascheroniConstant - Real.log (Real.log (Real.log (robinExtremalAt x : ℝ))))
        * (Real.sqrt x * Real.log x)
      ≤ (mertensProductError x - mertensError x) * (Real.sqrt x * Real.log x)
        + mertensErrorRemainder (Real.log x) * (Real.sqrt x * Real.log x)
        - (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => 3 / 2 * Real.sqrt x < p), 1 / (p : ℝ) ^ 2) * (Real.sqrt x * Real.log x)
        + (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x
        - Chebyshev.theta (5 / 4 * Real.sqrt x) / Real.sqrt x
        + 35 / 4 * (K + 4) ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ)) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hsx : 100 ≤ Real.sqrt x := by
    rw [show (100 : ℝ) = Real.sqrt 10000 by rw [show (10000 : ℝ) = 100 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < Real.log x := by linarith
  have hy₁x : 5 / 4 * Real.sqrt x ≤ x :=
    calc 5 / 4 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right (by linarith) hsx0.le
      _ = x := hxx
  have hdec := log_sigma_div_robinExtremalAt_eq hx1
  have hu1 := log_robinExtremalAt_ge hx1 hy₁x h2
  have hu2 := log_robinExtremalAt_sub_theta_le (by linarith : (100 : ℝ) ≤ x)
  have hES := sum_prime_inv_sq_le_robinDeficit (by linarith : (12 : ℝ) < x)
  set N := robinExtremalAt x with hNdef
  set u := Real.log (N : ℝ) with hu
  set E := ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
    -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) with hE
  set S := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
    (fun p : ℕ => 3 / 2 * Real.sqrt x < p), 1 / (p : ℝ) ^ 2 with hS
  set D := Real.sqrt x * Real.log x with hD
  have hD0 : 0 < D := mul_pos hsx0 hL0
  have hθy0 : 0 ≤ Chebyshev.theta (5 / 4 * Real.sqrt x) := Chebyshev.theta_nonneg _
  have hu25 : 2 / 5 * x ≤ u := by linarith
  have hu_gt : 1 < u := by linarith
  have hlu : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hux : |u - x| ≤ (K + 4) * Real.sqrt x * Real.log x ^ 2 := by
    have h3 : Real.log x ≤ Real.log x ^ 2 := by nlinarith
    have h4 : Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_left h3 hsx0.le
    rw [abs_le] at hθ ⊢
    constructor <;> nlinarith
  have hll1 := log_log_ge_add hx1 hu_gt
  have hll2 := sub_div_sub_le_sq hx1 hu25 hlu
  have f1 : (Chebyshev.psi x - x) / (x * Real.log x) * D
      = (Chebyshev.psi x - x) / Real.sqrt x := by
    calc (Chebyshev.psi x - x) / (x * Real.log x) * D
        = (Chebyshev.psi x - x) * Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by
          rw [hD, hxx]; field_simp
      _ = _ := by field_simp
  have f2 : (u - x) / (x * Real.log x) * D = (u - x) / Real.sqrt x := by
    calc (u - x) / (x * Real.log x) * D
        = (u - x) * Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by rw [hD, hxx]; field_simp
      _ = _ := by field_simp
  have f3 : 35 / 4 * ((u - x) ^ 2 / (x ^ 2 * Real.log x)) * D
      = 35 / 4 * ((u - x) ^ 2 / (x * Real.sqrt x)) := by
    rw [hD]; field_simp
    rw [Real.sq_sqrt hx0.le]; ring
  have hsq : (u - x) ^ 2 / (x * Real.sqrt x)
      ≤ (K + 4) ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    have h5 : (u - x) ^ 2 ≤ ((K + 4) * Real.sqrt x * Real.log x ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hux 2
    have h6 : ((K + 4) * Real.sqrt x * Real.log x ^ 2) ^ 2
        = (K + 4) ^ 2 * x * Real.log x ^ 4 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le]; ring
    rw [h6] at h5
    calc (u - x) ^ 2 / (x * Real.sqrt x)
        ≤ (K + 4) ^ 2 * x * Real.log x ^ 4 / (x * Real.sqrt x) :=
          div_le_div_of_nonneg_right h5 (by positivity)
      _ = (K + 4) ^ 2 * (Real.log x ^ 4 / Real.sqrt x) := by field_simp
  have hψu : (Chebyshev.psi x - x) / Real.sqrt x - (u - x) / Real.sqrt x
      ≤ (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x
        - Chebyshev.theta (5 / 4 * Real.sqrt x) / Real.sqrt x := by
    rw [← sub_div, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hsx0.le
  have hllb : (u - x) / (x * Real.log x) - 35 / 4 * ((u - x) ^ 2 / (x ^ 2 * Real.log x))
      ≤ Real.log (Real.log u) - Real.log (Real.log x) := by linarith
  have hpre : Real.log ((sigma 1 N : ℝ) / (N : ℝ)) - Real.eulerMascheroniConstant
      - Real.log (Real.log u)
      ≤ (mertensProductError x - mertensError x) + mertensErrorRemainder (Real.log x) - S
        + (Chebyshev.psi x - x) / (x * Real.log x)
        - ((u - x) / (x * Real.log x) - 35 / 4 * ((u - x) ^ 2 / (x ^ 2 * Real.log x))) := by
    rw [hdec]; linarith
  have hmul := mul_le_mul_of_nonneg_right hpre hD0.le
  have hexp : ((mertensProductError x - mertensError x) + mertensErrorRemainder (Real.log x) - S
        + (Chebyshev.psi x - x) / (x * Real.log x)
        - ((u - x) / (x * Real.log x) - 35 / 4 * ((u - x) ^ 2 / (x ^ 2 * Real.log x)))) * D
      = (mertensProductError x - mertensError x) * D + mertensErrorRemainder (Real.log x) * D
        - S * D + (Chebyshev.psi x - x) / (x * Real.log x) * D
        - (u - x) / (x * Real.log x) * D
        + 35 / 4 * ((u - x) ^ 2 / (x ^ 2 * Real.log x)) * D := by ring
  rw [hexp, f1, f2, f3] at hmul
  have h35 : 35 / 4 * ((u - x) ^ 2 / (x * Real.sqrt x))
      ≤ 35 / 4 * (K + 4) ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 35 / 4 by norm_num)
    linarith
  linarith only [hmul, hψu, h35]

/-- **Robin's inequality at the extremal numbers under RH.** -/
theorem eventually_robin_robinExtremalAt (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, Real.log ((sigma 1 (robinExtremalAt x) : ℝ) / (robinExtremalAt x : ℝ))
      < Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (robinExtremalAt x : ℝ))) := by
  obtain ⟨K, hK, hθK⟩ := exists_abs_theta_sub_le_of_riemannHypothesis hRH
  have ha3 := poleSharpConstant_lt_three_tenths
  have hΦ : ∀ L : ℝ, weilLagFunctionReal L ≤ poleSharpConstant := fun L => by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH L
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have E3 := (tendsto_order.1 (tendsto_mertensProductError_sub_scaled hRH)).2 (1 + 1 / 24)
    (by norm_num)
  have E4 := (tendsto_order.1 (tendsto_mertensErrorRemainder_scaled_sub_lag hRH)).2 (1 / 24)
    (by norm_num)
  have E5 := (tendsto_order.1 (tendsto_psi_sub_theta_div_sqrt hRH)).2 (1 + 1 / 24) (by norm_num)
  have E6 := (tendsto_order.1 tendsto_theta_five_fourths_sqrt_div).1 (5 / 4 - 1 / 24)
    (by norm_num)
  have E7 := eventually_sum_prime_inv_sq_scaled_ge (c := 3 / 2) (δ := 1 / 24) (by norm_num)
    (by norm_num)
  have E8 := (tendsto_order.1 ((tendsto_log_pow_div_rpow_atTop 4 (r := 1 / 2)
    (by norm_num)).const_mul (35 / 4 * (K + 4) ^ 2))).2 (1 / 24) (by norm_num)
  filter_upwards [eventually_two_le_robinExponent, eventually_ge_atTop (10000 : ℝ),
    E3, E4, E5, E6, E7, E8, eventually_two_fifths_le_theta] with x h2 hx e3 e4 e5 e6 e7 e8 e9
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < Real.sqrt x * Real.log x :=
    mul_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos (by linarith))
  have hb := robinDefect_robinExtremalAt_scaled_le hx h2 e9 (hθK x (by linarith))
  have hΦx := hΦ (Real.log x)
  have hc : (2 : ℝ) / (3 / 2) - 1 / 24 = 31 / 24 := by norm_num
  rw [hc] at e7
  have hneg : (Real.log ((sigma 1 (robinExtremalAt x) : ℝ) / (robinExtremalAt x : ℝ))
        - Real.eulerMascheroniConstant - Real.log (Real.log (Real.log (robinExtremalAt x : ℝ))))
        * (Real.sqrt x * Real.log x) < 0 := by
    linarith only [hb, e3, e4, e5, e6, e7, e8, hΦx, ha3]
  have := neg_of_mul_neg_left hneg hD0.le
  linarith


/-! ## From the extremal numbers to every integer -/

/-- `log log u - log log ℓ ≤ (u - ℓ)/(ℓ log ℓ)` for `u, ℓ > 1`. -/
theorem log_log_sub_log_log_le {ℓ u : ℝ} (hℓ : 1 < ℓ) (hu : 1 < u) :
    Real.log (Real.log u) - Real.log (Real.log ℓ) ≤ (u - ℓ) / (ℓ * Real.log ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hu0 : 0 < u := by linarith
  have hlℓ := Real.log_pos hℓ
  have hlu := Real.log_pos hu
  have h1 : Real.log (Real.log u) - Real.log (Real.log ℓ) ≤ Real.log u / Real.log ℓ - 1 := by
    rw [← Real.log_div hlu.ne' hlℓ.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hlu hlℓ)
  have h2 : Real.log u - Real.log ℓ ≤ u / ℓ - 1 := by
    rw [← Real.log_div hu0.ne' hℓ0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hu0 hℓ0)
  have h3 : Real.log u / Real.log ℓ - 1 = (Real.log u - Real.log ℓ) / Real.log ℓ := by field_simp
  have h4 : (Real.log u - Real.log ℓ) / Real.log ℓ ≤ (u / ℓ - 1) / Real.log ℓ :=
    div_le_div_of_nonneg_right h2 hlℓ.le
  have h5 : (u / ℓ - 1) / Real.log ℓ = (u - ℓ) / (ℓ * Real.log ℓ) := by field_simp
  linarith

theorem continuousOn_robinParameter {a b : ℝ} (ha : 1 < a) :
    ContinuousOn robinParameter (Icc a b) := by
  unfold robinParameter
  refine ContinuousOn.div ?_ (Real.continuousOn_log.mono ?_) ?_
  · refine (Real.continuousOn_log.comp (continuousOn_const.add (continuousOn_const.div
      continuousOn_id ?_)) ?_)
    · intro t ht
      have : 1 < t := lt_of_lt_of_le ha ht.1
      exact (show (0 : ℝ) < t by linarith).ne'
    · intro t ht
      have : 1 < t := lt_of_lt_of_le ha ht.1
      simp only [mem_compl_iff, mem_singleton_iff]
      have : 0 < 1 / t := by positivity
      linarith
  · intro t ht
    have : 1 < t := lt_of_lt_of_le ha ht.1
    simp only [mem_compl_iff, mem_singleton_iff]; linarith
  · intro t ht
    exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'

/-- `θ(x) ≤ log N_x`. -/
theorem theta_le_log_robinExtremalAt {x : ℝ} (hx : 1 < x) :
    Chebyshev.theta x ≤ Real.log (robinExtremalAt x : ℝ) := by
  rw [robinExtremalAt, log_robinExtremal, Chebyshev.theta_eq_sum_Icc x]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := (Finset.mem_filter.mp hp).2
  have hpx : (p : ℝ) ≤ x := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact (Nat.le_floor_iff (by linarith)).mp this
  have h1 : (1 : ℝ) ≤ robinExponent (robinParameter x) p := by
    exact_mod_cast (one_le_robinExponent_iff_le hx hpp).mpr hpx
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  nlinarith

/-- **Robin's inequality for all large `n` under RH.** -/
theorem eventually_robin_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in atTop, (sigma 1 n : ℝ)
      < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (((eventually_robin_robinExtremalAt hRH).and
    (eventually_ge_atTop (100 : ℝ))).and eventually_two_fifths_le_theta)
  set X := max X₀ 100 with hX
  have hX100 : 100 ≤ X := le_max_right _ _
  have hX1 : 1 < X := by linarith
  have hεX := robinParameter_pos hX1
  -- `ℓ = log n` large enough that `1/(ℓ log ℓ) ≤ ε(X)` and `ℓ ≥ X`
  have hℓ : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => 1 / (Real.log n * Real.log (Real.log n))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hℓ.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp hℓ))
  filter_upwards [hsmall.eventually (ge_mem_nhds hεX), hℓ.eventually (eventually_ge_atTop X),
    eventually_ge_atTop 1] with n hn1 hn2 hn3
  set ℓ := Real.log n with hℓdef
  have hℓ1 : 1 < ℓ := by linarith
  have hlℓ := Real.log_pos hℓ1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn3
  set ε := 1 / (ℓ * Real.log ℓ) with hεdef
  have hε0 : 0 < ε := by positivity
  -- choose `x ∈ [X, ℓ]` with `ε(x) = ε`
  have hmem : ε ∈ Icc (robinParameter ℓ) (robinParameter X) :=
    ⟨robinParameter_le hℓ1, hn1⟩
  obtain ⟨x, ⟨hXx, hxℓ⟩, hxε⟩ :=
    intermediate_value_Icc' hn2 (continuousOn_robinParameter hX1) hmem
  have hx1 : 1 < x := by linarith
  obtain ⟨⟨hR, hx100⟩, hx25⟩ := hX₀ x (le_trans (le_max_left _ _) hXx)
  set N := robinExtremalAt x with hNdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast robinExtremal_pos _ _
  have hu1 : 1 < Real.log (N : ℝ) := by
    have := theta_le_log_robinExtremalAt hx1; linarith
  -- the Lagrangian inequality at `ε = ε(x)`
  have hB : ∀ p : ℕ, p.Prime → ⌊x⌋₊ < p → robinExponent (robinParameter x) p = 0 :=
    fun p hp hpx => robinExponent_eq_zero_of_floor_lt hx1 hp hpx
  have hlag := log_sigma_div_sub_le_robinExtremal (robinParameter_pos hx1) hB
    (show n ≠ 0 by omega)
  rw [← robinExtremalAt, ← hNdef, hxε] at hlag
  -- the mismatch
  have hmis := log_log_sub_log_log_le hℓ1 hu1
  have hmis' : Real.log (Real.log (Real.log (N : ℝ))) + ε * (ℓ - Real.log (N : ℝ))
      ≤ Real.log (Real.log ℓ) := by
    have e : (Real.log (N : ℝ) - ℓ) / (ℓ * Real.log ℓ) = ε * (Real.log (N : ℝ) - ℓ) := by
      rw [hεdef]; ring
    rw [e] at hmis
    linarith
  have hlog : Real.log ((sigma 1 n : ℝ) / (n : ℝ))
      < Real.eulerMascheroniConstant + Real.log (Real.log ℓ) := by
    rw [← hℓdef] at hlag
    linarith
  have hσ : (0 : ℝ) < sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)
  have hlℓ' : 0 < Real.log ℓ := hlℓ
  rw [Real.log_lt_iff_lt_exp (div_pos hσ hn0), Real.exp_add, Real.exp_log hlℓ',
    div_lt_iff₀ hn0] at hlog
  calc (sigma 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * Real.log ℓ * n := hlog
    _ = Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
        rw [hℓdef]; ring

/-- `n ≤ lcm(1, …, n)`. -/
theorem le_lcmUpto {n : ℕ} (hn : 1 ≤ n) : n ≤ Nat.lcmUpto n :=
  Nat.le_of_dvd (Nat.lcmUpto_pos n) (Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))

/-- **Robin's criterion.**  The Riemann hypothesis holds if and only if
`σ(n) < e^γ n log log n` for all large `n`. -/
theorem riemannHypothesis_iff_eventually_robin :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, (sigma 1 n : ℝ)
      < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  refine ⟨eventually_robin_of_riemannHypothesis, fun h => ?_⟩
  refine riemannHypothesis_of_eventually_robin_lcmUpto ?_
  have hlcm : Tendsto Nat.lcmUpto atTop atTop :=
    tendsto_atTop_mono' atTop (eventually_ge_atTop 1 |>.mono fun n hn => le_lcmUpto hn)
      tendsto_id
  exact hlcm.eventually h

end

end RHTower
