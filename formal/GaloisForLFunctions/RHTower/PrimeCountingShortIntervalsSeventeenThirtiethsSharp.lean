import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsSharp
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Guth–Maynard Corollary 1.3 for `π`

For every `ε > 0` and every `y ∈ [x^{17/30+ε}, x^{0.99}]`,

`|π(x + y) - π(x) - y/log x| ≤ y exp(-(log x)^{1/4})`

for all large `x` (`exists_abs_primeCounting_short_interval_le`).

The transfer from `ψ` is elementary.  Writing `N = #{p prime : x < p ≤ x + y}`, the corpus window
bounds `N log x ≤ θ(x+y) - θ(x) ≤ N log(x+y)` give

`|N - (θ(x+y) - θ(x))/log x| ≤ (θ(x+y) - θ(x)) · (log(x+y) - log x)/(log x log(x+y))
   ≤ (θ(x+y) - θ(x)) · y/x`,

while `|ψ - θ| ≤ 2√t log t` on both endpoints costs `10 √x log x`.  With `y ≥ x^{17/30+ε}` one has
`√x ≤ y x^{-1/15}` and `y/x ≤ x^{-1/100}`, so all three errors are below `y exp(-(log x)^{1/4})/4`
once the `ψ` bound is taken with the saving `exp(-2(log x)^{1/4})`.

Everything except the `ψ` input is unconditional; the `ψ` input carries the single datum
`hGM : GuthMaynardLargeValuesBound`.
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Filter Topology RHTower.Sieve RHTower.GuthMaynard

/-! ## Plain-real assembly lemmas -/

/-- A quantity squeezed between `Θ/L'` and `Θ/L` is within `Θ g` of `Θ/L` when `L' - L ≤ g` and
`1 ≤ L ≤ L'`. -/
theorem abs_sub_div_le_of_between {N Θ L L' g : ℝ} (hL : 1 ≤ L) (hLL' : L ≤ L') (hΘ : 0 ≤ Θ)
    (hg : L' - L ≤ g) (hg0 : 0 ≤ g) (hlow : L * N ≤ Θ) (hup : Θ ≤ L' * N) :
    |N - Θ / L| ≤ Θ * g := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL'0 : (0 : ℝ) < L' := by linarith
  have h1 : N ≤ Θ / L := by rw [le_div_iff₀ hL0]; linarith
  have h2 : Θ / L' ≤ N := by rw [div_le_iff₀ hL'0]; linarith
  have h3 : Θ / L - Θ / L' ≤ Θ * g := by
    rw [div_sub_div _ _ hL0.ne' hL'0.ne', div_le_iff₀ (by positivity)]
    have e1 : Θ * L' - L * Θ = Θ * (L' - L) := by ring
    have e2 : Θ * (L' - L) ≤ Θ * g := mul_le_mul_of_nonneg_left hg hΘ
    have hLL1 : (1 : ℝ) ≤ L * L' := by nlinarith
    have e3 : Θ * g ≤ Θ * g * (L * L') :=
      le_mul_of_one_le_right (mul_nonneg hΘ hg0) hLL1
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Dividing by `L ≥ 1` does not increase a nonnegative bound. -/
theorem abs_div_le_of_abs_le {d L M : ℝ} (hL : 1 ≤ L) (hM : 0 ≤ M) (h : |d| ≤ M) :
    |d / L| ≤ M := by
  have hL0 : (0 : ℝ) < L := by linarith
  rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
  nlinarith [abs_nonneg d]

/-- From `E p < 1/8` and `η E = 1`: `2 y p ≤ y η/4`. -/
theorem two_mul_le_quarter_of_exp_mul_lt {y p η E : ℝ} (hy : 0 ≤ y) (hE : 0 < E)
    (hηE : η * E = 1) (h : E * p < 1 / 8) : 2 * (y * p) ≤ y * η / 4 := by
  have hη0 : 0 < η := by
    rcases le_or_gt η 0 with h0 | h0
    · nlinarith
    · exact h0
  have hlt : p < η / 8 := by
    have h2 := mul_lt_mul_of_pos_left h hη0
    rw [← mul_assoc, hηE, one_mul] at h2
    linarith
  nlinarith

/-- Doubling the exponent of the saving gains a factor `4` once `t ≥ log 4`. -/
theorem mul_exp_two_mul_le_quarter {y t : ℝ} (hy : 0 ≤ y) (ht : Real.log 4 ≤ t) :
    y * Real.exp (-(2 * t)) ≤ y * Real.exp (-t) / 4 := by
  have h1 : Real.exp (-t) ≤ 1 / 4 := by
    have h := Real.exp_le_exp.mpr (show -t ≤ -Real.log 4 by linarith)
    have h4 : Real.exp (-Real.log 4) = 1 / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    rwa [h4] at h
  have h2 : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  nlinarith [mul_nonneg hy (Real.exp_pos (-t)).le, h1, Real.exp_pos (-t)]

/-- From `sx ≤ y w`, `E((L+2)w) < 1/40` and `η E = 1`: `10 sx L ≤ y η/4`. -/
theorem ten_mul_le_quarter_of_exp_mul_lt {sx y w L η E : ℝ} (hsx : sx ≤ y * w) (hy : 0 ≤ y)
    (hL : 0 ≤ L) (hsx0 : 0 ≤ sx) (hE : 0 < E) (hηE : η * E = 1)
    (h : E * ((L + 2) * w) < 1 / 40) : 10 * sx * L ≤ y * η / 4 := by
  have hη0 : 0 < η := by
    rcases le_or_gt η 0 with h0 | h0
    · nlinarith
    · exact h0
  have hkey : (L + 2) * w < η / 40 := by
    have h2 := mul_lt_mul_of_pos_left h hη0
    rw [← mul_assoc, hηE, one_mul] at h2
    linarith
  have h1 : 10 * sx * L ≤ 10 * y * ((L + 2) * w) := by nlinarith
  have h2 : 10 * y * ((L + 2) * w) ≤ 10 * y * (η / 40) :=
    mul_le_mul_of_nonneg_left hkey.le (by linarith)
  linarith

/-- The four error pieces of the transfer add up to the target. -/
theorem transfer_pieces_le {A B Θ p s t y g : ℝ} (hA : A ≤ Θ * p) (hΘ : Θ ≤ 2 * y + s)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hB : B ≤ t + s) (hs0 : 0 ≤ s)
    (h1 : 2 * (y * p) ≤ g / 4) (h2 : s ≤ g / 4) (h3 : t ≤ g / 4) :
    A + B ≤ g := by
  have e1 : Θ * p ≤ (2 * y + s) * p := mul_le_mul_of_nonneg_right hΘ hp0
  have e2 : (2 * y + s) * p = 2 * (y * p) + s * p := by ring
  have e3 : s * p ≤ s := by nlinarith
  linarith

/-! ## Elementary window estimates -/

/-- `√(x + y) ≤ 2√x` for `y ≤ 3x`. -/
theorem sqrt_add_le_two_mul_sqrt {x y : ℝ} (hy : y ≤ 3 * x) :
    Real.sqrt (x + y) ≤ 2 * Real.sqrt x := by
  have h4 : x + y ≤ 4 * x := by linarith
  calc Real.sqrt (x + y) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt h4
    _ = 2 * Real.sqrt x := by
        rw [show (4 : ℝ) * x = 2 ^ 2 * x by norm_num, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]

/-- `log (x + y) ≤ 2 log x` for `y ≤ x² - x`. -/
theorem log_add_le_two_mul_log {x y : ℝ} (hx : 2 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ x * x - x) :
    Real.log (x + y) ≤ 2 * Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : Real.log (x + y) ≤ Real.log (x * x) := Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul hx0.ne' hx0.ne'] at h1
  linarith

/-- `log (x + y) - log x ≤ y/x`. -/
theorem log_add_sub_log_le_div {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    Real.log (x + y) - Real.log x ≤ y / x := by
  have h1 : Real.log ((x + y) / x) ≤ (x + y) / x - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by linarith) hx.ne'] at h1
  have h2 : (x + y) / x - 1 = y / x := by field_simp
  linarith

/-- `y/x ≤ x^{-1/100}` once `y ≤ x^{99/100}`. -/
theorem div_le_rpow_neg_hundredth {x y : ℝ} (hx : 0 < x) (hy : y ≤ x ^ ((99 : ℝ) / 100)) :
    y / x ≤ x ^ (-((1 : ℝ) / 100)) := by
  rw [div_le_iff₀ hx]
  have heq : x ^ (-((1 : ℝ) / 100)) * x ^ ((1 : ℝ)) = x ^ ((99 : ℝ) / 100) := by
    rw [← Real.rpow_add hx]; congr 1; norm_num
  rw [Real.rpow_one] at heq
  exact le_trans hy (le_of_eq heq.symm)

/-- `y ≤ x/2` once `y ≤ x^{99/100}` and `x^{-1/100} ≤ 1/2`. -/
theorem le_half_of_rpow_le {x y : ℝ} (hx : 0 < x) (hy : y ≤ x ^ ((99 : ℝ) / 100))
    (hh : x ^ (-((1 : ℝ) / 100)) ≤ 1 / 2) : y ≤ x / 2 := by
  have h := le_trans (div_le_rpow_neg_hundredth hx hy) hh
  rw [div_le_iff₀ hx] at h
  linarith

/-- `√x ≤ y x^{-1/15}` once `y ≥ x^{17/30+ε}` with `ε ≥ 0`. -/
theorem sqrt_le_mul_rpow_neg_fifteenth {x y ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hy : x ^ (17 / 30 + ε) ≤ y) : Real.sqrt x ≤ y * x ^ (-((1 : ℝ) / 15)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.sqrt_eq_rpow]
  have hstep : x ^ ((1 : ℝ) / 2) ≤ x ^ (17 / 30 + ε) * x ^ (-((1 : ℝ) / 15)) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact le_trans hstep (mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hx0.le _))

/-- The prime-power defect of a window:  `|(ψ(x+y) - ψ(x)) - (θ(x+y) - θ(x))| ≤ 10√x log x`. -/
theorem abs_psi_sub_theta_window_le {x y : ℝ} (hx : 4 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ x / 2) :
    |(Chebyshev.psi (x + y) - Chebyshev.psi x)
        - (Chebyshev.theta (x + y) - Chebyshev.theta x)|
      ≤ 10 * Real.sqrt x * Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hyxx : y ≤ x * x - x := by nlinarith
  have hy3 : y ≤ 3 * x := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ha1 : Chebyshev.psi (x + y) - Chebyshev.theta (x + y)
      ≤ 2 * Real.sqrt (x + y) * Real.log (x + y) := Chebyshev.psi_sub_theta_le (by linarith)
  have ha0 : 0 ≤ Chebyshev.psi (x + y) - Chebyshev.theta (x + y) := by
    linarith [Chebyshev.theta_le_psi (x + y)]
  have hb1 : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
    Chebyshev.psi_sub_theta_le hx1
  have hb0 : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by linarith [Chebyshev.theta_le_psi x]
  have hsq := sqrt_add_le_two_mul_sqrt hy3
  have hlg := log_add_le_two_mul_log (by linarith : (2 : ℝ) ≤ x) hy0 hyxx
  have hl'0 : (0 : ℝ) ≤ Real.log (x + y) := Real.log_nonneg (by linarith)
  have hcross : 2 * Real.sqrt (x + y) * Real.log (x + y) ≤ 8 * Real.sqrt x * Real.log x := by
    have hstep : 2 * Real.sqrt (x + y) * Real.log (x + y)
        ≤ 2 * (2 * Real.sqrt x) * (2 * Real.log x) := by
      gcongr
      exact Real.sqrt_nonneg _
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The window prime count is a difference of values of `π`.  Reuses the corpus identity
`card_primesInIoc`. -/
theorem card_windowPrimes_eq_primeCounting_sub {x y : ℝ} (hxy : x ≤ y) :
    ((windowPrimes x y).card : ℝ)
      = (Nat.primeCounting ⌊y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ := by
  have h := GaloisForLFunctions.HTGeometry.card_primesInIoc (Nat.floor_le_floor hxy)
  rw [GaloisForLFunctions.HTGeometry.primesInIoc] at h
  rw [windowPrimes]
  convert h using 3

/-! ## Corollary 1.3 for `π` -/

/-- **Guth–Maynard Corollary 1.3 for `π`.**  For every `ε > 0` there is `x₀` with

`|π(⌊x+y⌋) - π(⌊x⌋) - y/log x| ≤ y exp(-(log x)^{1/4})`

for all `x ≥ x₀` and all `y ∈ [x^{17/30+ε}, x^{0.99}]`.  Carries the Theorem 1.1 datum. -/
theorem exists_abs_primeCounting_short_interval_le (hGM : GuthMaynardLargeValuesBound) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ x₀ : ℝ, 4 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |(Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ - y / Real.log x|
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) := by
  obtain ⟨xψ, hxψ4, hψ⟩ := exists_abs_psi_short_interval_le hGM hε (K := 2) (by norm_num)
  have hG1 := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := 1)
    (by norm_num : (0 : ℝ) < 1 / 100)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  have hG4 := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 1 (K := 1)
    (by norm_num : (0 : ℝ) < 1 / 15)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 40))
  have hG3 : ∀ᶠ x : ℝ in atTop, Real.log 4 ≤ Real.log x ^ ((1 : ℝ) / 4) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have hG5 : ∀ᶠ x : ℝ in atTop, x ^ (-((1 : ℝ) / 100)) ≤ 1 / 2 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hmain : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |(Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ - y / Real.log x|
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) := by
    filter_upwards [hG1, hG4, hG3, hG5, eventually_ge_atTop xψ, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (4 : ℝ)] with x h1 h4 h3 h5 hxψ' hxe hx4
    intro y hy1 hy2
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; exact hxe
    have hL0 : (0 : ℝ) < Real.log x := by linarith
    have hLq : (0 : ℝ) ≤ Real.log x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hL0.le _
    have hEx : (0 : ℝ) < Real.exp (Real.log x ^ ((1 : ℝ) / 4)) := Real.exp_pos _
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hy1
    have hyx : y ≤ x / 2 := le_half_of_rpow_le hx0 hy2 h5
    -- the saving and its reciprocal
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) := ⟨_, rfl⟩
    have hηE : η * Real.exp (Real.log x ^ ((1 : ℝ) / 4)) = 1 := by
      rw [hηdef, ← Real.exp_add]; simp
    -- the window prime count and the two window bounds
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ((windowPrimes x (x + y)).card : ℝ) := ⟨_, rfl⟩
    have hN0 : 0 ≤ N := hNdef ▸ Nat.cast_nonneg _
    have hNeq : (Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ = N := by
      rw [hNdef]
      exact (card_windowPrimes_eq_primeCounting_sub (by linarith : x ≤ x + y)).symm
    obtain ⟨Θ, hΘdef⟩ : ∃ Θ : ℝ, Θ = Chebyshev.theta (x + y) - Chebyshev.theta x := ⟨_, rfl⟩
    have hNlow : Real.log x * N ≤ Θ := by
      rw [hNdef, hΘdef, mul_comm]
      exact PrimeCells.card_windowPrimes_mul_log_le hx1 (by linarith)
    have hNup : Θ ≤ Real.log (x + y) * N := by
      rw [hNdef, hΘdef, mul_comm]
      exact PrimeCells.theta_sub_le_card_mul_log hx0.le (by linarith)
    have hΘ0 : 0 ≤ Θ := by
      have := mul_nonneg hL0.le hN0
      linarith
    -- the error pieces
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 10 * Real.sqrt x * Real.log x := ⟨_, rfl⟩
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = y * Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hsdef]; positivity
    have hΨ := hψ x hxψ' y hy1 hy2
    have hdef := abs_psi_sub_theta_window_le hx4 hy0.le hyx
    have hΘy : |Θ - y| ≤ t + s := by
      have hc := abs_sub_le Θ (Chebyshev.psi (x + y) - Chebyshev.psi x) y
      have hd : |Θ - (Chebyshev.psi (x + y) - Chebyshev.psi x)| ≤ s := by
        rw [hsdef, abs_sub_comm, hΘdef]
        exact hdef
      rw [htdef]
      linarith
    have hΘb : Θ ≤ 2 * y + s := by
      have he1 : Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      have hle : t ≤ y := by
        rw [htdef]
        have h := mul_le_mul_of_nonneg_left he1 hy0.le
        rw [mul_one] at h
        exact h
      have := abs_le.1 hΘy
      linarith
    -- the sandwich width
    obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = y / x := ⟨_, rfl⟩
    have hp0 : 0 ≤ p := by rw [hpdef]; positivity
    have hp1 : p ≤ 1 := by rw [hpdef, div_le_one hx0]; linarith
    have hgap : Real.log (x + y) - Real.log x ≤ p := by
      rw [hpdef]; exact log_add_sub_log_le_div hx0 hy0.le
    have hLL : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx0 (by linarith)
    have hA := abs_sub_div_le_of_between hL1 hLL hΘ0 hgap hp0 hNlow hNup
    have hB : |(Θ - y) / Real.log x| ≤ t + s :=
      abs_div_le_of_abs_le hL1 (by rw [htdef]; positivity) hΘy
    -- the three quarter bounds
    have hq1 : 2 * (y * p) ≤ y * η / 4 := by
      refine two_mul_le_quarter_of_exp_mul_lt hy0.le hEx hηE ?_
      rw [hpdef]
      have hple : y / x ≤ x ^ (-((1 : ℝ) / 100)) := div_le_rpow_neg_hundredth hx0 hy2
      rw [one_mul, pow_zero, one_mul] at h1
      have := mul_le_mul_of_nonneg_left hple hEx.le
      linarith
    have hq2 : s ≤ y * η / 4 := by
      rw [hsdef]
      rw [one_mul, pow_one] at h4
      exact ten_mul_le_quarter_of_exp_mul_lt
        (sqrt_le_mul_rpow_neg_fifteenth hx1 hε.le hy1) hy0.le
        hL0.le (Real.sqrt_nonneg x) hEx hηE h4
    have hq3 : t ≤ y * η / 4 := by
      rw [htdef, hηdef]
      exact mul_exp_two_mul_le_quarter hy0.le h3
    -- assemble
    have hLne : Real.log x ≠ 0 := hL0.ne'
    have hsplit : (N - Θ / Real.log x) + (Θ - y) / Real.log x = N - y / Real.log x := by
      field_simp
    rw [hNeq, ← hsplit, ← hηdef]
    exact le_trans (abs_add _ _) (transfer_pieces_le hA hΘb hp0 hp1 hB hs0 hq1 hq2 hq3)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hmain
  exact ⟨max x₀ 4, le_max_right _ _, fun x hx => hx₀ x (le_trans (le_max_left _ _) hx)⟩

end RHTower

end
