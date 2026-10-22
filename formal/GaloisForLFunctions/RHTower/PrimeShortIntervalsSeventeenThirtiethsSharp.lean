import GaloisForLFunctions.RHTower.ZeroDensitySupremumVinogradovKorobov
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtieths

/-!
# Guth–Maynard Corollary 1.3: primes in `[x, x + y]` with the Vinogradov–Korobov error

For every `ε > 0` and every `y ∈ [x^{17/30+ε}, x^{0.99}]`,

`|ψ(x + y) - ψ(x) - y| ≤ y exp(-K (log x)^{1/4})`

for all large `x` and every constant `K` (`exists_abs_psi_short_interval_le`).

The explicit-formula bookkeeping is unconditional: with `h = y` and `h' = yη/8` the two window
bounds of `ChebyshevShortWindowLowerBound` and `ChebyshevShortWindowUpperBound` give

`|ψ(x + y) - ψ(x) - y| ≤ yη/4 + 32/(xyη) + 8y Σ_ρ x^{β-1} min(1, 64x²/(y²η)/(|ρ||1-ρ|))`,

so the whole statement reduces to `Σ ≤ η/16` together with `128 ≤ x y² η²`
(`abs_psi_window_sub_le_of_tsum_le`).  At `η = exp(-K (log x)^{1/4})` the cut-off `64x²/(y²η)` lies
below `x^{2u}` with `u = 13/30 - ε/2` (`window_cutoff_le_rpow`), and the density exponent
`30/13 + ε` makes the zero weight `o(exp(-K(log x)^{1/4}))` through the Vinogradov–Korobov saving
`exp(-κ (log x)^{2/7})`.

The density input, hence the two corollaries, carries the single datum
`hGM : GuthMaynardLargeValuesBound`.
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Filter Topology RHTower.Sieve RHTower.GuthMaynard

/-! ## The unconditional window bookkeeping -/

/-- **The two-sided short-window bound.**  For `0 < η ≤ 1`, `0 < y ≤ x/2` and `4 ≤ x`, a zero
weight below `η/16` at the cut-off `64x²/(y²η)` forces `|ψ(x+y) - ψ(x) - y| ≤ yη`.  The inner
window `h' = yη/8` costs `2h' = yη/4`, the trivial zeros cost `4/(xh') = 32/(xyη) ≤ yη/4` once
`128 ≤ xy²η²`, and the zeros cost at most `8yΣ ≤ yη/2`.  Unconditional. -/
theorem abs_psi_window_sub_le_of_tsum_le {x y η : ℝ} (hx : 4 ≤ x) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hy0 : 0 < y) (hyx : y ≤ x / 2) (hroom : 128 ≤ x * y ^ 2 * η ^ 2)
    (hZ : ∑' q : XiZeroCopy, zeroShortWeight x (64 * x ^ 2 / (y ^ 2 * η)) (q.1 : ℂ) ≤ η / 16) :
    |Chebyshev.psi (x + y) - Chebyshev.psi x - y| ≤ y * η := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨h', hh'def⟩ : ∃ h' : ℝ, h' = y * η / 8 := ⟨_, rfl⟩
  have hh'0 : 0 < h' := by rw [hh'def]; positivity
  have h2h' : 2 * h' ≤ y := by rw [hh'def]; nlinarith
  have hyx' : y ≤ x := by linarith
  -- the two cut-offs produced by the window bounds
  have hY8 : 8 * x ^ 2 / (y * h') = 64 * x ^ 2 / (y ^ 2 * η) := by
    rw [hh'def]; field_simp; ring
  have hY4 : 4 * x ^ 2 / (y * h') = 32 * x ^ 2 / (y ^ 2 * η) := by
    rw [hh'def]; field_simp; ring
  have hmono : ∑' q : XiZeroCopy, zeroShortWeight x (32 * x ^ 2 / (y ^ 2 * η)) (q.1 : ℂ)
      ≤ ∑' q : XiZeroCopy, zeroShortWeight x (64 * x ^ 2 / (y ^ 2 * η)) (q.1 : ℂ) :=
    tsum_zeroShortWeight_mono_right hx1 (by positivity) (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg x, sq_nonneg y])
  have hlow := psi_window_ge_sub_zeroShortWeight (x := x) (h := y) (h' := h')
    (by linarith) hh'0 h2h' hyx'
  have hup := psi_window_le_add_zeroShortWeight (x := x) (h := y) (h' := h') hx hh'0 h2h' hyx
  rw [hY8] at hlow
  rw [hY4] at hup
  -- the trivial-zero term
  have hterm : 4 / (x * h') ≤ y * η / 4 := by
    have he : 4 / (x * h') = 32 / (x * y * η) := by rw [hh'def]; field_simp; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  have hZ0 : 0 ≤ ∑' q : XiZeroCopy, zeroShortWeight x (64 * x ^ 2 / (y ^ 2 * η)) (q.1 : ℂ) :=
    tsum_nonneg fun q => zeroShortWeight_nonneg hx0.le (by positivity) _
  have h2h'eq : 2 * h' = y * η / 4 := by rw [hh'def]; ring
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The exponential saving at the exponent `13/30` -/

/-- **The weighted zero sum is `o(exp(-K(log x)^{1/4}))` below the exponent `13/30`.**  Carries the
Theorem 1.1 datum through the density exponent `30/13 + ε` with `ε = min(1, (1/u - 30/13)/2)`. -/
theorem tendsto_exp_quarter_mul_tsum_zeroShortWeight_seventeen_thirtieths
    (hGM : GuthMaynardLargeValuesBound) {K u c : ℝ} (hu : 0 < u) (hu' : u < 13 / 30)
    (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4))
      * ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)) atTop (𝓝 0) := by
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
  exact tendsto_exp_quarter_mul_tsum_zeroShortWeight_of_density (K := K) (by positivity)
    (by linarith) hu (by linarith) huA hc hD hdens

/-! ## The cut-off arithmetic -/

/-- With `y ≥ x^{17/30+ε}` and `64/η ≤ x^ε` the window cut-off `64x²/(y²η)` stays below
`x^{2u}`, `u = 13/30 - ε/2`:  `x²/y² ≤ x^{13/15 - 2ε}` and `x^ε x^{13/15-2ε} = x^{13/15-ε}`. -/
theorem window_cutoff_le_rpow {x y η ε : ℝ} (hx : 1 ≤ x) (hη : 0 < η)
    (hy : x ^ (17 / 30 + ε) ≤ y) (hroom : 64 / η ≤ x ^ ε) :
    64 * x ^ 2 / (y ^ 2 * η) ≤ x ^ (2 * (13 / 30 - ε / 2)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hy
  have hxsq : x ^ 2 = x ^ ((2 : ℝ)) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hysq : x ^ (2 * (17 / 30 + ε)) ≤ y ^ 2 := by
    have h1 : (x ^ (17 / 30 + ε)) ^ 2 ≤ y ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hy 2
    rwa [← Real.rpow_natCast (x ^ (17 / 30 + ε)) 2, ← Real.rpow_mul hx0.le,
      show (17 / 30 + ε) * ((2 : ℕ) : ℝ) = 2 * (17 / 30 + ε) by push_cast; ring] at h1
  have hquot : x ^ 2 / y ^ 2 ≤ x ^ (13 / 15 - 2 * ε) := by
    rw [hxsq, div_le_iff₀ (by positivity)]
    have hpos : (0 : ℝ) ≤ x ^ (13 / 15 - 2 * ε) := Real.rpow_nonneg hx0.le _
    calc x ^ ((2 : ℝ)) = x ^ (13 / 15 - 2 * ε) * x ^ (2 * (17 / 30 + ε)) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ x ^ (13 / 15 - 2 * ε) * y ^ 2 := mul_le_mul_of_nonneg_left hysq hpos
  have hsplit : 64 * x ^ 2 / (y ^ 2 * η) = 64 / η * (x ^ 2 / y ^ 2) := by
    field_simp
  rw [hsplit]
  calc 64 / η * (x ^ 2 / y ^ 2) ≤ x ^ ε * x ^ (13 / 15 - 2 * ε) :=
        mul_le_mul hroom hquot (by positivity) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (2 * (13 / 30 - ε / 2)) := by rw [← Real.rpow_add hx0]; congr 1; ring

/-! ## Corollary 1.3 -/

/-- **Guth–Maynard Corollary 1.3 for `ψ`.**  For every `ε > 0` and every constant `K` there is `x₀`
with

`|ψ(x + y) - ψ(x) - y| ≤ y exp(-K (log x)^{1/4})`

for all `x ≥ x₀` and all `y ∈ [x^{17/30+ε}, x^{0.99}]`.  Carries the Theorem 1.1 datum. -/
theorem exists_abs_psi_short_interval_le (hGM : GuthMaynardLargeValuesBound) {ε K : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ x₀ : ℝ, 4 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |Chebyshev.psi (x + y) - Chebyshev.psi x - y|
        ≤ y * Real.exp (-(K * Real.log x ^ ((1 : ℝ) / 4))) := by
  -- shrink `ε` so that the exponent window is nonempty and the density margin survives
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = min ε (1 / 4) := ⟨_, rfl⟩
  have he0 : 0 < e := hedef ▸ lt_min hε (by norm_num)
  have he4 : e ≤ 1 / 4 := hedef ▸ min_le_right _ _
  have heε : e ≤ ε := hedef ▸ min_le_left _ _
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 13 / 30 - e / 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hudef]; linarith
  have hu13 : u < 13 / 30 := by rw [hudef]; linarith
  -- the three eventual inputs
  have hE1 := (tendsto_exp_quarter_mul_tsum_zeroShortWeight_seventeen_thirtieths hGM (K := K)
    (c := 1) hu0 hu13 le_rfl).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hE2 := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := K) he0).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))
  have hE3 := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := 2 * K)
    (by norm_num : (0 : ℝ) < 2)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 128))
  have hE4 : ∀ᶠ x : ℝ in atTop, x ^ (-((1 : ℝ) / 100)) ≤ 1 / 2 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hmain : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |Chebyshev.psi (x + y) - Chebyshev.psi x - y|
        ≤ y * Real.exp (-(K * Real.log x ^ ((1 : ℝ) / 4))) := by
    filter_upwards [hE1, hE2, hE3, hE4, eventually_ge_atTop (4 : ℝ)]
      with x h1 h2 h3 h4 hx4
    intro y hy1 hy2
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hLq : (0 : ℝ) ≤ Real.log x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hL0 _
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.exp (-(K * Real.log x ^ ((1 : ℝ) / 4))) := ⟨_, rfl⟩
    have hη0 : 0 < η := hηdef ▸ Real.exp_pos _
    have hη1 : η ≤ 1 := by
      rw [hηdef, Real.exp_le_one_iff]
      have : 0 ≤ K * Real.log x ^ ((1 : ℝ) / 4) := mul_nonneg hK hLq
      linarith
    have hηinv : 1 / η = Real.exp (K * Real.log x ^ ((1 : ℝ) / 4)) := by
      rw [hηdef, Real.exp_neg, one_div, inv_inv]
    have hηE : η * Real.exp (K * Real.log x ^ ((1 : ℝ) / 4)) = 1 := by
      rw [hηdef, ← Real.exp_add]
      simp
    -- `y` is at least `x^{17/30+e}` and so at least `√x`
    have hy1' : x ^ (17 / 30 + e) ≤ y :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hy1
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hy1'
    -- `y ≤ x/2`
    have hyx : y ≤ x / 2 := by
      refine le_trans hy2 ?_
      have hfac : x ^ ((99 : ℝ) / 100) = x * x ^ (-((1 : ℝ) / 100)) := by
        rw [show ((99 : ℝ) / 100) = 1 + (-((1 : ℝ) / 100)) by norm_num, Real.rpow_add hx0,
          Real.rpow_one]
      rw [hfac]
      have := mul_le_mul_of_nonneg_left h4 hx0.le
      linarith
    -- `x ≤ y²`, hence `128 ≤ x y² η²`
    have hxy : x ≤ y ^ 2 := by
      have h1' : (x ^ (17 / 30 + e)) ^ 2 ≤ y ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hy1' 2
      have h2' : x ^ ((1 : ℝ)) ≤ (x ^ (17 / 30 + e)) ^ 2 := by
        rw [← Real.rpow_natCast (x ^ (17 / 30 + e)) 2, ← Real.rpow_mul hx0.le]
        refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
        push_cast
        linarith
      rw [Real.rpow_one] at h2'
      linarith
    have hroom : 128 ≤ x * y ^ 2 * η ^ 2 := by
      rw [pow_zero, one_mul] at h3
      have hx2 : x ^ (-(2 : ℝ)) = 1 / x ^ 2 := by
        rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le,
          Real.rpow_natCast, one_div]
      have hE0 : (0 : ℝ) < Real.exp (2 * K * Real.log x ^ ((1 : ℝ) / 4)) := Real.exp_pos _
      rw [hx2, mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)] at h3
      have hηsq : η ^ 2 * Real.exp (2 * K * Real.log x ^ ((1 : ℝ) / 4)) = 1 := by
        rw [hηdef, sq, ← Real.exp_add, ← Real.exp_add]
        simp only [Real.exp_eq_one_iff]
        ring
      have hxx : x * x ≤ x * y ^ 2 := mul_le_mul_of_nonneg_left hxy hx0.le
      have hηsq0 : (0 : ℝ) < η ^ 2 := by positivity
      nlinarith [h3, hηsq, hxx, hE0, hηsq0]
    -- the zero weight at the window cut-off
    have hcut : 64 * x ^ 2 / (y ^ 2 * η) ≤ 1 * x ^ (2 * u) := by
      rw [one_mul, hudef]
      refine window_cutoff_le_rpow hx1 hη0 hy1' ?_
      rw [pow_zero, one_mul] at h2
      have hxe : x ^ (-e) = 1 / x ^ e := by rw [Real.rpow_neg hx0.le, one_div]
      have hxe0 : (0 : ℝ) < x ^ e := Real.rpow_pos_of_pos hx0 _
      rw [hxe, mul_one_div, div_lt_div_iff₀ hxe0 (by norm_num)] at h2
      have hdiv : (64 : ℝ) / η = 64 * (1 / η) := by ring
      rw [hdiv, hηinv]
      linarith
    have hZu : ∑' q : XiZeroCopy, zeroShortWeight x (1 * x ^ (2 * u)) (q.1 : ℂ) ≤ η / 16 := by
      have hmul := mul_lt_mul_of_pos_left h1 hη0
      rw [← mul_assoc, hηE, one_mul] at hmul
      linarith
    have hZ : ∑' q : XiZeroCopy, zeroShortWeight x (64 * x ^ 2 / (y ^ 2 * η)) (q.1 : ℂ)
        ≤ η / 16 :=
      le_trans (tsum_zeroShortWeight_mono_right hx1 (by positivity) hcut) hZu
    rw [← hηdef]
    exact abs_psi_window_sub_le_of_tsum_le hx4 hη0 hη1 hy0 hyx hroom hZ
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hmain
  exact ⟨max x₀ 4, le_max_right _ _, fun x hx => hx₀ x (le_trans (le_max_left _ _) hx)⟩

end RHTower

end
