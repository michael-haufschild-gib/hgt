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

/-! ## The prime counting form -/

/-- `π(b) - π(a)` counts the primes of `(a, b]`. -/
theorem primeCounting_sub_eq_card_filter_Ioc {a b : ℕ} (hab : a ≤ b) :
    (Nat.primeCounting b : ℝ) - Nat.primeCounting a
      = (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) := by
  classical
  have hdisj : Disjoint ((Finset.range (a + 1)).filter Nat.Prime)
      ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp'
    omega
  have hunion : (Finset.range (b + 1)).filter Nat.Prime
      = ((Finset.range (a + 1)).filter Nat.Prime) ∪ ((Finset.Ioc a b).filter Nat.Prime) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h3⟩
  have hcard : Nat.primeCounting a + ((Finset.Ioc a b).filter Nat.Prime).card
      = Nat.primeCounting b := by
    unfold Nat.primeCounting Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, hunion,
      Finset.card_union_of_disjoint hdisj]
  have hR : ((Nat.primeCounting a : ℝ) + (((Finset.Ioc a b).filter Nat.Prime).card : ℝ))
      = (Nat.primeCounting b : ℝ) := by exact_mod_cast hcard
  linarith

/-- **The prime count against `θ`.**  Every prime of the window has logarithm between `log x` and
`log (x + y)`, so `log x · N ≤ θ(x+y) - θ(x) ≤ log(x+y) · N`.  Unconditional. -/
theorem theta_window_between_log_mul_card {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) :
    Real.log x * ((((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℕ) : ℝ)
        ≤ Chebyshev.theta (x + y) - Chebyshev.theta x ∧
      Chebyshev.theta (x + y) - Chebyshev.theta x
        ≤ Real.log (x + y) * ((((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℕ) : ℝ) := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hbounds : ∀ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime,
      Real.log x ≤ Real.log p ∧ Real.log p ≤ Real.log (x + y) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hlow : x < (p : ℝ) := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hp.1.1
      linarith [Nat.lt_floor_add_one x]
    have hup : (p : ℝ) ≤ x + y := by
      have h1 : (p : ℝ) ≤ (⌊x + y⌋₊ : ℝ) := by exact_mod_cast hp.1.2
      linarith [Nat.floor_le (show (0 : ℝ) ≤ x + y by linarith)]
    exact ⟨Real.log_le_log hx0 hlow.le, Real.log_le_log (by linarith) hup⟩
  rw [Sieve.theta_sub_eq_sum_Ioc (by linarith : x ≤ x + y)]
  constructor
  · have h := Finset.card_nsmul_le_sum ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log x) fun p hp => (hbounds p hp).1
    rwa [nsmul_eq_mul, mul_comm] at h
  · have h := Finset.sum_le_card_nsmul ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log (x + y)) fun p hp => (hbounds p hp).2
    rwa [nsmul_eq_mul, mul_comm] at h

/-- **Guth–Maynard Corollary 1.3 for `π`.**  For every `ε > 0` there is `x₀` with

`|π(⌊x+y⌋) - π(⌊x⌋) - y/log x| ≤ y exp(-(log x)^{1/4})`

for all `x ≥ x₀` and all `y ∈ [x^{17/30+ε}, x^{0.99}]`.  The transfer from `ψ` is the sandwich
`θ/log(x+y) ≤ N ≤ θ/log x`, whose width is `θ (log(x+y) - log x)/(log x log(x+y)) ≤ 2y²/x`, plus
`|ψ - θ| ≤ 2√t log t` and `√x ≤ y x^{-1/15}`.  Carries the Theorem 1.1 datum. -/
theorem exists_abs_primeCounting_short_interval_le (hGM : GuthMaynardLargeValuesBound) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ x₀ : ℝ, 4 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |(Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ - y / Real.log x|
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) := by
  classical
  obtain ⟨xψ, hxψ4, hψ⟩ := exists_abs_psi_short_interval_le hGM hε (K := 2) (by norm_num)
  -- `8 e^{L^{1/4}} x^{-1/100} < 1` and `40 e^{L^{1/4}} (L+2) x^{-1/15} < 1`
  have hG1 := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := 1)
    (by norm_num : (0 : ℝ) < 1 / 100)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  have hG4 := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 1 (K := 1)
    (by norm_num : (0 : ℝ) < 1 / 15)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 40))
  have hG3 : ∀ᶠ x : ℝ in atTop, Real.log 4 ≤ Real.log x ^ ((1 : ℝ) / 4) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have hmain : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |(Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ - y / Real.log x|
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) := by
    filter_upwards [hG1, hG4, hG3, eventually_ge_atTop xψ, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (4 : ℝ)] with x h1 h4 h3 hxψ' hxe hx4
    intro y hy1 hy2
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; exact hxe
    have hLq : (0 : ℝ) ≤ Real.log x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    have hEx : (0 : ℝ) < Real.exp (Real.log x ^ ((1 : ℝ) / 4)) := Real.exp_pos _
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hy1
    -- the three smallness inputs, cleared of their `rpow`s
    rw [pow_zero, one_mul] at h1
    rw [pow_one] at h4
    have hx100 : x ^ (-((1 : ℝ) / 100)) = 1 / x ^ ((1 : ℝ) / 100) := by
      rw [Real.rpow_neg hx0.le]
      ring
    -- `y/x ≤ x^{-1/100}` and `√x ≤ y x^{-1/15}`
    have hyx100 : y / x ≤ x ^ (-((1 : ℝ) / 100)) := by
      rw [div_le_iff₀ hx0]
      have heq : x ^ (-((1 : ℝ) / 100)) * x ^ ((1 : ℝ)) = x ^ ((99 : ℝ) / 100) := by
        rw [← Real.rpow_add hx0]
        congr 1
        norm_num
      rw [Real.rpow_one] at heq
      exact le_trans hy2 (le_of_eq heq.symm)
    have hsqrt : Real.sqrt x ≤ y * x ^ (-((1 : ℝ) / 15)) := by
      rw [Real.sqrt_eq_rpow]
      have hstep : x ^ ((1 : ℝ) / 2) ≤ x ^ (17 / 30 + ε) * x ^ (-((1 : ℝ) / 15)) := by
        rw [← Real.rpow_add hx0]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      exact le_trans hstep
        (mul_le_mul_of_nonneg_right hy1 (Real.rpow_nonneg hx0.le _))
    -- the `ψ` window bound and the prime-power defect
    have hyx2 : y ≤ x / 2 := by
      have hx100' : x ^ (-((1 : ℝ) / 100)) ≤ 1 / 8 := by
        rw [hx100] at h1 ⊢
        have hxp : (0 : ℝ) < x ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hx0 _
        rw [mul_one_div, div_lt_div_iff₀ hxp (by norm_num)] at h1
        rw [div_le_div_iff₀ hxp (by norm_num)]
        nlinarith [hEx]
      have := mul_le_mul_of_nonneg_left (le_trans hyx100 hx100') hx0.le
      rw [mul_div_cancel₀ _ hx0.ne'] at this
      linarith
    have hψx := hψ x hxψ' y hy1 hy2
    have hpt1 := Chebyshev.psi_sub_theta_le (x := x + y) (by linarith)
    have hpt2 := Chebyshev.psi_sub_theta_le (x := x) hx1
    have htp1 := Chebyshev.theta_le_psi (x + y)
    have htp2 := Chebyshev.theta_le_psi x
    have hsq2 : Real.sqrt (x + y) ≤ 2 * Real.sqrt x := by
      have h2x : x + y ≤ 4 * x := by linarith
      calc Real.sqrt (x + y) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt h2x
        _ = 2 * Real.sqrt x := by
            rw [show (4 : ℝ) * x = 2 ^ 2 * x by norm_num, Real.sqrt_mul (by positivity),
              Real.sqrt_sq (by norm_num)]
    have hlog2x : Real.log (x + y) ≤ 2 * Real.log x := by
      have h1' : Real.log (x + y) ≤ Real.log (x * x) := Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_mul hx0.ne' hx0.ne'] at h1'
      linarith
    have hsqx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    -- `|θ(x+y) - θ(x) - y| ≤ y e^{-2L^{1/4}} + 10 √x log x`
    have hdefect : 2 * Real.sqrt (x + y) * Real.log (x + y) + 2 * Real.sqrt x * Real.log x
        ≤ 10 * Real.sqrt x * Real.log x := by
      have hcross : 2 * Real.sqrt (x + y) * Real.log (x + y)
          ≤ 2 * (2 * Real.sqrt x) * (2 * Real.log x) := by
        have hl0 : (0 : ℝ) ≤ Real.log (x + y) := Real.log_nonneg (by linarith)
        gcongr
      nlinarith [hsqx0, hL1]
    have hΘ : |Chebyshev.theta (x + y) - Chebyshev.theta x - y|
        ≤ y * Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) + 10 * Real.sqrt x * Real.log x := by
      have habs := abs_le.1 hψx
      rw [abs_le]
      constructor <;> linarith
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ,
        N = ((((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℕ) : ℝ) := ⟨_, rfl⟩
    have hN0 : 0 ≤ N := hNdef ▸ Nat.cast_nonneg _
    have hNeq : (Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ = N := by
      rw [hNdef]
      exact primeCounting_sub_eq_card_filter_Ioc (Nat.floor_le_floor (by linarith))
    obtain ⟨hNlow, hNup⟩ := theta_window_between_log_mul_card (x := x) (y := y)
      (by linarith) hy0.le
    rw [← hNdef] at hNlow hNup
    -- the sandwich width
    have hLL : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx0 (by linarith)
    have hL0 : (0 : ℝ) < Real.log x := by linarith
    have hL'0 : (0 : ℝ) < Real.log (x + y) := by linarith
    have hΘ0 : 0 ≤ Chebyshev.theta (x + y) - Chebyshev.theta x := by
      have := hNlow
      nlinarith [hN0, hL0]
    have hgap : Real.log (x + y) - Real.log x ≤ y / x := by
      have h1' : Real.log ((x + y) / x) ≤ (x + y) / x - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by linarith) hx0.ne'] at h1'
      have h2' : (x + y) / x - 1 = y / x := by field_simp
      linarith
    have hsand : |N - (Chebyshev.theta (x + y) - Chebyshev.theta x) / Real.log x|
        ≤ (Chebyshev.theta (x + y) - Chebyshev.theta x) * (y / x) := by
      rw [abs_le]
      constructor
      · rw [le_sub_iff_add_le, ← sub_le_iff_le_add']
        rw [div_le_iff₀ hL0] at *
        nlinarith [hNup, hgap, hΘ0, hL1, hL'0]
      · rw [sub_le_iff_le_add]
        have : (Chebyshev.theta (x + y) - Chebyshev.theta x) / Real.log x
            ≥ N := by rw [ge_iff_le, le_div_iff₀ hL0]; linarith
        nlinarith [mul_nonneg hΘ0 (div_nonneg hy0.le hx0.le)]
    -- assemble
    have hΘbound : Chebyshev.theta (x + y) - Chebyshev.theta x
        ≤ 2 * y + 10 * Real.sqrt x * Real.log x := by
      have := abs_le.1 hΘ
      have he1 : Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith
      nlinarith
    have hsplit : (Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ - y / Real.log x
        = (N - (Chebyshev.theta (x + y) - Chebyshev.theta x) / Real.log x)
          + ((Chebyshev.theta (x + y) - Chebyshev.theta x) - y) / Real.log x := by
      rw [hNeq]
      field_simp
    rw [hsplit]
    refine le_trans (abs_add _ _) ?_
    have hterm2 : |((Chebyshev.theta (x + y) - Chebyshev.theta x) - y) / Real.log x|
        ≤ y * Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) + 10 * Real.sqrt x * Real.log x := by
      rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
      nlinarith [abs_nonneg (Chebyshev.theta (x + y) - Chebyshev.theta x - y), hΘ,
        mul_nonneg hsqx0 hL0.le, hy0.le, Real.exp_nonneg (-(2 * Real.log x ^ ((1 : ℝ) / 4)))]
    -- the four pieces against `y e^{-L^{1/4}}/4`
    have hA : (2 * y + 10 * Real.sqrt x * Real.log x) * (y / x)
        ≤ 2 * (y * (y / x)) + 10 * Real.sqrt x * Real.log x * (y / x) := by ring_nf; linarith
    have hq1 : 2 * (y * (y / x)) ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) / 4 := by
      have hx100' : Real.exp (Real.log x ^ ((1 : ℝ) / 4)) * (y / x) ≤ 1 / 8 := by
        refine le_trans (mul_le_mul_of_nonneg_left hyx100 hEx.le) ?_
        rw [hx100] at h1 ⊢
        linarith
      rw [Real.exp_neg, ← one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith [hy0.le, div_nonneg hy0.le hx0.le]
    have hq2 : 10 * Real.sqrt x * Real.log x * (y / x)
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) / 4 := by
      have hstep : 10 * Real.sqrt x * Real.log x * (y / x)
          ≤ 10 * (y * x ^ (-((1 : ℝ) / 15))) * Real.log x * (y / x) := by
        have hfac : (0 : ℝ) ≤ 10 * (Real.log x * (y / x)) := by positivity
        nlinarith [hsqrt, hL0.le, div_nonneg hy0.le hx0.le]
      have hy1x : y / x ≤ 1 := by
        rw [div_le_one hx0]; linarith
      have hL2 : Real.log x ≤ Real.log x + 2 := by linarith
      have hkey : Real.exp (Real.log x ^ ((1 : ℝ) / 4))
          * ((Real.log x + 2) * x ^ (-((1 : ℝ) / 15))) ≤ 1 / 40 := le_of_lt h4
      have hnn : (0 : ℝ) ≤ x ^ (-((1 : ℝ) / 15)) := Real.rpow_nonneg hx0.le _
      rw [Real.exp_neg, ← one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith [hstep, hkey, hy0.le, hnn, hL0.le, hy1x, hEx.le]
    have hq3 : y * Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4)))
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) / 4 := by
      have h4e : (4 : ℝ) ≤ Real.exp (Real.log x ^ ((1 : ℝ) / 4)) := by
        rw [show (4 : ℝ) = Real.exp (Real.log 4) by rw [Real.exp_log]; norm_num, Real.exp_le_exp]
        exact h3
      have hsq : Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4)))
          * Real.exp (Real.log x ^ ((1 : ℝ) / 4)) ^ 2 = 1 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        simp only [Real.exp_eq_one_iff]
        ring
      rw [Real.exp_neg, ← one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith [hsq, hy0.le, hEx, h4e]
    have hq4 : 10 * Real.sqrt x * Real.log x
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) / 4 := by
      have hkey : Real.exp (Real.log x ^ ((1 : ℝ) / 4))
          * ((Real.log x + 2) * x ^ (-((1 : ℝ) / 15))) ≤ 1 / 40 := le_of_lt h4
      have hnn : (0 : ℝ) ≤ x ^ (-((1 : ℝ) / 15)) := Real.rpow_nonneg hx0.le _
      have hstep : 10 * Real.sqrt x * Real.log x
          ≤ 10 * (y * x ^ (-((1 : ℝ) / 15))) * (Real.log x + 2) := by
        nlinarith [hsqrt, hL0.le, hy0.le, hnn]
      rw [Real.exp_neg, ← one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith [hstep, hkey, hy0.le, hnn, hEx.le]
    calc |N - (Chebyshev.theta (x + y) - Chebyshev.theta x) / Real.log x|
          + |((Chebyshev.theta (x + y) - Chebyshev.theta x) - y) / Real.log x|
        ≤ (Chebyshev.theta (x + y) - Chebyshev.theta x) * (y / x)
          + (y * Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) + 10 * Real.sqrt x * Real.log x) :=
          add_le_add hsand hterm2
      _ ≤ (2 * y + 10 * Real.sqrt x * Real.log x) * (y / x)
          + (y * Real.exp (-(2 * Real.log x ^ ((1 : ℝ) / 4))) + 10 * Real.sqrt x * Real.log x) := by
          have := mul_le_mul_of_nonneg_right hΘbound (div_nonneg hy0.le hx0.le)
          linarith
      _ ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) := by linarith
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hmain
  exact ⟨max x₀ 4, le_max_right _ _, fun x hx => hx₀ x (le_trans (le_max_left _ _) hx)⟩

end RHTower

end
