import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockBelowTheGridIsSharp
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# The second-order term of a horizon block

The horizon theorem says that past the critical curve a horizon block, divided by the overlap,
is `κ Q(H)`, and the coercivity theorem that at the critical curve the excess is of exact order
`1/K`. This file identifies the excess exactly. Above the grid the symbol is
`ν(τ) = log N/2π + O(1 + log(|τ|/N))` (`abs_nuSymbol_sub_log_le`), and the remainder costs `O(c^{−p})`
(`abs_remainder_le`, a dyadic sum whose block weights no longer contain `log N`). The rest is
`log N/2π` times the energy above the grid, which is the total energy (Plancherel and Poisson)
minus the part below the grid (Riemann sums). Hence (`horizon_layer_sharp`): along every schedule
with `c → ∞` and `c (log N)²/N → 0`,

`c⁻¹ ⟨W x, x⟩ − κ Q(H) − (log N/∫φ²) 𝒜_N → 0`,   `𝒜_N = (2/N) Σ_n h(log(n/N))² a_φ(cn/N)`,

where `a_φ(s) = Σ_{k ≥ 1} |φ̂(2πks)|²` is the aliasing density of the atom grid at overlap `s`.
The second-order term of the degeneration on a horizon window is Weil's form of the synthesized
test plus `log N` times the window average of the aliasing density at the local overlaps `c n/N`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### The archimedean symbol above the grid -/

theorem mu_neg (τ : ℝ) : mu (-τ) = mu τ := by
  unfold mu
  have e : (1 / 4 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ) / 2 =
      conj ((1 / 4 : ℂ) + Complex.I * (τ : ℂ) / 2) := by
    simp only [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_one, map_ofNat]
    push_cast; ring
  rw [e, ReflectedDigammaAnomaly.digamma_conj, Complex.conj_re]

/-- `μ(τ) = log|τ|/2π + O(1)` for `|τ| ≥ 2`. -/
theorem exists_abs_mu_sub_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 2 ≤ |τ| → |mu τ - Real.log |τ| / (2 * Real.pi)| ≤ C := by
  have hpi := Real.pi_pos
  refine ⟨(|digammaVerticalLogConstant| + 20) / (2 * Real.pi), by positivity, fun τ hτ => ?_⟩
  have hmu : mu τ = mu |τ| := by
    rcases abs_choice τ with h | h
    · rw [h]
    · rw [h, mu_neg]
  rw [hmu]
  set t := |τ| with ht
  have ht2 : 2 ≤ t := hτ
  have ht0 : 0 < t := by linarith
  -- upper bound from the vertical digamma bound
  have hup : mu t ≤ (Real.log t + |digammaVerticalLogConstant|) / (2 * Real.pi) := by
    have hψ := norm_digamma_vertical_le_log (σ := 1 / 4) (t := t / 2) (by norm_num) (by linarith)
      (by linarith)
    have e : ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I = 1 / 4 + Complex.I * (t : ℂ) / 2 := by
      push_cast; ring
    rw [e] at hψ
    have hre := (Complex.re_le_norm _).trans hψ
    have hlog : Real.log (t / 2) ≤ Real.log t := Real.log_le_log (by positivity) (by linarith)
    have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    unfold mu
    rw [le_div_iff₀ (by positivity)]
    have : 1 / (2 * Real.pi) * (Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re *
        (2 * Real.pi) = (Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re := by
      field_simp
    have h2 : Real.log Real.pi / (2 * Real.pi) * (2 * Real.pi) = Real.log Real.pi := by
      field_simp
    rw [sub_mul, this, h2]
    linarith [le_abs_self digammaVerticalLogConstant]
  -- lower bound
  have hlow := RHTower.mu_ge_log t
  rw [abs_of_pos ht0] at hlow
  have hl4 : Real.log t - Real.log 4 ≤ Real.log (1 + t / 4) := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlog4 : Real.log 4 ≤ 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  rw [abs_le]
  constructor
  · have : (Real.log t - 12) / (2 * Real.pi) ≤ mu t :=
      le_trans (div_le_div_of_nonneg_right (by linarith) (by positivity)) hlow
    have e : (Real.log t - 12) / (2 * Real.pi) = Real.log t / (2 * Real.pi) - 12 / (2 * Real.pi) := by
      ring
    have h12 : 12 / (2 * Real.pi) ≤ (|digammaVerticalLogConstant| + 20) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (by linarith [abs_nonneg digammaVerticalLogConstant])
        (by positivity)
    linarith
  · have e : (Real.log t + |digammaVerticalLogConstant|) / (2 * Real.pi) =
        Real.log t / (2 * Real.pi) + |digammaVerticalLogConstant| / (2 * Real.pi) := by ring
    have h20 : |digammaVerticalLogConstant| / (2 * Real.pi) ≤
        (|digammaVerticalLogConstant| + 20) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

/-- On the dyadic block `[2^j N e^{−A}, 2^{j+1} N e^{−A}]` the symbol is `log N/2π` up to
`C + X²/π + A + 1 + j`. -/
theorem abs_nuSymbol_sub_log_le {C : ℝ} (hC : ∀ τ : ℝ, 2 ≤ |τ| →
    |mu τ - Real.log |τ| / (2 * Real.pi)| ≤ C) (L : ℝ) (hA0 : 0 ≤ A) {N : ℕ}
    (hT : 2 ≤ (N : ℝ) * Real.exp (-A)) (j : ℕ) {sgn : ℝ} (hsgn : |sgn| = 1) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (2 ^ j * ((N : ℝ) * Real.exp (-A))) (2 * (2 ^ j * ((N : ℝ) * Real.exp (-A))))) :
    |nuSymbol (Real.exp L) (sgn * τ) - Real.log N / (2 * Real.pi)| ≤
      C + Real.exp L ^ 2 / Real.pi + A + 1 + j := by
  have hpi := Real.pi_pos
  have hT0 : 0 < (N : ℝ) * Real.exp (-A) := by linarith
  have hN0 : (0 : ℝ) < N := by
    by_contra h0; push Not at h0
    have : (N : ℝ) * Real.exp (-A) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 (Real.exp_pos _).le
    linarith
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ.1
  have habs : |sgn * τ| = τ := by rw [abs_mul, hsgn, one_mul, abs_of_pos hτ0]
  have hτ2 : 2 ≤ τ := by nlinarith [hτ.1]
  have hmu := hC (sgn * τ) (by rw [habs]; exact hτ2)
  rw [habs] at hmu
  have hPX := RHTower.Littlewood.abs_PX_le (Real.exp_pos L).le (sgn * τ)
  -- `log τ − log N` on the block
  have hlo : (j : ℝ) * Real.log 2 - A ≤ Real.log τ - Real.log N := by
    have h1 : Real.log (2 ^ j * ((N : ℝ) * Real.exp (-A))) ≤ Real.log τ :=
      Real.log_le_log (by positivity) hτ.1
    rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul hN0.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_pow] at h1
    linarith
  have hhi : Real.log τ - Real.log N ≤ (j + 1) * Real.log 2 - A := by
    have h1 : Real.log τ ≤ Real.log (2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))) :=
      Real.log_le_log hτ0 hτ.2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hT0.ne',
      Real.log_mul hN0.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at h1
    linarith
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hdiff : |Real.log τ - Real.log N| ≤ A + 1 + j := by
    rw [abs_le]; constructor <;> nlinarith
  have hdiv : |Real.log τ - Real.log N| / (2 * Real.pi) ≤ |Real.log τ - Real.log N| :=
    div_le_self (abs_nonneg _) (by linarith [Real.pi_gt_three])
  unfold nuSymbol
  have e : mu (sgn * τ) + PX (Real.exp L) (sgn * τ) - Real.log N / (2 * Real.pi) =
      (mu (sgn * τ) - Real.log τ / (2 * Real.pi)) + PX (Real.exp L) (sgn * τ) +
        (Real.log τ - Real.log N) / (2 * Real.pi) := by ring
  rw [e]
  calc |(mu (sgn * τ) - Real.log τ / (2 * Real.pi)) + PX (Real.exp L) (sgn * τ) +
        (Real.log τ - Real.log N) / (2 * Real.pi)|
      ≤ |mu (sgn * τ) - Real.log τ / (2 * Real.pi)| + |PX (Real.exp L) (sgn * τ)| +
          |Real.log τ - Real.log N| / (2 * Real.pi) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_of_eq ?_))
        rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ C + Real.exp L ^ 2 / Real.pi + (A + 1 + j) := by gcongr; exact hdiv.trans hdiff
    _ = C + Real.exp L ^ 2 / Real.pi + A + 1 + j := by ring

/-! ### The remainder above the grid -/

section Remainder

variable {Cφ p : ℝ} {ν : ℝ → ℝ} {Bh : ℝ}

/-- One dyadic block of the aliasing tail with a block-local weight bound `|ν| ≤ W`. -/
theorem integral_aliasIntegrand_block_le' (hCφ : 0 ≤ Cφ) (hp0 : 0 ≤ p)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ Bh) {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) {U : ℝ} (hU1 : 1 ≤ U) {W : ℝ}
    (hW : ∀ τ ∈ Set.Icc U (2 * U), |ν (sgn * τ)| ≤ W)
    (hint : IntervalIntegrable (aliasIntegrand φ ν h N w sgn) volume U (2 * U)) :
    ∫ τ in U..(2 * U), aliasIntegrand φ ν h N w sgn τ ≤
      Cφ * (w * U) ^ (-p) * W * ((U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : 0 < U := by linarith
  have hUle : U ≤ 2 * U := by linarith
  have hsgn1 : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> simp
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW U ⟨le_rfl, hUle⟩)
  set Wt : ℝ := Cφ * (w * U) ^ (-p) * W with hWt
  have hWt0 : 0 ≤ Wt := by positivity
  have hpt : ∀ τ ∈ Set.Icc U (2 * U), aliasIntegrand φ ν h N w sgn τ ≤
      Wt * (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hU0 hτ.1
    have habs : |sgn * τ| = τ := by rw [abs_mul, hsgn1, one_mul, abs_of_pos hτ0]
    have h1 := hdecay (w * (sgn * τ))
    rw [show ((w * (sgn * τ) : ℝ) : ℂ) = (w : ℂ) * ((sgn * τ : ℝ) : ℂ) by push_cast; ring] at h1
    have hwτ : |w * (sgn * τ)| = w * τ := by rw [abs_mul, abs_of_pos hw0, habs]
    rw [hwτ] at h1
    have h2 : (1 + w * τ) ^ (-p) ≤ (w * U) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hτ.1]) (by linarith)
    have hD0 : 0 ≤ ‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N := by
      positivity
    unfold aliasIntegrand
    calc ‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) * |ν (sgn * τ)|
        ≤ (Cφ * (w * U) ^ (-p)) *
          (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) * W :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (h1.trans (mul_le_mul_of_nonneg_left h2 hCφ)) hD0) (hW τ hτ) (abs_nonneg _)
            (by positivity)
      _ = Wt * (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) := by
          rw [hWt]; ring
  have hcontD : Continuous fun τ : ℝ =>
      ‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N :=
    ((continuous_norm_sq_dirichletPoly N (horizonWeights h N)).comp
      (continuous_const.mul continuous_id)).div_const _
  have hmono := intervalIntegral.integral_mono_on hUle hint
    ((continuous_const.mul hcontD).intervalIntegrable U (2 * U)) hpt
  simp only [Pi.mul_apply] at hmono
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  have hMV : ∫ τ in U..(2 * U), ‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 ≤
      U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2) := by
    have hS1 := sum_horizonWeights_sq_le hsupp hB hN (A := A)
    have hS2 := sum_mul_horizonWeights_sq_le hB N (h := h)
    rcases hsgn with rfl | rfl
    · simp only [one_mul]
      refine (integral_window_le N (horizonWeights h N) U).trans ?_
      gcongr
    · simp only [neg_one_mul]
      refine (integral_window_neg_le N (horizonWeights h N) U).trans ?_
      gcongr
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMV hN0.le) hWt0

/-- The numerics of a block with weight `V + j`. -/
theorem block_bound_le' (hCφ : 0 ≤ Cφ) {V : ℝ} (hV : 0 ≤ V) (hA : 0 ≤ A) {N : ℕ}
    (hNA : Real.exp A ≤ N) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    Cφ * (c / N * (2 ^ j * (N * Real.exp (-A)))) ^ (-p) * (V + j) *
        ((2 ^ j * (N * Real.exp (-A)) * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N) ≤
      209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) *
        (((2 : ℝ) ^ (1 - p)) ^ j * (V + j)) := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN0 : (0 : ℝ) < N := by linarith
  set T₀ : ℝ := N * Real.exp (-A) with hT₀
  set U : ℝ := 2 ^ j * T₀ with hU
  have hwU : c / N * U = c * 2 ^ j * Real.exp (-A) := by
    rw [hU, hT₀]; field_simp
  have hmass : (U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N ≤ 209 * Bh ^ 2 * 2 ^ j := by
    have hUN : U * Real.exp A = 2 ^ j * N := by
      rw [hU, hT₀, mul_assoc, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [div_le_iff₀ hN0]
    have hU' : U * (Bh ^ 2 * Real.exp A) = Bh ^ 2 * (2 ^ j * N) := by rw [← hUN]; ring
    have h208 : 208 * (N * Bh ^ 2) ≤ 208 * (2 ^ j * N * Bh ^ 2) := by
      have : (0 : ℝ) ≤ N * Bh ^ 2 := by positivity
      nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := j)]
    rw [hU']
    have hring : Bh ^ 2 * (2 ^ j * N) + 208 * (2 ^ j * N * Bh ^ 2) = 209 * Bh ^ 2 * 2 ^ j * N := by
      ring
    linarith
  have hrj : ((2 : ℝ) ^ (-p)) ^ j * 2 ^ j = ((2 : ℝ) ^ (1 - p)) ^ j := by
    rw [← mul_pow, show (1 : ℝ) - p = -p + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [hwU, rpow_block_eq hc j]
  calc Cφ * (c ^ (-p) * ((2 : ℝ) ^ (-p)) ^ j * Real.exp (p * A)) * (V + j) *
        ((U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N)
      ≤ Cφ * (c ^ (-p) * ((2 : ℝ) ^ (-p)) ^ j * Real.exp (p * A)) * (V + j) *
        (209 * Bh ^ 2 * 2 ^ j) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) *
        ((((2 : ℝ) ^ (-p)) ^ j * 2 ^ j) * (V + j)) := by ring
    _ = _ := by rw [hrj]

/-- **The aliasing tail with block weights `V + j`**: `≤ K_al V/c^p`, with no `log N`. -/
theorem integral_aliasing_le_of_blocks (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {V : ℝ} (hV : 1 ≤ V)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh)
    {N : ℕ} (hNA : Real.exp A ≤ N) {c : ℝ} (hc : 0 < c) {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1)
    (hν : ∀ j : ℕ, ∀ τ ∈ Set.Icc (2 ^ j * ((N : ℝ) * Real.exp (-A)))
      (2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))), |ν (sgn * τ)| ≤ V + j)
    (hint : MeasureTheory.IntegrableOn (aliasIntegrand φ ν h N (c / N) sgn)
      (Set.Ioi ((N : ℝ) * Real.exp (-A)))) :
    ∫ τ in Set.Ioi ((N : ℝ) * Real.exp (-A)), aliasIntegrand φ ν h N (c / N) sgn τ ≤
      aliasConst Cφ p A Bh * V / c ^ p := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hT₀1 : 1 ≤ (N : ℝ) * Real.exp (-A) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos A), one_mul]; exact hNA
  obtain ⟨hsum, htsum⟩ := tsum_blocks_le (A := A) (Bh := Bh) hp hCφ hc (a := V) hV
  refine (integral_Ioi_le_of_dyadic (by linarith) hint hsum (fun j => by positivity)
    fun j => ?_).trans htsum
  have hU1 : 1 ≤ 2 ^ j * ((N : ℝ) * Real.exp (-A)) := by
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := j)]
  have hintb : IntervalIntegrable (aliasIntegrand φ ν h N (c / N) sgn) volume
      (2 ^ j * ((N : ℝ) * Real.exp (-A))) (2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr (hint.mono_set ?_)
    intro τ hτ
    have : (N : ℝ) * Real.exp (-A) ≤ 2 ^ j * ((N : ℝ) * Real.exp (-A)) :=
      le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    exact lt_of_le_of_lt this hτ.1
  refine (integral_aliasIntegrand_block_le' hCφ (by linarith) hdecay hsupp hB hN
    (div_pos hc hN0) hsgn hU1 (hν j) hintb).trans ?_
  exact block_bound_le' hCφ (by linarith) hA hNA hc j

end Remainder

/-- The energy integrand `|φ̂(wτ)|² |D_x(τ)|²/N` is integrable (Plancherel). -/
theorem integrable_blockIntegrand (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    Integrable fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hT : Continuous (cx (centredHorizonTest φ h c N)) :=
    Complex.continuous_ofReal.comp (contDiff_centredHorizonTest hφ h c N).continuous
  have hTc : HasCompactSupport (cx (centredHorizonTest φ h c N)) :=
    (hasCompactSupport_centredHorizonTest hφsupp h hc hN).comp_left Complex.ofReal_zero
  have hi := RHTower.KernelStrip.integrable_norm_sq_paperFT (hT.integrable_of_hasCompactSupport hTc)
    (hT.memLp_of_hasCompactSupport hTc)
  refine (hi.const_mul ((c / N) ^ 2 * N)⁻¹).congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [norm_sq_paperFT_centredHorizonTest hφ.continuous hφc h hc hN τ]
  field_simp

/-- **The remainder above the grid**: replacing the symbol by `log N/2π` above the grid costs
`O(c^{−p})`. -/
theorem abs_remainder_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, 2 ≤ |τ| → |mu τ - Real.log |τ| / (2 * Real.pi)| ≤ C) (L : ℝ)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    {N : ℕ} (hNA : Real.exp A ≤ N) (hT2 : 2 ≤ (N : ℝ) * Real.exp (-A)) {c : ℝ} (hc : 0 < c) :
    |∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        (horizonSymbolIntegrand φ h c N (Real.exp L) τ -
          Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)))| ≤
      2 * (aliasConst Cφ p A Bh * (C + Real.exp L ^ 2 / Real.pi + A + 1) / c ^ p) := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN : 1 ≤ N := by exact_mod_cast hN1
  set T₀ : ℝ := (N : ℝ) * Real.exp (-A) with hT₀
  set ν' : ℝ → ℝ := fun τ => nuSymbol (Real.exp L) τ - Real.log N / (2 * Real.pi) with hν'
  set S : ℝ → ℝ := fun τ => horizonSymbolIntegrand φ h c N (Real.exp L) τ -
    Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)) with hS
  have hSi : Integrable S := (integrable_horizonSymbolIntegrand hφ hφsupp h hc hN L).sub
    ((integrable_blockIntegrand hφ hφsupp h hc hN).const_mul _)
  have hSeq : ∀ τ, S τ = ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) * ν' τ := fun τ => by
    simp only [hS, hν', horizonSymbolIntegrand]; ring
  refine (abs_integral_le_integral_abs).trans ?_
  have hunion : (Set.Icc (-T₀) T₀)ᶜ = Set.Iio (-T₀) ∪ Set.Ioi T₀ := by
    ext τ; simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hτ; by_contra hc'; push Not at hc'; exact hτ ⟨hc'.1, hc'.2⟩
    · rintro (hτ | hτ) ⟨h1, h2⟩ <;> linarith
  have habsi : Integrable fun τ => |S τ| := hSi.abs
  rw [hunion, setIntegral_union (Set.disjoint_left.mpr fun τ h1 h2 => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at h1 h2
      have : 0 ≤ T₀ := by positivity
      linarith) measurableSet_Ioi habsi.integrableOn habsi.integrableOn]
  have hpos : ∀ τ, |S τ| = aliasIntegrand φ ν' h N (c / N) 1 τ := by
    intro τ
    rw [hSeq, aliasIntegrand, one_mul, abs_mul, abs_of_nonneg (by positivity)]
  have hneg : ∀ τ, |S (-τ)| = aliasIntegrand φ ν' h N (c / N) (-1) τ := by
    intro τ
    rw [hSeq, aliasIntegrand, neg_one_mul, abs_mul, abs_of_nonneg (by positivity)]
  set V := C + Real.exp L ^ 2 / Real.pi + A + 1 with hV
  have hV1 : 1 ≤ V := by
    have : 0 ≤ Real.exp L ^ 2 / Real.pi := by positivity
    rw [hV]; linarith
  have hblocks : ∀ sgn : ℝ, |sgn| = 1 → ∀ j : ℕ, ∀ τ ∈ Set.Icc (2 ^ j * T₀) (2 * (2 ^ j * T₀)),
      |ν' (sgn * τ)| ≤ V + j := fun sgn hsgn j τ hτ =>
    abs_nuSymbol_sub_log_le hC L hA hT2 j hsgn hτ
  have hI1 : ∫ τ in Set.Ioi T₀, |S τ| ≤ aliasConst Cφ p A Bh * V / c ^ p := by
    have hfun : aliasIntegrand φ ν' h N (c / N) 1 = fun τ => |S τ| := funext fun τ => (hpos τ).symm
    have := integral_aliasing_le_of_blocks hp hCφ hdecay hV1 hsupp hA hB hNA hc (Or.inl rfl)
      (hblocks 1 (by norm_num)) (by rw [hfun]; exact habsi.integrableOn)
    rwa [hfun] at this
  have hI2 : ∫ τ in Set.Iio (-T₀), |S τ| ≤ aliasConst Cφ p A Bh * V / c ^ p := by
    have hcomp : Integrable fun τ => |S (-τ)| := habsi.comp_neg
    have hfun : aliasIntegrand φ ν' h N (c / N) (-1) = fun τ => |S (-τ)| :=
      funext fun τ => (hneg τ).symm
    have := integral_aliasing_le_of_blocks hp hCφ hdecay hV1 hsupp hA hB hNA hc (Or.inr rfl)
      (hblocks (-1) (by norm_num)) (by rw [hfun]; exact hcomp.integrableOn)
    rw [hfun] at this
    simp only [integral_comp_neg_Ioi (f := fun τ => |S τ|)] at this
    rw [← integral_Iic_eq_integral_Iio]
    exact this
  linarith

/-! ### The Riemann sum of the synthesized mass -/

/-- `N⁻¹ Σ_n h(log(n/N))² = ∫ e^y h(y)² dy + O(1/N)`. -/
theorem exists_abs_riemann_sq_sub_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |(N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 -
        ∫ y, Real.exp y * h y ^ 2| ≤ K / N := by
  have hg : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hgs
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hgs) hg (by norm_num)
  refine ⟨((Lg : ℝ) + ‖(1 : ℂ) - 1‖ * Bg) * Real.exp (2 * A), by
    have : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
    positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR := norm_riemannSum_sub_le hg hgs hA hBg hLg (s := 1) (by norm_num) (by norm_num) hN
  have hprof : ∀ r ∈ Icc 1 N, horizonProfile (fun y => h y ^ 2) 1 (r / N) =
      ((h (Real.log r - Real.log N) ^ 2 : ℝ) : ℂ) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
    rw [horizonProfile, if_pos (div_pos hr0 hN0), sub_self, Complex.cpow_zero, mul_one,
      Real.log_div hr0.ne' hN0.ne']
  have htr : horizonTransform (fun y => h y ^ 2) 1 = ((∫ y, Real.exp y * h y ^ 2 : ℝ) : ℂ) := by
    rw [horizonTransform, ← integral_complex_ofReal]
    congr 1; funext y
    push_cast; rw [one_mul]; ring
  rw [sum_congr rfl hprof, htr, ← Complex.ofReal_sum, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hR
  exact hR

/-! ### Limits of the error terms -/

theorem tendsto_log_pow_div_natCast (n : ℕ) :
    Tendsto (fun N : ℕ => Real.log N ^ n / N) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp

/-- **The energy above the grid, to `o(1/log N)`**: along `c ≥ 1`, `c (log N)²/N → 0`,
`log N (E_N − L_N − 2π 𝒜_N) → 0`. -/
theorem tendsto_log_mul_energyDefect (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log N * (blockEnergy φ h (c N) N - lowPart φ h (c N) N A -
      2 * Real.pi * horizonAlias φ h (c N) N)) atTop (𝓝 0) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := abs_blockEnergy_sub_le hφ hφsupp hh hsupp (A := A)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_abs_riemann_sq_sub_le hh hA hsupp
  obtain ⟨K₃, hK₃0, hK₃⟩ := abs_lowPart_sub_le hφ hφsupp hh hA hsupp
  set I₁ := ∫ u, φ u with hI₁
  have hhat := integral_normSq_horizonTransform hh hsupp
  -- eventual conditions
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := hlogN.eventually (eventually_ge_atTop 1)
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => by
      have := hc1 N; positivity) ?_ hclog
    filter_upwards [hev3] with N hN
    have hc0 : 0 ≤ c N / N := by have := hc1 N; positivity
    calc c N / N = c N / N * 1 := (mul_one _).symm
      _ ≤ c N / N * Real.log N ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc0
      _ = c N * Real.log N ^ 2 / N := by ring
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  have hR4 : Tendsto (fun N : ℕ => Real.log N ^ 4 / N) atTop (𝓝 0) := tendsto_log_pow_div_natCast 4
  have hevR : ∀ᶠ N : ℕ in atTop, Real.log N ^ 4 ≤ N * Real.exp (-A) := by
    filter_upwards [hR4.eventually (gt_mem_nhds (Real.exp_pos (-A))), eventually_ge_atTop 1]
      with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  -- the bound
  set B : ℕ → ℝ := fun N => Real.log N * (K₁ * c N / N + 2 * Real.pi * I₁ ^ 2 * (K₂ / N) +
    K₃ * (Real.sqrt (c N / N) + 1 / Real.sqrt (Real.log N ^ 4) + (Real.log N ^ 4) ^ 2 / N))
    with hB
  have hbound : ∀ᶠ N : ℕ in atTop, ‖Real.log N * (blockEnergy φ h (c N) N -
      lowPart φ h (c N) N A - 2 * Real.pi * horizonAlias φ h (c N) N)‖ ≤ B N := by
    filter_upwards [hev3, hev4, hevR, eventually_ge_atTop 1] with N h3 h4 hR hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog0 : 0 ≤ Real.log N := by linarith
    have hR1 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ h3
    have e1 := hK₁ (c N) (hc1 N) N h4
    have e2 := hK₂ N hN
    have e3 := hK₃ (c N) (by linarith [hc1 N]) N hN _ hR1 hR
    rw [hhat] at e3
    have hsplit : blockEnergy φ h (c N) N - lowPart φ h (c N) N A -
        2 * Real.pi * horizonAlias φ h (c N) N =
        (blockEnergy φ h (c N) N - (2 * Real.pi / N * I₁ ^ 2 *
          ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 + 2 * Real.pi * horizonAlias φ h (c N) N)) +
        2 * Real.pi * I₁ ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 -
          ∫ y, Real.exp y * h y ^ 2) -
        (lowPart φ h (c N) N A - I₁ ^ 2 * (2 * Real.pi * ∫ y, Real.exp y * h y ^ 2)) := by
      field_simp; ring
    rw [hsplit, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0, hB]
    refine mul_le_mul_of_nonneg_left ?_ hlog0
    have hI0 : 0 ≤ 2 * Real.pi * I₁ ^ 2 := by positivity
    calc _ ≤ |blockEnergy φ h (c N) N - (2 * Real.pi / N * I₁ ^ 2 *
          ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 + 2 * Real.pi * horizonAlias φ h (c N) N)| +
        |2 * Real.pi * I₁ ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 -
          ∫ y, Real.exp y * h y ^ 2)| +
        |lowPart φ h (c N) N A - I₁ ^ 2 * (2 * Real.pi * ∫ y, Real.exp y * h y ^ 2)| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ K₁ * c N / N + 2 * Real.pi * I₁ ^ 2 * (K₂ / N) +
          K₃ * (Real.sqrt (c N / N) + 1 / Real.sqrt (Real.log N ^ 4) + (Real.log N ^ 4) ^ 2 / N) := by
          rw [abs_mul, abs_of_nonneg hI0]
          gcongr
  refine squeeze_zero_norm' hbound ?_
  -- the bound tends to zero
  have t1 : Tendsto (fun N : ℕ => Real.log N * (c N / N)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hclog
    · have := hc1 N
      have := Real.log_natCast_nonneg N
      positivity
    · filter_upwards [hev3] with N hN
      have hc0 : 0 ≤ c N / N := by have := hc1 N; positivity
      calc Real.log N * (c N / N) ≤ Real.log N * Real.log N * (c N / N) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hN) hc0
        _ = c N * Real.log N ^ 2 / N := by ring
  have t2 : Tendsto (fun N : ℕ => Real.log N * (K₂ / N)) atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_natCast 1).const_mul K₂
    simp only [pow_one, mul_zero] at this
    exact this.congr fun N => by ring
  have t3 : Tendsto (fun N : ℕ => Real.log N * Real.sqrt (c N / N)) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hclog
    rw [Real.sqrt_zero] at hs
    refine hs.congr' ?_
    filter_upwards [hev3] with N hN
    simp only [Function.comp_apply]
    rw [show c N * Real.log N ^ 2 / N = Real.log N ^ 2 * (c N / N) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have t4 : Tendsto (fun N : ℕ => Real.log N * (1 / Real.sqrt (Real.log N ^ 4))) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hlogN
    refine this.congr' ?_
    filter_upwards [hev3] with N hN
    simp only [Function.comp_apply]
    rw [show Real.log N ^ 4 = (Real.log N ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    field_simp
  have t5 : Tendsto (fun N : ℕ => Real.log N * ((Real.log N ^ 4) ^ 2 / N)) atTop (𝓝 0) :=
    (tendsto_log_pow_div_natCast 9).congr fun N => by ring
  have hlim := ((t1.const_mul K₁).add ((t2.const_mul (2 * Real.pi * I₁ ^ 2)).add
    (((t3.add t4).add t5).const_mul K₃)))
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr fun N => ?_
  simp only [hB]
  ring

/-! ### The second-order term -/

theorem tendsto_div_of_log_sq {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun N => by have := hc1 N; positivity) ?_ hclog
  filter_upwards [hlogN.eventually (eventually_ge_atTop 1)] with N hN
  have hc0 : 0 ≤ c N / N := by have := hc1 N; positivity
  simp only [Function.comp_apply] at hN
  calc c N / N = c N / N * 1 := (mul_one _).symm
    _ ≤ c N / N * Real.log N ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc0
    _ = c N * Real.log N ^ 2 / N := by ring

/-- **The second-order term of a horizon block.** For a `C²` profile on `[0, 1]` with
`|φ̂(u)|² ≤ C_φ (1 + |u|)^{−p}`, `p > 1`, a `C²` window profile `h` on `[−A, 0]`, and every
schedule with `c_N ≥ 1`, `c_N → ∞`, `c_N (log N)²/N → 0`:
`c⁻¹ ⟨W x, x⟩ − κ Q(H) − (log N/∫φ²) 𝒜_N → 0`, where `𝒜_N = (2/N) Σ_n h(log(n/N))² a_φ(cn/N)`. -/
theorem horizon_layer_sharp (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) -
      Real.log N / (∫ u, φ u ^ 2) * horizonAlias φ h (c N) N) atTop (𝓝 0) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hpole := tendsto_polePart hφ.continuous hφc hh.continuous hsupp hA hcN
  have hlow := tendsto_lowFrequency hφ hφsupp hh hA hsupp hc0 hcN
  have hdef := tendsto_log_mul_energyDefect hφ hφsupp hh hA hsupp hc1 hclog
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  set M := ∫ u, φ u ^ 2 with hM
  set I₁ := ∫ u, φ u with hI₁
  set Ph := (horizonTransform h 0 * conj (horizonTransform h 1) +
    horizonTransform h 1 * conj (horizonTransform h 0)).re with hPh
  set Gh := ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
    nuSymbol (Real.exp (2 * (A + 1))) τ with hGh
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A)))ᶜ, (horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ -
        Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N))) with hRmdef
  -- the remainder above the grid vanishes
  have hRm : Tendsto Rm atTop (𝓝 0) := by
    set V := C + Real.exp (2 * (A + 1)) ^ 2 / Real.pi + A + 1 with hV
    have hcp : Tendsto (fun N : ℕ => c N ^ p) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hcinf
    have hlim : Tendsto (fun N : ℕ => 2 * (aliasConst Cφ p A Bh * V / c N ^ p)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := aliasConst Cφ p A Bh * V)).div_atTop hcp
      simpa using this.const_mul 2
    have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A)),
      hT.eventually (eventually_ge_atTop 2)] with N h1 h2
    rw [Real.norm_eq_abs]
    exact abs_remainder_le hφ hφsupp hp hCφ hdecay hC0 hC (2 * (A + 1)) hsupp hA hB h1 h2 (hc0 N)
  -- the identity
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_one hN0] at h1
    exact h1.le
  have hid : ∀ᶠ N : ℕ in atTop, M⁻¹ * ((alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
        alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)).re - I₁ ^ 2 * Ph) +
      M⁻¹ * ((∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
        horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ) - I₁ ^ 2 * Gh) +
      M⁻¹ * Rm N + M⁻¹ * ((2 * Real.pi)⁻¹ * (Real.log N * (blockEnergy φ h (c N) N -
        lowPart φ h (c N) N A - 2 * Real.pi * horizonAlias φ h (c N) N))) =
      (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      I₁ ^ 2 / M * weilQuad (halfWeight h) - Real.log N / M * horizonAlias φ h (c N) N := by
    filter_upwards [hcle, eventually_ge_atTop 1] with N h6 hN
    rw [horizonForm_eq hφ hφsupp hφ2 hsupp hA (hc0 N) hN h6, weilQuad_halfWeight_eq hh hsupp hA]
    have hS := integrable_horizonSymbolIntegrand hφ hφsupp h (hc0 N) hN (2 * (A + 1))
    have hE := integrable_blockIntegrand hφ hφsupp h (hc0 N) hN
    have hsplitS := (integral_add_compl (s := Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A))) measurableSet_Icc hS).symm
    have hsplitE := integral_add_compl (s := Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A))) measurableSet_Icc hE
    have hcompl : ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ = Rm N +
          Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A)))
            ((N : ℝ) * Real.exp (-A)))ᶜ, ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
              (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) := by
      simp only [hRmdef]
      rw [integral_sub hS.integrableOn (hE.const_mul _).integrableOn, integral_const_mul]
      ring
    have hEL : ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) =
        blockEnergy φ h (c N) N - lowPart φ h (c N) N A := by
      rw [blockEnergy, lowPart, ← hsplitE]; ring
    rw [hsplitS, hcompl, hEL, ← hM, ← hPh, ← hGh]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hM0 : M ≠ 0 := hφ2.ne'
    field_simp
    ring
  refine Tendsto.congr' hid ?_
  have l1 := (hpole.sub_const (I₁ ^ 2 * Ph)).const_mul M⁻¹
  have l2 := (hlow.sub_const (I₁ ^ 2 * Gh)).const_mul M⁻¹
  have l3 := hRm.const_mul M⁻¹
  have l4 := (hdef.const_mul (2 * Real.pi)⁻¹).const_mul M⁻¹
  have := ((l1.add l2).add l3).add l4
  simpa using this

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
