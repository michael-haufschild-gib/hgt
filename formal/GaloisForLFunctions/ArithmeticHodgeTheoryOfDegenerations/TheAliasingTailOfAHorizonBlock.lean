import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockIsQuietBelowTheGrid
import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare

/-!
# The aliasing tail of a horizon block

Above the atom grid, `|τ| > T₀ = N e^{−A}`, the Dirichlet polynomial of a horizon block is no longer
small pointwise: its atoms undersample the synthesized test and alias it to the frequencies near
`2πkN`. Its mean square is still controlled. The sharp mean-value theorem gives, on every window
`[U, 2U]`, `∫ |D_x|² ≤ U Σ x_n² + 208 Σ n x_n² ≤ B² (U e^A + 208 N)`, and the atom transform decays
like `(1 + |wτ|)^{−p}`. Summing over the dyadic windows `U = 2^j T₀`, `wT₀ = c e^{−A}`:

* **Aliasing bound** (`integral_aliasing_le`): for a weight `|ν(τ)| ≤ A_ν + log(2 + |τ|)`,
  `∫_{τ > T₀} ‖φ̂(wτ)‖² (|D_x(τ)|²/N) |ν(τ)| ≤ K_al (A_ν + 2 + log N)/c^p`, and the same on `τ < −T₀`.

At the critical curve `c^p ≍ log N` the aliasing tail is of the size of a constant: it is the
coercive part of the second-order term of the horizon layer, inversely proportional to the
multiple `K`. Past the critical curve it vanishes.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri Zeta23

/-! ### The corpus Dirichlet polynomial -/

theorem dirichletPoly_eq_dirPoly (N : ℕ) (x : ℕ → ℝ) (τ : ℝ) :
    dirichletPoly N x τ = RHTower.Sieve.dirPoly N (fun i => (x ((i : ℕ) + 1) : ℂ)) τ := by
  unfold dirichletPoly RHTower.Sieve.dirPoly
  rw [Fin.sum_univ_eq_sum_range (fun i => (x (i + 1) : ℂ) *
      Complex.exp (((τ * Real.log ((i : ℕ) + 1) : ℝ) : ℂ) * Complex.I)) N,
    show Icc 1 N = Ico 1 (N + 1) from rfl, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun k _ => ?_
  rw [add_comm 1 k]
  push_cast
  ring_nf

theorem sum_fin_norm_sq (N : ℕ) (x : ℕ → ℝ) :
    ∑ i : Fin N, ‖(x ((i : ℕ) + 1) : ℂ)‖ ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖(x (i + 1) : ℂ)‖ ^ 2) N,
    show Icc 1 N = Ico 1 (N + 1) from rfl, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, add_comm]

theorem sum_fin_mul_norm_sq (N : ℕ) (x : ℕ → ℝ) :
    ∑ i : Fin N, (((i : ℕ) : ℝ) + 1) * ‖(x ((i : ℕ) + 1) : ℂ)‖ ^ 2 =
      ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) * ‖(x (i + 1) : ℂ)‖ ^ 2) N,
    show Icc 1 N = Ico 1 (N + 1) from rfl, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, add_comm 1 k]
  push_cast
  ring

/-- **Mean square on a window** (Montgomery–Vaughan form). -/
theorem integral_window_le (N : ℕ) (x : ℕ → ℝ) (U : ℝ) :
    ∫ τ in U..(2 * U), ‖dirichletPoly N x τ‖ ^ 2 ≤
      U * ∑ n ∈ Icc 1 N, x n ^ 2 + 208 * ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 := by
  have h := RHTower.Sieve.dirichlet_meanValue_sharp_window N
    (fun i => (x ((i : ℕ) + 1) : ℂ)) U (2 * U)
  rw [sum_fin_norm_sq, sum_fin_mul_norm_sq, show 2 * U - U = U by ring] at h
  simp only [← dirichletPoly_eq_dirPoly] at h
  have := (abs_le.mp h).2
  linarith

/-- The same on negative windows. -/
theorem integral_window_neg_le (N : ℕ) (x : ℕ → ℝ) (U : ℝ) :
    ∫ τ in U..(2 * U), ‖dirichletPoly N x (((-τ : ℝ) : ℂ))‖ ^ 2 ≤
      U * ∑ n ∈ Icc 1 N, x n ^ 2 + 208 * ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 := by
  have h := RHTower.Sieve.dirichlet_meanValue_sharp_window_neg N
    (fun i => (x ((i : ℕ) + 1) : ℂ)) U (2 * U)
  rw [sum_fin_norm_sq, sum_fin_mul_norm_sq, show 2 * U - U = U by ring] at h
  simp only [← dirichletPoly_eq_dirPoly] at h
  have := (abs_le.mp h).2
  linarith

/-! ### Mass of the horizon weights -/

section Mass

variable {h : ℝ → ℝ} {A Bh : ℝ}

theorem sum_horizonWeights_sq_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hB : ∀ y, |h y| ≤ Bh) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 ≤ Bh ^ 2 * Real.exp A := by
  set n₀ := windowStart A N
  have h1 := one_le_windowStart hN A
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn₀0 : (0 : ℝ) < n₀ := by exact_mod_cast h1
  have hterm : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 ≤ Bh ^ 2 / n₀ := by
    intro n hn
    rcases lt_or_ge n n₀ with hlt | hge
    · rw [horizonWeights_eq_zero_of_lt hsupp (mem_Icc.mp hn).1 hlt]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [horizonWeights, div_pow, Real.sq_sqrt hn0.le]
      have hh2 : h (Real.log n - Real.log N) ^ 2 ≤ Bh ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
      calc h (Real.log n - Real.log N) ^ 2 / n ≤ Bh ^ 2 / n := by gcongr
        _ ≤ Bh ^ 2 / n₀ := by gcongr
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hge := le_windowStart A N
  calc (N : ℝ) * (Bh ^ 2 / n₀) ≤ N * (Bh ^ 2 / (N * Real.exp (-A))) := by
        gcongr
    _ = Bh ^ 2 * Real.exp A := by
        rw [Real.exp_neg]; field_simp

theorem sum_mul_horizonWeights_sq_le (hB : ∀ y, |h y| ≤ Bh) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 ≤ N * Bh ^ 2 := by
  have hterm : ∀ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 ≤ Bh ^ 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [horizonWeights, div_pow, Real.sq_sqrt hn0.le, mul_div_cancel₀ _ hn0.ne', ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

end Mass

/-! ### Dyadic summation of a nonnegative tail -/

/-- If a nonnegative integrable tail has its dyadic blocks bounded by a summable sequence, the tail
is bounded by the sum. -/
theorem integral_Ioi_le_of_dyadic {g : ℝ → ℝ} {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hg : IntegrableOn g (Set.Ioi T₀)) {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ j, 0 ≤ b j)
    (hblock : ∀ j : ℕ, ∫ τ in (2 ^ j * T₀)..(2 * (2 ^ j * T₀)), g τ ≤ b j) :
    ∫ τ in Set.Ioi T₀, g τ ≤ ∑' j, b j := by
  have hlim : Tendsto (fun J : ℕ => ∫ τ in T₀..(2 ^ J * T₀), g τ) atTop
      (𝓝 (∫ τ in Set.Ioi T₀, g τ)) :=
    intervalIntegral_tendsto_integral_Ioi T₀ hg
      (Tendsto.atTop_mul_const hT₀ (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  refine le_of_tendsto hlim (Eventually.of_forall fun J => ?_)
  have hge : ∀ j : ℕ, T₀ ≤ 2 ^ j * T₀ := fun j =>
    le_mul_of_one_le_left hT₀.le (one_le_pow₀ (by norm_num))
  have hint : ∀ k < J, IntervalIntegrable g volume (2 ^ k * T₀) (2 ^ (k + 1) * T₀) := by
    intro k _
    have hle : 2 ^ k * T₀ ≤ 2 ^ (k + 1) * T₀ := by
      rw [pow_succ]; nlinarith [pow_pos (two_pos (α := ℝ)) k]
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr (hg.mono_set ?_)
    intro τ hτ
    exact lt_of_le_of_lt (hge k) hτ.1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun j : ℕ => 2 ^ j * T₀) (n := J) hint
  simp only [pow_zero, one_mul] at hsum
  rw [← hsum]
  calc ∑ k ∈ range J, ∫ τ in (2 ^ k * T₀)..(2 ^ (k + 1) * T₀), g τ
      ≤ ∑ k ∈ range J, b k := sum_le_sum fun k _ => by
        rw [pow_succ, mul_comm (2 ^ k : ℝ) 2, mul_assoc]; exact hblock k
    _ ≤ ∑' j, b j := hb.sum_le_tsum _ fun j _ => hb0 j

theorem continuous_norm_sq_dirichletPoly (N : ℕ) (x : ℕ → ℝ) :
    Continuous fun τ : ℝ => ‖dirichletPoly N x τ‖ ^ 2 := by
  unfold dirichletPoly
  fun_prop

/-! ### The aliasing bound -/

/-- The aliasing constant `209 C_φ e^{pA} B² (1/(1 − r) + r/(1 − r)²)`, `r = 2^{1−p}`. -/
def aliasConst (Cφ p A Bh : ℝ) : ℝ :=
  209 * Cφ * Real.exp (p * A) * Bh ^ 2 *
    (1 / (1 - (2 : ℝ) ^ (1 - p)) + (2 : ℝ) ^ (1 - p) / (1 - (2 : ℝ) ^ (1 - p)) ^ 2)

section Aliasing

variable {φ : ℝ → ℝ} {Cφ p : ℝ} {ν : ℝ → ℝ} {Aν : ℝ} {h : ℝ → ℝ} {A Bh : ℝ}

/-- The block weight: on `[U, 2U]` the transform and the symbol are at most
`C_φ (wU)^{−p} (A_ν + log(2 + 2U))`. -/
theorem weight_le_on_block (hCφ : 0 ≤ Cφ) (hp : 0 ≤ p)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hν : ∀ τ, |ν τ| ≤ Aν + Real.log (2 + |τ|)) {w U τ : ℝ} (hw : 0 < w) (hU : 0 < U)
    (hτ : τ ∈ Set.Icc U (2 * U)) (sgn : ℝ) (hsgn : |sgn| = 1) :
    ‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 * |ν (sgn * τ)| ≤
      Cφ * (w * U) ^ (-p) * (Aν + Real.log (2 + 2 * U)) := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hU hτ.1
  have habs : |sgn * τ| = τ := by rw [abs_mul, hsgn, one_mul, abs_of_pos hτ0]
  have h1 := hdecay (w * (sgn * τ))
  rw [show ((w * (sgn * τ) : ℝ) : ℂ) = (w : ℂ) * ((sgn * τ : ℝ) : ℂ) by push_cast; ring] at h1
  have hwτ : |w * (sgn * τ)| = w * τ := by rw [abs_mul, abs_of_pos hw, habs]
  rw [hwτ] at h1
  have h2 : (1 + w * τ) ^ (-p) ≤ (w * U) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hτ.1]) (by linarith)
  have h3 : |ν (sgn * τ)| ≤ Aν + Real.log (2 + 2 * U) := by
    refine (hν _).trans ?_
    rw [habs]
    gcongr
    exact hτ.2
  have hν0 : 0 ≤ |ν (sgn * τ)| := abs_nonneg _
  calc ‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 * |ν (sgn * τ)|
      ≤ (Cφ * (w * U) ^ (-p)) * (Aν + Real.log (2 + 2 * U)) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hCφ)) h3 hν0 (by positivity)
    _ = _ := by ring

/-- `(c 2^j e^{−A})^{−p} = c^{−p} (2^{−p})^j e^{pA}`. -/
theorem rpow_block_eq {c p A : ℝ} (hc : 0 < c) (j : ℕ) :
    (c * 2 ^ j * Real.exp (-A)) ^ (-p) = c ^ (-p) * ((2 : ℝ) ^ (-p)) ^ j * Real.exp (p * A) := by
  rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, Real.mul_rpow hc.le (by positivity),
    ← Real.exp_mul, show -A * -p = p * A by ring, ← Real.rpow_natCast (2 : ℝ) j,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-p)) j,
    ← Real.rpow_mul (by norm_num), mul_comm (j : ℝ) (-p)]

/-- The integrand of the aliasing tail at frequency `sgn · τ`. -/
def aliasIntegrand (φ ν h : ℝ → ℝ) (N : ℕ) (w sgn τ : ℝ) : ℝ :=
  ‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 *
    (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) * |ν (sgn * τ)|

/-- **One dyadic block** `[U, 2U]` of the aliasing tail. -/
theorem integral_aliasIntegrand_block_le (hCφ : 0 ≤ Cφ) (hp0 : 0 ≤ p)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hAν : 0 ≤ Aν) (hν : ∀ τ, |ν τ| ≤ Aν + Real.log (2 + |τ|))
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ Bh) {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) {U : ℝ} (hU1 : 1 ≤ U)
    (hint : IntervalIntegrable (aliasIntegrand φ ν h N w sgn) volume U (2 * U)) :
    ∫ τ in U..(2 * U), aliasIntegrand φ ν h N w sgn τ ≤
      Cφ * (w * U) ^ (-p) * (Aν + Real.log (2 + 2 * U)) *
        ((U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : 0 < U := by linarith
  have hUle : U ≤ 2 * U := by linarith
  have hsgn1 : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> simp
  set Wt : ℝ := Cφ * (w * U) ^ (-p) * (Aν + Real.log (2 + 2 * U)) with hWt
  have hWt0 : 0 ≤ Wt := by
    have : 0 ≤ Real.log (2 + 2 * U) := Real.log_nonneg (by linarith)
    positivity
  have hpt : ∀ τ ∈ Set.Icc U (2 * U), aliasIntegrand φ ν h N w sgn τ ≤
      Wt * (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) := by
    intro τ hτ
    have hw' := weight_le_on_block (φ := φ) hCφ hp0 hdecay hν hw0 hU0 hτ sgn hsgn1
    have hD0 : 0 ≤ ‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N := by
      positivity
    calc aliasIntegrand φ ν h N w sgn τ
        = (‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 * |ν (sgn * τ)|) *
          (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) := by
            unfold aliasIntegrand; ring
      _ ≤ Wt * (‖dirichletPoly N (horizonWeights h N) ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hw' hD0
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

/-- **The numerics of a block**: at `U = 2^j N e^{−A}`, `w = c/N`, the block bound is at most
`K₁ r^j (A_ν + 2 + log N + j)` with `K₁ = 209 C_φ e^{pA} B² c^{−p}` and `r = 2^{1−p}`. -/
theorem block_bound_le (hCφ : 0 ≤ Cφ) (hAν : 0 ≤ Aν) (hA : 0 ≤ A) {N : ℕ}
    (hNA : Real.exp A ≤ N) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    Cφ * (c / N * (2 ^ j * (N * Real.exp (-A)))) ^ (-p) *
        (Aν + Real.log (2 + 2 * (2 ^ j * (N * Real.exp (-A))))) *
        ((2 ^ j * (N * Real.exp (-A)) * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N) ≤
      209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) *
        (((2 : ℝ) ^ (1 - p)) ^ j * (Aν + 2 + Real.log N + j)) := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN0 : (0 : ℝ) < N := by linarith
  set T₀ : ℝ := N * Real.exp (-A) with hT₀
  have hT₀1 : 1 ≤ T₀ := by
    rw [hT₀, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos A), one_mul]; exact hNA
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  set U : ℝ := 2 ^ j * T₀ with hU
  have hU1 : 1 ≤ U := by rw [hU]; nlinarith
  have hwU : c / N * U = c * 2 ^ j * Real.exp (-A) := by
    rw [hU, hT₀]; field_simp
  have hlog : Real.log (2 + 2 * U) ≤ 2 + j + Real.log N := by
    have h4U : 2 + 2 * U ≤ 4 * U := by linarith
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hjl : (j : ℝ) * Real.log 2 ≤ j := by
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    calc Real.log (2 + 2 * U) ≤ Real.log (4 * U) := Real.log_le_log (by linarith) h4U
      _ = Real.log 4 + j * Real.log 2 + Real.log N + -A := by
          rw [hU, hT₀, Real.log_mul (by norm_num) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
          ring
      _ ≤ 2 + j + Real.log N := by linarith
  have hmass : (U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N ≤ 209 * Bh ^ 2 * 2 ^ j := by
    have hUN : U * Real.exp A = 2 ^ j * N := by
      rw [hU, hT₀, mul_assoc, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [div_le_iff₀ hN0]
    have hU' : U * (Bh ^ 2 * Real.exp A) = Bh ^ 2 * (2 ^ j * N) := by rw [← hUN]; ring
    have h208 : 208 * (N * Bh ^ 2) ≤ 208 * (2 ^ j * N * Bh ^ 2) := by
      have : (0 : ℝ) ≤ N * Bh ^ 2 := by positivity
      nlinarith
    rw [hU']
    have hring : Bh ^ 2 * (2 ^ j * N) + 208 * (2 ^ j * N * Bh ^ 2) = 209 * Bh ^ 2 * 2 ^ j * N := by
      ring
    linarith
  have hrj : ((2 : ℝ) ^ (-p)) ^ j * 2 ^ j = ((2 : ℝ) ^ (1 - p)) ^ j := by
    rw [← mul_pow, show (1 : ℝ) - p = -p + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have hlog0 : 0 ≤ Real.log (2 + 2 * U) := Real.log_nonneg (by linarith)
  rw [hwU, rpow_block_eq hc j]
  calc Cφ * (c ^ (-p) * ((2 : ℝ) ^ (-p)) ^ j * Real.exp (p * A)) * (Aν + Real.log (2 + 2 * U)) *
        ((U * (Bh ^ 2 * Real.exp A) + 208 * (N * Bh ^ 2)) / N)
      ≤ Cφ * (c ^ (-p) * ((2 : ℝ) ^ (-p)) ^ j * Real.exp (p * A)) * (Aν + (2 + j + Real.log N)) *
        (209 * Bh ^ 2 * 2 ^ j) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hmass
          (by positivity) (by positivity)
    _ = 209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) *
        ((((2 : ℝ) ^ (-p)) ^ j * 2 ^ j) * (Aν + 2 + Real.log N + j)) := by ring
    _ = _ := by rw [hrj]

/-- **The geometric sum of the blocks.** -/
theorem tsum_blocks_le (hp : 1 < p) (hCφ : 0 ≤ Cφ) {c : ℝ} (hc : 0 < c) {a : ℝ} (ha1 : 1 ≤ a) :
    Summable (fun j : ℕ => 209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) *
        (((2 : ℝ) ^ (1 - p)) ^ j * (a + j))) ∧
      ∑' j : ℕ, 209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) *
        (((2 : ℝ) ^ (1 - p)) ^ j * (a + j)) ≤ aliasConst Cφ p A Bh * a / c ^ p := by
  set r : ℝ := (2 : ℝ) ^ (1 - p) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K₁ : ℝ := 209 * Cφ * Real.exp (p * A) * Bh ^ 2 * c ^ (-p) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hsum1 : Summable fun j : ℕ => r ^ j := summable_geometric_of_lt_one hr0 hr1
  have hsum2 : Summable fun j : ℕ => (j : ℝ) * r ^ j := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hr0])
    simpa using this
  have hfun : (fun j : ℕ => K₁ * (r ^ j * (a + j))) =
      fun j : ℕ => K₁ * (a * r ^ j + (j : ℝ) * r ^ j) := funext fun j => by ring
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact ((hsum1.mul_left a).add hsum2).mul_left K₁
  have h1 := tsum_geometric_of_lt_one hr0 hr1
  have h2 := tsum_coe_mul_geometric_of_norm_lt_one (r := r) (by rwa [Real.norm_of_nonneg hr0])
  rw [hfun, tsum_mul_left, (hsum1.mul_left a).tsum_add hsum2, tsum_mul_left, h1, h2]
  have h1r : 0 < 1 - r := by linarith
  have hle : a * (1 - r)⁻¹ + r / (1 - r) ^ 2 ≤ a * (1 / (1 - r) + r / (1 - r) ^ 2) := by
    have : r / (1 - r) ^ 2 ≤ a * (r / (1 - r) ^ 2) := le_mul_of_one_le_left (by positivity) ha1
    rw [mul_add, one_div]
    linarith
  calc K₁ * (a * (1 - r)⁻¹ + r / (1 - r) ^ 2) ≤ K₁ * (a * (1 / (1 - r) + r / (1 - r) ^ 2)) :=
        mul_le_mul_of_nonneg_left hle hK₁0
    _ = aliasConst Cφ p A Bh * a / c ^ p := by
        rw [hK₁, aliasConst, Real.rpow_neg hc.le, div_eq_mul_inv]
        ring

/-- **The aliasing tail.** Above the grid, for either sign of the frequency,
`∫_{τ > N e^{−A}} ‖φ̂(wτ)‖² (|D_x(±τ)|²/N) |ν(±τ)| ≤ K_al (A_ν + 2 + log N)/c^p`, `w = c/N`. -/
theorem integral_aliasing_le (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hAν : 0 ≤ Aν) (hν : ∀ τ, |ν τ| ≤ Aν + Real.log (2 + |τ|))
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh)
    {N : ℕ} (hNA : Real.exp A ≤ N) {c : ℝ} (hc : 0 < c) {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1)
    (hint : MeasureTheory.IntegrableOn (aliasIntegrand φ ν h N (c / N) sgn)
      (Set.Ioi ((N : ℝ) * Real.exp (-A)))) :
    ∫ τ in Set.Ioi ((N : ℝ) * Real.exp (-A)), aliasIntegrand φ ν h N (c / N) sgn τ ≤
      aliasConst Cφ p A Bh * (Aν + 2 + Real.log N) / c ^ p := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hT₀1 : 1 ≤ (N : ℝ) * Real.exp (-A) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos A), one_mul]; exact hNA
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  obtain ⟨hsum, htsum⟩ := tsum_blocks_le (A := A) (Bh := Bh) hp hCφ hc
    (a := Aν + 2 + Real.log N) (by linarith)
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
  refine (integral_aliasIntegrand_block_le hCφ (by linarith) hdecay hAν hν hsupp hB hN
    (div_pos hc hN0) hsgn hU1 hintb).trans ?_
  have := block_bound_le (p := p) (Bh := Bh) hCφ hAν hA hNA hc j
  convert this using 2

end Aliasing


end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
