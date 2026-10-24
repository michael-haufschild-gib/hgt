import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheNearRadicalOfZetaIsFiniteDimensional
import GaloisForLFunctions.RHTower.SharpWeilNearRadicalCount
import GaloisForLFunctions.RHTower.WeilNearRadicalDimension
import GaloisForLFunctions.RHTower.RiemannKernelTruncationEnergyOrder

/-!
# The Landau–Widom Near-Radical Law and the Shannon–Riemann–von Mangoldt Surplus

This module resolves Open Problem 2 of `ArithmeticCastelnuovoSeveri`: the two-sided Landau–Widom
law for the near-radical dimension at aperture `L`, the sharp Bessel–Shannon concentration bound,
and the two-sided rate `−log μ(L) ≍ 2π² N(T*)/log N(T*)` at the Landau–Nyquist height
`T*(L) = 2πe^{2L}`.

## Main results

1. **Two-sided Riemann–von Mangoldt cumulative zero count (`zeroCount_lower`,
   `zeroCount_twoSided`).** Complementing `RHTower.zeroCount_upper`, dyadic summation of the lower
   half of `Zeta23.RvM.rvM_main` proves `zeroCountMain T − C log²T ≤ N(0, T)` and hence
   `|N(0, T) − zeroCountMain T| ≤ C log²T` for all `T ≥ T₁`.

2. **Exact Shannon–RvM variational identity and uniform `(2 + η)e^{2L}` upper bound
   (`shannonZeroSurplus_eq_landau_deficit`, `shannonZeroSurplus_le_two_mul_exp`,
   `shannonZeroSurplus_eq_two_mul_exp_iff`, `eventually_shannon_sub_zetaZeroCount_le`).**
   The degrees-of-freedom surplus `shannonZeroSurplus L T = 2TL/π − 2 zeroCountMain T` of the
   time-frequency box `[−L, L] × [−T, T]` after subtracting the zeros in `[−T, T]` satisfies the
   exact identity
   `shannonZeroSurplus L T = 2e^{2L} − 2e^{2L}(u log u − u + 1)` with `u = T/(2πe^{2L})`.
   Since `u log u − u + 1 ≥ 0` with equality iff `u = 1`, `shannonZeroSurplus L T ≤ 2e^{2L}` for
   all `T > 0` with equality iff `T = 2πe^{2L}`, and `shannonZeroSurplus L T < 0` for
   `T > 2πe^{2L+1}`. Combining with `zeroCount_lower` gives the uniform upper bound
   `2TL/π − 2N(0, T) ≤ (2 + η)e^{2L}` for all large `L` and *every* `T ≥ 0`.

3. **Sharp Bessel–Shannon concentration bound and two-sided `(2 ∓ η)e^{2L}` Landau–Widom law
   (`finrank_mul_le_four_mul_of_concentrated`, `zeta_near_radical_finrank_le_shannon`,
   `hodgeDefectAt_zeta_le_shannon`, `finrank_mul_le_sub_of_concentrated_ker`,
   `zeta_landau_widom_two_sided_dimension_law`).**
   Using a `δ`-transition cut-off character on `[−(a + δ), a + δ]` and letting `δ → 0⁺`, any
   subspace `V` of aperture-`a` tests carrying band mass `≥ κ‖f‖²` in `[−T, T]` obeys
   `dim V · κ ≤ 4Ta`. On the near radical (`Re W_ζ(f, f) ≤ ε‖f‖²`), `κ = π` gives the unconditional
   bound `dim V ≤ 4L T_ε(L)/π = 2 · Shannon(L, T_ε(L))` (removing the `T_ε^{3/2}(L+1)^{3/2}`
   Lipschitz-grid overhead of `zeta_near_radical_finrank_le`) and sharpens `hodgeDefectAt_zeta_le`
   to `1 + 4aT(a)/π`. For subspaces `κ`-concentrated along the kernel of a rank-`R` zero-evaluation
   map on a bandwidth-`T` space `W`, dual Bessel inequalities yield
   `dim V · κ ≤ dim W − R`, giving `(2 − η)e^{2L} ≤ dim V_−` and `dim V_+ ≤ (2 + η)e^{2L}` across
   all bandwidths `T ≥ 0`.

4. **Two-sided Landau–Widom rate `−log μ(L) ≍ 2π² N(T*)/log N(T*)` and critical-line coercivity
   (`zeroCountMain_edgeRate_div_log_bounds`, `eventually_zetaZeroCount_edgeRate_div_log_bounds`,
   `exists_twoSided_truncKernel_log_energy_landauRate`, `sum_norm_sq_paperFT_le_re_W_of_criticalLine`).**
   At the Landau height `T* = 2πe^{2L}`, `N(T*)/log N(T*) ≍ e^{2L}` (`1/2 · e^{2L} ≤ F(T*)/log F(T*) ≤ e^{2L}`
   for all `L ≥ 1`, and `1/3 · e^{2L} ≤ N(0, T*)/log N(0, T*) ≤ 2e^{2L}` for large `L`), so the
   canonical near-null Weil energy `W_L = Re W_ζ(Φχ_L, Φχ_L)` and its Rayleigh quotient obey the
   unconditional two-sided law
   `(1/(4π)) · (2π² N(0, T*)/log N(0, T*)) ≤ −log W_L ≤ (9/(2π)) · (2π² N(0, T*)/log N(0, T*))`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate InnerProductSpace Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Two-sided Riemann–von Mangoldt cumulative zero count -/

/-- Upper bound for `zeroCountMain t` on `[0, B]`. -/
theorem zeroCountMain_le_of_le {t B : ℝ} (ht0 : 0 ≤ t) (htB : t ≤ B) (hB : 3 ≤ B) :
    RHTower.zeroCountMain t ≤ B * Real.log B := by
  unfold RHTower.zeroCountMain
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simp only [zero_div, zero_mul]
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  · have ht2pi : t / (2 * π) ≤ B := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hlog : Real.log (t / (2 * π)) - 1 ≤ Real.log B := by
      have h1 : Real.log (t / (2 * π)) ≤ Real.log B :=
        Real.log_le_log (by positivity) ht2pi
      linarith
    rcases le_or_gt (Real.log (t / (2 * π)) - 1) 0 with hneg | hpos
    · have : t / (2 * π) * (Real.log (t / (2 * π)) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
      exact this.trans (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
    · exact mul_le_mul ht2pi hlog hpos.le (by linarith)

/-- Dyadic lower induction for the cumulative zero count:
`zeroCountMain T − k C log T − 2 T₀ log(2 T₀) ≤ N(0, T)` for `T₀ ≤ T ≤ 2^{k+1} T₀`. -/
theorem zeroCount_dyadic_lower {C T₀ : ℝ} (hC : 0 ≤ C) (hT₀ : 3 ≤ T₀)
    (hrvm : ∀ T : ℝ, T₀ ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * π) * ell1 T| ≤ C * Real.log T) :
    ∀ k : ℕ, ∀ T : ℝ, T₀ ≤ T → T ≤ 2 ^ (k + 1) * T₀ →
      RHTower.zeroCountMain T - k * C * Real.log T - 2 * T₀ * Real.log (2 * T₀) ≤
        (zetaZeroConfig.N 0 T : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro T hT hT2
    have hF : RHTower.zeroCountMain T ≤ (2 * T₀) * Real.log (2 * T₀) :=
      zeroCountMain_le_of_le (by linarith) (by simpa using hT2) (by linarith)
    have hN : (0 : ℝ) ≤ zetaZeroConfig.N 0 T := Nat.cast_nonneg _
    simp only [CharP.cast_eq_zero, zero_mul, sub_zero]
    linarith
  | succ k ih =>
    intro T hT hT2
    have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    by_cases hsmall : T ≤ 2 ^ (k + 1) * T₀
    · have := ih T hT hsmall
      have hk : (k : ℝ) * C * Real.log T ≤ ((k + 1 : ℕ) : ℝ) * C * Real.log T := by
        push_cast; nlinarith
      linarith
    · push Not at hsmall
      set T' := T / 2 with hT'
      have hpow : 2 * T₀ ≤ (2 : ℝ) ^ (k + 1) * T₀ := by
        have : (2 : ℝ) ≤ 2 ^ (k + 1) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      have hT'lo : T₀ ≤ T' := by rw [hT']; linarith
      have hT'hi : T' ≤ 2 ^ (k + 1) * T₀ := by
        have e : (2 : ℝ) ^ (k + 1 + 1) * T₀ = 2 * (2 ^ (k + 1) * T₀) := by ring
        rw [e] at hT2
        rw [hT']; linarith
      have hih := ih T' hT'lo hT'hi
      have h2T : 2 * T' = T := by rw [hT']; ring
      have hsplit : zetaZeroConfig.N 0 T = zetaZeroConfig.N 0 T' + zetaZeroConfig.N T' T :=
        Assembly.N_add zetaZeroConfig (by linarith) (by linarith)
      have hw := hrvm T' hT'lo
      rw [h2T] at hw
      have hw' := (abs_le.mp hw).1
      have htel := RHTower.zeroCountMain_two_mul_sub (t := T') (by linarith)
      rw [h2T] at htel
      have hlogT' : Real.log T' ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
      have hk1 : (k : ℝ) * C * Real.log T' ≤ (k : ℝ) * C * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT' (by positivity)
      have hk2 : C * Real.log T' ≤ C * Real.log T := mul_le_mul_of_nonneg_left hlogT' hC
      have hcast : (zetaZeroConfig.N 0 T : ℝ) =
          (zetaZeroConfig.N 0 T' : ℝ) + (zetaZeroConfig.N T' T : ℝ) := by
        rw [hsplit]; push_cast; ring
      rw [hcast]
      push_cast
      linarith

/-- **Lower bound for the cumulative zero count of `ζ`.**
`zeroCountMain T − C log²T ≤ N(0, T)` for `T ≥ T₁`. -/
theorem zeroCount_lower : ∃ C T₁ : ℝ, 0 ≤ C ∧ 3 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
    RHTower.zeroCountMain T - C * Real.log T ^ 2 ≤ (zetaZeroConfig.N 0 T : ℝ) := by
  obtain ⟨C₀, T₀, hrvm⟩ := RvM.rvM_main gammaFacts
  set C := max C₀ 0 with hCdef
  set T₁ := max T₀ 3 with hT₁def
  have hC : 0 ≤ C := le_max_right _ _
  have hT₁3 : 3 ≤ T₁ := le_max_right _ _
  have hrvm' : ∀ T : ℝ, T₁ ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * π) * ell1 T| ≤ C * Real.log T := by
    intro T hT
    refine (hrvm T (le_trans (le_max_left _ _) hT)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith))
  set K : ℝ := 2 * T₁ * Real.log (2 * T₁) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  refine ⟨2 * C + K, T₁, by positivity, hT₁3, fun T hT => ?_⟩
  have hlog1 : 1 ≤ Real.log T := by
    have : Real.exp 1 ≤ T := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) this
  set x := T / T₁ with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by linarith)]; linarith
  set k := ⌊Real.logb 2 x⌋₊ with hk
  have hkx : Real.logb 2 x < k + 1 := Nat.lt_floor_add_one _
  have hxlt : x < 2 ^ (k + 1) := by
    have h1 : x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num)
      (by linarith)).symm
    have h2 : (2 : ℝ) ^ (Real.logb 2 x) < (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      push_cast; exact hkx
    rw [Real.rpow_natCast] at h2
    linarith
  have hTle : T ≤ 2 ^ (k + 1) * T₁ := by
    have := hxlt.le
    rw [hx, div_le_iff₀ (by linarith)] at this
    linarith
  have hmain := zeroCount_dyadic_lower hC hT₁3 hrvm' k T hT hTle
  have hkle : (k : ℝ) ≤ 2 * Real.log T := by
    have h1 : (k : ℝ) ≤ Real.logb 2 x := Nat.floor_le (Real.logb_nonneg (by norm_num) hx1)
    have h2 : Real.logb 2 x ≤ Real.logb 2 T := by
      apply Real.logb_le_logb_of_le (by norm_num) (by linarith)
      rw [hx, div_le_iff₀ (by linarith)]; nlinarith
    have h3 : Real.logb 2 T ≤ 2 * Real.log T := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have : 1 / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith
    linarith
  have hKlog : K ≤ K * Real.log T ^ 2 := by
    have : 1 ≤ Real.log T ^ 2 := by nlinarith
    nlinarith
  have hkC : (k : ℝ) * C * Real.log T ≤ 2 * C * Real.log T ^ 2 := by
    have := mul_le_mul_of_nonneg_right hkle (mul_nonneg hC (by linarith : (0 : ℝ) ≤ Real.log T))
    nlinarith
  rw [← hK] at hmain
  nlinarith

/-- **Two-sided cumulative zero-count law for `ζ`.**
`|N(0, T) − zeroCountMain T| ≤ C log²T` for all `T ≥ T₁`. -/
theorem zeroCount_twoSided : ∃ C T₁ : ℝ, 0 ≤ C ∧ 3 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
    |(zetaZeroConfig.N 0 T : ℝ) - RHTower.zeroCountMain T| ≤ C * Real.log T ^ 2 := by
  obtain ⟨C₁, T₁, hC₁, hT₁, hup⟩ := RHTower.zeroCount_upper
  obtain ⟨C₂, T₂, hC₂, hT₂, hlo⟩ := zeroCount_lower
  refine ⟨max C₁ C₂, max T₁ T₂, le_trans hC₁ (le_max_left _ _),
    le_trans hT₁ (le_max_left _ _), fun T hT => ?_⟩
  have h1 := hup T (le_trans (le_max_left _ _) hT)
  have h2 := hlo T (le_trans (le_max_right _ _) hT)
  have hsq : 0 ≤ Real.log T ^ 2 := sq_nonneg _
  have hc1 : C₁ * Real.log T ^ 2 ≤ max C₁ C₂ * Real.log T ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hsq
  have hc2 : C₂ * Real.log T ^ 2 ≤ max C₁ C₂ * Real.log T ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hsq
  rw [abs_le]
  constructor <;> linarith

/-! ### 2. The Shannon–RvM variational law and the `(2 + η)e^{2L}` upper bound -/

/-- The Shannon–Riemann–von Mangoldt surplus at aperture `L` and bandwidth `T`:
the Shannon number `2TL/π` of `[−L, L] × [−T, T]` minus the main term `2 zeroCountMain T`
of the number of zeros of `ζ` in `[−T, T]`. -/
def shannonZeroSurplus (L T : ℝ) : ℝ :=
  2 * T * L / π - 2 * RHTower.zeroCountMain T

/-- Algebraic form of `shannonZeroSurplus`:
`shannonZeroSurplus L T = (T/π)(2L + 1 − log(T/2π))`. -/
theorem shannonZeroSurplus_eq (L T : ℝ) :
    shannonZeroSurplus L T = T / π * (2 * L + 1 - Real.log (T / (2 * π))) := by
  unfold shannonZeroSurplus RHTower.zeroCountMain
  ring

/-- **Exact variational identity relative to the Landau height `edgeRate L = 2πe^{2L}`.**
With `u = T / edgeRate L`,
`shannonZeroSurplus L T = 2e^{2L} · u(1 − log u) = 2e^{2L} − 2e^{2L}(u log u − u + 1)`. -/
theorem shannonZeroSurplus_eq_landau_deficit (L : ℝ) {T : ℝ} (hT : 0 < T) :
    shannonZeroSurplus L T =
      2 * Real.exp (2 * L) -
        2 * Real.exp (2 * L) *
          ((T / RHTower.edgeRate L) * Real.log (T / RHTower.edgeRate L) -
            T / RHTower.edgeRate L + 1) := by
  rw [shannonZeroSurplus_eq]
  have hpi := Real.pi_pos
  have hE := Real.exp_pos (2 * L)
  have hdiv : T / (2 * π) = (T / RHTower.edgeRate L) * Real.exp (2 * L) := by
    unfold RHTower.edgeRate
    field_simp
  have hu : 0 < T / RHTower.edgeRate L := div_pos hT (RHTower.edgeRate_pos L)
  have hlog : Real.log (T / (2 * π)) = Real.log (T / RHTower.edgeRate L) + 2 * L := by
    rw [hdiv, Real.log_mul hu.ne' hE.ne', Real.log_exp]
  rw [hlog]
  have hTpi : T / π = 2 * Real.exp (2 * L) * (T / RHTower.edgeRate L) := by
    unfold RHTower.edgeRate
    field_simp
  rw [hTpi]
  ring

/-- At the Landau–Nyquist height `edgeRate L = 2πe^{2L}`, the Shannon–RvM surplus is
exactly `2e^{2L}` (the Connes–Consani constant `2`). -/
theorem shannonZeroSurplus_edgeRate (L : ℝ) :
    shannonZeroSurplus L (RHTower.edgeRate L) = 2 * Real.exp (2 * L) := by
  rw [shannonZeroSurplus_eq_landau_deficit L (RHTower.edgeRate_pos L),
    div_self (RHTower.edgeRate_pos L).ne', Real.log_one]
  ring

/-- Elementary convexity inequality `0 ≤ u log u − u + 1` for `u > 0`. -/
theorem mul_log_sub_add_one_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ u * Real.log u - u + 1 := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
  rw [Real.log_inv] at h
  have hmul := mul_le_mul_of_nonneg_left h hu.le
  rw [mul_sub, mul_inv_cancel₀ hu.ne', mul_one, mul_neg] at hmul
  linarith

/-- Strict convexity `0 < u log u − u + 1` for `u > 0`, `u ≠ 1`. -/
theorem mul_log_sub_add_one_pos_of_ne_one {u : ℝ} (hu : 0 < u) (hne : u ≠ 1) :
    0 < u * Real.log u - u + 1 := by
  have hne' : u⁻¹ ≠ 1 := fun h => hne (inv_eq_one.mp h)
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hu) hne'
  rw [Real.log_inv] at h
  have hmul := mul_lt_mul_of_pos_left h hu
  rw [mul_sub, mul_inv_cancel₀ hu.ne', mul_one, mul_neg] at hmul
  linarith

/-- **Global maximum of the Shannon–RvM surplus.** For every aperture `L` and every bandwidth
`T > 0`, `shannonZeroSurplus L T ≤ 2e^{2L}`. -/
theorem shannonZeroSurplus_le_two_mul_exp (L : ℝ) {T : ℝ} (hT : 0 < T) :
    shannonZeroSurplus L T ≤ 2 * Real.exp (2 * L) := by
  rw [shannonZeroSurplus_eq_landau_deficit L hT]
  have hu : 0 < T / RHTower.edgeRate L := div_pos hT (RHTower.edgeRate_pos L)
  have hconv := mul_log_sub_add_one_nonneg hu
  have hE := Real.exp_pos (2 * L)
  nlinarith

/-- **Uniqueness of the Landau height.** For `T > 0`, `shannonZeroSurplus L T = 2e^{2L}`
if and only if `T = edgeRate L = 2πe^{2L}`. -/
theorem shannonZeroSurplus_eq_two_mul_exp_iff (L : ℝ) {T : ℝ} (hT : 0 < T) :
    shannonZeroSurplus L T = 2 * Real.exp (2 * L) ↔ T = RHTower.edgeRate L := by
  constructor
  · intro heq
    by_contra hne
    have hu : 0 < T / RHTower.edgeRate L := div_pos hT (RHTower.edgeRate_pos L)
    have hune : T / RHTower.edgeRate L ≠ 1 :=
      div_ne_one_of_ne hne
    have hpos := mul_log_sub_add_one_pos_of_ne_one hu hune
    have hE := Real.exp_pos (2 * L)
    have hlt : shannonZeroSurplus L T < 2 * Real.exp (2 * L) := by
      rw [shannonZeroSurplus_eq_landau_deficit L hT]
      nlinarith
    linarith
  · rintro rfl
    exact shannonZeroSurplus_edgeRate L

/-- Above `e · edgeRate L = 2πe^{2L + 1}`, the zero count strictly exceeds the Shannon number
(`shannonZeroSurplus L T < 0`). -/
theorem shannonZeroSurplus_neg_of_gt (L : ℝ) {T : ℝ}
    (hT : Real.exp 1 * RHTower.edgeRate L < T) :
    shannonZeroSurplus L T < 0 := by
  have hY := RHTower.edgeRate_pos L
  have hTpos : 0 < T := lt_trans (by positivity) hT
  rw [shannonZeroSurplus_eq]
  have hdiv : Real.exp (2 * L + 1) < T / (2 * π) := by
    unfold RHTower.edgeRate at hT
    rw [Real.exp_add]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hlog : 2 * L + 1 < Real.log (T / (2 * π)) := by
    rw [← Real.log_exp (2 * L + 1)]
    exact Real.log_lt_log (Real.exp_pos _) hdiv
  have hTpi : 0 < T / π := div_pos hTpos Real.pi_pos
  nlinarith

/-- Elementary bound `Real.log T ^ 2 ≤ 16 * T` for `T ≥ 1`. -/
theorem log_sq_le_sixteen_mul {T : ℝ} (hT : 1 ≤ T) : Real.log T ^ 2 ≤ 16 * T := by
  have hT0 : 0 < T := by linarith
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have h1 : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 := Real.log_le_sub_one_of_pos hsqrt
  have h2 : Real.log T = 2 * Real.log (Real.sqrt T) := by
    rw [Real.log_sqrt hT0.le]; ring
  have h3 : Real.log T ≤ 2 * Real.sqrt T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  calc Real.log T ^ 2 ≤ (2 * Real.sqrt T) ^ 2 := pow_le_pow_left₀ hlog0 h3 2
    _ = 4 * T := by rw [mul_pow, Real.sq_sqrt hT0.le]; ring
    _ ≤ 16 * T := by linarith

/-- **Uniform `(2 + η)e^{2L}` upper bound for the Shannon–zero surplus of `ζ`.**
Unconditionally, for every `η > 0`, for all sufficiently large `L` and *every* bandwidth `T ≥ 0`
(uniformly in `T`, with no upper bound on `T`),
`2TL/π − 2 N(0, T) ≤ (2 + η)e^{2L}`. -/
theorem eventually_shannon_sub_zetaZeroCount_le :
    ∀ η : ℝ, 0 < η → ∀ᶠ L : ℝ in atTop, ∀ T : ℝ, 0 ≤ T →
      2 * T * L / π - 2 * (zetaZeroConfig.N 0 T : ℝ) ≤ (2 + η) * Real.exp (2 * L) := by
  intro η hη
  obtain ⟨C, T₁, hC0, hT₁, hlow⟩ := zeroCount_lower
  have hpi := Real.pi_pos
  have he1 := RHTower.eventually_mul_pow_four_le_exp (K := η) hη (2 * C * 36)
  have he2 := RHTower.eventually_mul_pow_four_le_exp (K := 2) two_pos T₁
  filter_upwards [eventually_ge_atTop (max 2 (32 * π * C)), he1, he2] with L hLmax hC_exp hT₁_exp
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hLmax
  have hL_C : 32 * π * C ≤ L := le_trans (le_max_right _ _) hLmax
  have hE := Real.exp_pos (2 * L)
  intro T hT0
  by_cases hT_small : T < T₁
  · -- Small `T < T₁`: `2TL/π − 2N(0, T) ≤ 2T₁L/π ≤ 2e^{2L} ≤ (2 + η)e^{2L}`
    have hN0 : (0 : ℝ) ≤ zetaZeroConfig.N 0 T := Nat.cast_nonneg _
    have hTL : 2 * T * L / π ≤ 2 * T₁ * L / π := by
      apply div_le_div_of_nonneg_right _ hpi.le
      nlinarith
    have hpow : L ≤ (1 + L) ^ 4 := by
      have : (1 + L) ^ 1 ≤ (1 + L) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have hT₁L : T₁ * L ≤ 2 * Real.exp (2 * L) :=
      (mul_le_mul_of_nonneg_left hpow (by linarith)).trans hT₁_exp
    have hpi2 : 2 * T₁ * L / π ≤ 2 * Real.exp (2 * L) := by
      rw [div_le_iff₀ hpi]
      nlinarith [Real.pi_gt_three]
    nlinarith
  · push Not at hT_small
    have hTpos : 0 < T := by linarith
    have hlo := hlow T hT_small
    have hsur : 2 * T * L / π - 2 * (zetaZeroConfig.N 0 T : ℝ) ≤
        shannonZeroSurplus L T + 2 * C * Real.log T ^ 2 := by
      unfold shannonZeroSurplus
      linarith
    by_cases hT_mid : T ≤ 2 * π * Real.exp (4 * L)
    · -- Moderate/Landau regime `T₁ ≤ T ≤ 2πe^{4L}`: `shannonZeroSurplus ≤ 2e^{2L}` and
      -- `2C log²T ≤ 2C(6L)² ≤ ηe^{2L}`
      have hmax := shannonZeroSurplus_le_two_mul_exp L hTpos
      have hlogT : Real.log T ≤ 6 * L := by
        have h1 : Real.log T ≤ Real.log (2 * π * Real.exp (4 * L)) :=
          Real.log_le_log hTpos hT_mid
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
        have h2 := RHTower.log_two_pi_lt_two
        linarith
      have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      have hlog2 : Real.log T ^ 2 ≤ 36 * (1 + L) ^ 4 := by
        calc Real.log T ^ 2 ≤ (6 * L) ^ 2 := pow_le_pow_left₀ hlog0 hlogT 2
          _ = 36 * L ^ 2 := by ring
          _ ≤ 36 * (1 + L) ^ 4 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            nlinarith
      have hCerr : 2 * C * Real.log T ^ 2 ≤ η * Real.exp (2 * L) := by
        calc 2 * C * Real.log T ^ 2 ≤ 2 * C * (36 * (1 + L) ^ 4) :=
              mul_le_mul_of_nonneg_left hlog2 (by positivity)
          _ = 2 * C * 36 * (1 + L) ^ 4 := by ring
          _ ≤ η * Real.exp (2 * L) := hC_exp
      linarith
    · -- Ultra-high frequency regime `T > 2πe^{4L}`: `log(T/2π) > 4L ≥ 2L + 1 + 16πC`, so
      -- `shannonZeroSurplus L T + 2C log²T ≤ -(T/π)(2L - 1) + 32CT ≤ 0`
      push Not at hT_mid
      rw [shannonZeroSurplus_eq] at hsur
      have hlog : 4 * L < Real.log (T / (2 * π)) := by
        rw [← Real.log_exp (4 * L)]
        exact Real.log_lt_log (Real.exp_pos _) ((lt_div_iff₀ (by positivity)).mpr (by linarith))
      have hsur_neg : T / π * (2 * L + 1 - Real.log (T / (2 * π))) ≤ -(T / π * L) := by
        have hTpi : 0 ≤ T / π := by positivity
        nlinarith
      have hlog16 : 2 * C * Real.log T ^ 2 ≤ 32 * C * T := by
        have := log_sq_le_sixteen_mul (by linarith : 1 ≤ T)
        nlinarith
      have hcancel : -(T / π * L) + 32 * C * T ≤ 0 := by
        have : 32 * C * T ≤ T / π * L := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
          nlinarith
        linarith
      have hpos_rhs : 0 ≤ (2 + η) * Real.exp (2 * L) := by positivity
      linarith

/-! ### 3. Sharp Bessel–Shannon concentration bound and the two-sided Landau–Widom law -/

/-- A continuous cut-off equal to `1` on `[−a, a]`, with values in `[0, 1]`, supported in
`[−(a + δ), a + δ]` for `δ > 0`. -/
def plateauDelta (a δ u : ℝ) : ℝ := max 0 (min 1 ((a + δ - |u|) / δ))

theorem continuous_plateauDelta (a δ : ℝ) : Continuous (plateauDelta a δ) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.sub continuous_abs).div_const δ))

theorem plateauDelta_eq_one {a δ u : ℝ} (hδ : 0 < δ) (hu : u ∈ Icc (-a) a) :
    plateauDelta a δ u = 1 := by
  have h : |u| ≤ a := abs_le.mpr hu
  have h1 : 1 ≤ (a + δ - |u|) / δ := by rw [le_div_iff₀ hδ]; linarith
  unfold plateauDelta
  rw [min_eq_left h1, max_eq_right zero_le_one]

theorem plateauDelta_nonneg (a δ u : ℝ) : 0 ≤ plateauDelta a δ u := le_max_left _ _

theorem plateauDelta_le_one (a δ u : ℝ) : plateauDelta a δ u ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem plateauDelta_eq_zero {a δ u : ℝ} (hδ : 0 < δ) (hu : u ∉ Icc (-(a + δ)) (a + δ)) :
    plateauDelta a δ u = 0 := by
  have h : a + δ < |u| := by
    by_contra h
    exact hu (abs_le.mp (not_lt.mp h))
  have hneg : (a + δ - |u|) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  unfold plateauDelta
  rw [max_eq_left (min_le_of_right_le hneg)]

theorem hasCompactSupport_plateauDelta (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (plateauDelta a δ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => plateauDelta_eq_zero hδ hu

/-- The `δ`-cut-off character `u ↦ plateauDelta a δ u · e^{iτu}`. -/
def cutCharDelta (a δ τ : ℝ) : ℝ → ℂ := fun u => (plateauDelta a δ u : ℂ) * cexp (I * τ * u)

theorem continuous_cutCharDelta (a δ τ : ℝ) : Continuous (cutCharDelta a δ τ) :=
  (continuous_ofReal.comp (continuous_plateauDelta a δ)).mul (by fun_prop)

theorem hasCompactSupport_cutCharDelta (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (τ : ℝ) :
    HasCompactSupport (cutCharDelta a δ τ) :=
  (hasCompactSupport_plateauDelta a hδ).comp_left Complex.ofReal_zero |>.mul_right

/-- The `δ`-cut-off character in `L²(ℝ)`. -/
def cutCharDeltaL2 (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (τ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two (continuous_cutCharDelta a δ τ)
    (hasCompactSupport_cutCharDelta a hδ τ)).toLp (cutCharDelta a δ τ)

/-- The `L²` norm squared of `cutCharDeltaL2 a hδ τ` is at most `2a + 2δ`. -/
theorem norm_cutCharDeltaL2_sq_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (τ : ℝ) :
    ‖cutCharDeltaL2 a hδ τ‖ ^ 2 ≤ 2 * a + 2 * δ := by
  rw [cutCharDeltaL2, norm_toLp_sq]
  have hpt : ∀ u, ‖cutCharDelta a δ τ u‖ ^ 2 ≤
      (Icc (-(a + δ)) (a + δ)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    have hn : ‖cutCharDelta a δ τ u‖ = plateauDelta a δ u := by
      rw [cutCharDelta, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (plateauDelta_nonneg a δ u),
        show I * (τ : ℂ) * (u : ℂ) = ((τ * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [hn]
    by_cases hu : u ∈ Icc (-(a + δ)) (a + δ)
    · rw [indicator_of_mem hu]
      have h0 := plateauDelta_nonneg a δ u
      have h1 := plateauDelta_le_one a δ u
      nlinarith
    · rw [indicator_of_notMem hu, plateauDelta_eq_zero hδ hu]
      norm_num
  have hint2 : Integrable ((Icc (-(a + δ)) (a + δ)).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  have hint1 : Integrable fun u => ‖cutCharDelta a δ τ u‖ ^ 2 :=
    hint2.mono' ((continuous_cutCharDelta a δ τ).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hpt u)
  calc ∫ u, ‖cutCharDelta a δ τ u‖ ^ 2
      ≤ ∫ u, (Icc (-(a + δ)) (a + δ)).indicator (fun _ => (1 : ℝ)) u :=
        integral_mono hint1 hint2 hpt
    _ = 2 * a + 2 * δ := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
        Real.volume_real_Icc_of_le (by linarith)]
      ring

theorem inner_comboL2_cutCharDeltaL2 {n : ℕ} {a δ : ℝ} (hδ : 0 < δ) (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a) (x : Fin n → ℂ) (τ : ℝ) :
    ⟪comboL2 f hf hfc x, cutCharDeltaL2 a hδ τ⟫_ℂ = paperFT (∑ i, conj (x i) • f i) τ := by
  rw [comboL2_apply, cutCharDeltaL2, inner_toLp, paperFT]
  congr 1
  funext u
  rw [conj_conjCombo, cutCharDelta]
  by_cases hu : u ∈ Icc (-a) a
  · rw [plateauDelta_eq_one hδ hu]
    push_cast
    ring
  · have h0 : (∑ i, conj (x i) • f i) u = 0 := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hu (hfs i h)
      rw [this, mul_zero]
    rw [h0, zero_mul, zero_mul]

/-- **Bessel count with non-strict inequality.** Let `Ψ` map a finite-dimensional space `U`
into an inner product space and let `φ τ` have square norm at most `c`. If `κ > 0` and every
nonzero `x ∈ U` has `Ψ x ≠ 0` and `κ‖Ψ x‖² ≤ ∫_{−T}^{T} |⟪Ψ x, φ τ⟫|²`, then
`dim U · κ ≤ 2Tc`. -/
theorem finrank_mul_le_of_concentrated_le {M E : Type*} [AddCommGroup M] [Module ℂ M]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (U : Submodule ℂ M) [FiniteDimensional ℂ U]
    (Ψ : M →ₗ[ℂ] E) (φ : ℝ → E) {κ T c : ℝ} (hT : 0 ≤ T) (hφ : ∀ τ, ‖φ τ‖ ^ 2 ≤ c)
    (hcont : ∀ x ∈ U, Continuous fun τ => ⟪Ψ x, φ τ⟫_ℂ)
    (hinjU : ∀ x ∈ U, Ψ x = 0 → x = 0)
    (hconc : ∀ x ∈ U, κ * ‖Ψ x‖ ^ 2 ≤ ∫ τ in (-T)..T, ‖⟪Ψ x, φ τ⟫_ℂ‖ ^ 2) :
    (Module.finrank ℂ U : ℝ) * κ ≤ 2 * T * c := by
  set Ψ' : U →ₗ[ℂ] E := Ψ.domRestrict U with hΨ'
  have hinj : Function.Injective Ψ' := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    exact Subtype.ext (hinjU y y.2 hy)
  set V := LinearMap.range Ψ'
  have hrank : Module.finrank ℂ V = Module.finrank ℂ U := LinearMap.finrank_range_of_inj hinj
  set b := stdOrthonormalBasis ℂ V
  have hon : Orthonormal ℂ (fun j => (b j : E)) := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hpre : ∀ j, ∃ y ∈ U, Ψ y = (b j : E) := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (b j).2
    exact ⟨y, y.2, hy⟩
  have hcj : ∀ j, Continuous fun τ => ⟪(b j : E), φ τ⟫_ℂ := by
    intro j
    obtain ⟨y, hyU, hy⟩ := hpre j
    rw [← hy]
    exact hcont y hyU
  have hlow : ∀ j, κ ≤ ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 := by
    intro j
    obtain ⟨y, hyU, hy⟩ := hpre j
    have h := hconc y hyU
    rwa [hy, hon.1 j, one_pow, mul_one] at h
  have hii : ∀ j, IntervalIntegrable (fun τ => ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2) volume (-T) T :=
    fun j => ((hcj j).norm.pow 2).intervalIntegrable _ _
  have hsum : ∑ j, ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 ≤ 2 * T * c := by
    rw [← intervalIntegral.integral_finsetSum fun j _ => hii j]
    calc ∫ τ in (-T)..T, ∑ j, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2
        ≤ ∫ _τ in (-T)..T, c := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((continuous_finsetSum _ fun j _ => (hcj j).norm.pow 2).intervalIntegrable _ _)
            intervalIntegrable_const fun τ _ => ?_
          exact (hon.sum_inner_products_le (φ τ) (s := Finset.univ)).trans (hφ τ)
      _ = 2 * T * c := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hκ : (Module.finrank ℂ V : ℝ) * κ ≤ ∑ j, ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 := by
    have h : ∑ _j : Fin (Module.finrank ℂ V), κ ≤
        ∑ j, ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => hlow j
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  rw [← hrank]
  linarith

/-- The `ℂ`-linear `L²` realization of a subspace `V` of continuous compactly supported functions,
mapping `f` to `(conj ∘ f)` via a basis of `V` or directly on `(Fin d → ℂ)`. -/
theorem finrank_mul_le_four_mul_of_band_concentrated {a T κ : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, Continuous f ∧ tsupport f ⊆ Icc (-a) a)
    (hconc : ∀ f ∈ V, κ * (∫ u, ‖f u‖ ^ 2) ≤ ∫ τ in (-T)..T, ‖paperFT f τ‖ ^ 2) :
    (Module.finrank ℂ V : ℝ) * κ ≤ 4 * T * a := by
  set d := Module.finrank ℂ V
  set bV := Module.finBasis ℂ V
  have hfd : ∀ i : Fin d, Continuous ((bV i : V) : ℝ → ℂ) := fun i => (hV _ (bV i).2).1
  have hfs : ∀ i : Fin d, tsupport ((bV i : V) : ℝ → ℂ) ⊆ Icc (-a) a := fun i => (hV _ (bV i).2).2
  have hfc : ∀ i : Fin d, HasCompactSupport ((bV i : V) : ℝ → ℂ) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hfs i)
  set f : Fin d → ℝ → ℂ := fun i => (bV i : V)
  have hmem : ∀ x : Fin d → ℂ, (∑ i, conj (x i) • f i) ∈ V := fun x =>
    Submodule.sum_mem V fun i _ => Submodule.smul_mem V _ (bV i).2
  have hinj : ∀ x : Fin d → ℂ, comboL2 f hfd hfc x = 0 → x = 0 := by
    intro x hx
    have hnorm : ‖comboL2 f hfd hfc x‖ ^ 2 = 0 := by rw [hx, norm_zero, sq, mul_zero]
    rw [norm_comboL2_sq] at hnorm
    set g := ∑ i, conj (x i) • f i
    have hgV : g ∈ V := hmem x
    have hgcont : Continuous g := (hV g hgV).1
    have hgc : HasCompactSupport g :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hV g hgV).2
    have hint : Integrable fun u => ‖g u‖ ^ 2 := by
      have h : Integrable fun u => ‖g u‖ * ‖g u‖ :=
        (hgcont.norm.mul hgcont.norm).integrable_of_hasCompactSupport hgc.norm.mul_right
      simpa only [← pow_two] using h
    have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hint).mp hnorm
    have hzero : (fun u => ‖g u‖ ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq volume (hgcont.norm.pow 2) continuous_const).mp hae
    have hg0 : g = 0 := by
      funext u
      have := congrFun hzero u
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        norm_eq_zero] at this
      exact this
    have hg0' : (∑ i, conj (x i) • bV i : V) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_zero]
      exact hg0
    have hli := Fintype.linearIndependent_iff.mp bV.linearIndependent (fun i => conj (x i)) hg0'
    funext i
    exact (map_eq_zero (starRingEnd ℂ)).mp (hli i)
  have hdelta : ∀ ε > 0, (d : ℝ) * κ ≤ 4 * T * a + ε := by
    intro ε hε
    set δ := ε / (4 * T + 1) with hδdef
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hle := finrank_mul_le_of_concentrated_le (⊤ : Submodule ℂ (Fin d → ℂ))
      (comboL2 f hfd hfc) (cutCharDeltaL2 a hδ) hT (norm_cutCharDeltaL2_sq_le ha hδ)
      (fun x _ => by
        have h : (fun τ => ⟪comboL2 f hfd hfc x, cutCharDeltaL2 a hδ τ⟫_ℂ) =
            fun τ : ℝ => paperFT (∑ i, conj (x i) • f i) τ :=
          funext fun τ => inner_comboL2_cutCharDeltaL2 hδ f hfd hfc hfs x τ
        rw [h]
        have hgV := hmem x
        exact RHTower.WeilOneSided.continuous_paperFT_real_arg
          ((hV _ hgV).1.integrable_of_hasCompactSupport
            (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hV _ hgV).2)))
      (fun x _ hx => hinj x hx)
      (fun x _ => by
        have h : ∫ τ in (-T)..T, ‖⟪comboL2 f hfd hfc x, cutCharDeltaL2 a hδ τ⟫_ℂ‖ ^ 2 =
            ∫ τ in (-T)..T, ‖paperFT (∑ i, conj (x i) • f i) τ‖ ^ 2 := by
          congr 1; funext τ; rw [inner_comboL2_cutCharDeltaL2 hδ f hfd hfc hfs x τ]
        rw [norm_comboL2_sq, h]
        exact hconc _ (hmem x))
    have htop : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = d := by
      rw [finrank_top, Module.finrank_fin_fun]
    rw [htop] at hle
    have h4T : 4 * T * δ ≤ ε := by
      rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]
      linarith
    linarith
  exact le_of_forall_pos_le_add hdelta

/-- **Unconditional Bessel–Shannon near-radical bound (`zeta_near_radical_finrank_le_shannon`).**
Every finite-dimensional subspace `V` of `C²` tests supported in `[−L, L]` (`L ≥ 0`), with
`paperFT f (I / 2) = 0` and `(zetaZeroConfig.W f f).re ≤ ε ∫ ‖f‖²` (`ε ≥ 0`), satisfies
`dim V ≤ 4 L T_ε(L) / π = 2 · Shannon(L, T_ε(L))`.
This removes the `T_ε(L)^{3/2}(L + 1)^{3/2}` Lipschitz-grid overhead of `finrank_le_of_re_W_le`. -/
theorem zeta_near_radical_finrank_le_shannon {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0)
    (hW : ∀ f ∈ V, (zetaZeroConfig.W f f).re ≤ ε * ∫ u, ‖f u‖ ^ 2) :
    (Module.finrank ℂ V : ℝ) ≤ 4 * L * horizonFreqEps L ε / π := by
  have hπ := Real.pi_pos
  rw [le_div_iff₀ hπ]
  have h := finrank_mul_le_four_mul_of_band_concentrated hL (horizonFreqEps_nonneg L hε) V
    (fun f hf => ⟨(hV f hf).1.continuous, (hV f hf).2.1⟩)
    (fun f hf => pi_mul_integral_le_of_re_W_le hε (hV f hf).1 (hV f hf).2.1 (hV f hf).2.2
      (hW f hf))
  linarith

/-- **Sharp degree-filtration bound for the Hodge defect of `ζ` (`negIndex_zeroGram_zeta_le_shannon`,
`hodgeDefectAt_zeta_le_shannon`).** At every degree `a ≥ 0`, every finite family of `C²` tests
supported in `[−a, a]` has at most `1 + 4aT(a)/π` negative squares in its Weil Gram matrix
(improving `1 + 2T(a)(2a + 2)/π` of `negIndex_zeroGram_zeta_le`, and giving `1` at `a = 0`). -/
theorem negIndex_zeroGram_zeta_le_shannon {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a) :
    (hermNegIndex (zeroGram zetaZeroConfig f) : ℝ) ≤ 1 + 4 * a * horizonFreq a / π := by
  have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hf i).1
  have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun i => (hf i).2
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hfs i)
  have hfcont : ∀ i, Continuous (f i) := fun i => (hfd i).continuous
  obtain ⟨U, hUrank, hU⟩ := exists_isPosDefOn_finrank_eq_posIndex (-zeroGram zetaZeroConfig f)
  have hneg : ∀ x ∈ U, x ≠ 0 → hermQuad (zeroGram zetaZeroConfig f) x < 0 := fun x hx hx0 => by
    have h := hU x hx hx0
    rw [hermQuad_neg] at h
    linarith
  have hdim := finrank_le_finrank_inf_ker_add_one U (evalFunctional f (I / 2))
  set U₀ : Submodule ℂ (Fin n → ℂ) := U ⊓ LinearMap.ker (evalFunctional f (I / 2))
  have hdelta : ∀ ε > 0, (Module.finrank ℂ U₀ : ℝ) * π ≤ 4 * horizonFreq a * a + ε := by
    intro ε hε
    set δ := ε / (4 * horizonFreq a + 1) with hδdef
    have hδ : 0 < δ := div_pos hε (by have := horizonFreq_nonneg a; positivity)
    have hcount := finrank_mul_le_of_concentrated U₀ (comboL2 f hfcont hfc) (cutCharDeltaL2 a hδ)
      (horizonFreq_nonneg a) (norm_cutCharDeltaL2_sq_le ha hδ)
      (fun x _ => by
        have h : (fun τ => ⟪comboL2 f hfcont hfc x, cutCharDeltaL2 a hδ τ⟫_ℂ) =
            fun τ : ℝ => paperFT (∑ i, conj (x i) • f i) τ :=
          funext fun τ => inner_comboL2_cutCharDeltaL2 hδ f hfcont hfc hfs x τ
        rw [h]
        exact RHTower.WeilOneSided.continuous_paperFT_real_arg
          ((contDiff_sum_smul f hfd _).continuous.integrable_of_hasCompactSupport
            (hasCompactSupport_sum_smul f hfc _)))
      (fun x hx hx0 => by
        have h : ∫ τ in (-horizonFreq a)..horizonFreq a,
              ‖⟪comboL2 f hfcont hfc x, cutCharDeltaL2 a hδ τ⟫_ℂ‖ ^ 2 =
            ∫ τ in (-horizonFreq a)..horizonFreq a,
              ‖paperFT (∑ i, conj (x i) • f i) τ‖ ^ 2 := by
          congr 1; funext τ; rw [inner_comboL2_cutCharDeltaL2 hδ f hfcont hfc hfs x τ]
        have h2 : ∫ τ in (-horizonFreq a)..horizonFreq a,
              ‖⟪comboL2 f hfcont hfc x, cutCharL2 a τ⟫_ℂ‖ ^ 2 =
            ∫ τ in (-horizonFreq a)..horizonFreq a,
              ‖paperFT (∑ i, conj (x i) • f i) τ‖ ^ 2 := by
          congr 1; funext τ; rw [inner_comboL2_cutCharL2 f hfcont hfc hfs x τ]
        rw [h, ← h2]
        exact conc_comboL2 f hfd hfc hfs hx.2 (hneg x hx.1 hx0))
    have h4T : 4 * horizonFreq a * δ ≤ ε := by
      have := horizonFreq_nonneg a
      rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hcount : (Module.finrank ℂ U₀ : ℝ) * π ≤ 4 * horizonFreq a * a :=
    le_of_forall_pos_le_add hdelta
  have hπ : 0 < π := Real.pi_pos
  have hle : (Module.finrank ℂ U₀ : ℝ) ≤ 4 * a * horizonFreq a / π := by
    rw [le_div_iff₀ hπ]
    linarith
  have hk : hermNegIndex (zeroGram zetaZeroConfig f) = Module.finrank ℂ U := hUrank.symm
  have hcast : (hermNegIndex (zeroGram zetaZeroConfig f) : ℝ) ≤
      (Module.finrank ℂ U₀ : ℝ) + 1 := by
    rw [hk]
    exact_mod_cast hdim
  linarith

/-- At every degree `a ≥ 0`, `hodgeDefectAt ζ a ≤ ⌊1 + 4aT(a)/π⌋`. -/
theorem hodgeDefectAt_zeta_le_shannon {a : ℝ} (ha : 0 ≤ a) :
    hodgeDefectAt zetaZeroConfig a ≤ (⌊1 + 4 * a * horizonFreq a / π⌋₊ : ℕ∞) :=
  iSup₂_le fun _ f => iSup_le fun hf =>
    ENat.coe_le_coe.mpr (Nat.le_floor (negIndex_zeroGram_zeta_le_shannon ha f hf))

/-- **Hilbert-space Bessel–projection dimension bound (`finrank_mul_le_finrank_of_concentrated`).**
Let `V` and `K` be finite-dimensional subspaces of an inner product space `E`, and let `bK` be
the standard orthonormal basis of `K`. If every `x ∈ V` has at least `κ‖x‖²` of its norm squared
along `K` (`κ * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪x, bK i⟫_ℂ‖ ^ 2`), then `dim V · κ ≤ dim K`. -/
theorem finrank_mul_le_finrank_of_concentrated {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (V K : Submodule ℂ E) [FiniteDimensional ℂ V] [FiniteDimensional ℂ K]
    {κ : ℝ} (hconc : ∀ x ∈ V,
      κ * ‖x‖ ^ 2 ≤ ∑ i : Fin (Module.finrank ℂ K), ‖⟪x, (stdOrthonormalBasis ℂ K i : E)⟫_ℂ‖ ^ 2) :
    (Module.finrank ℂ V : ℝ) * κ ≤ Module.finrank ℂ K := by
  set bV := stdOrthonormalBasis ℂ V
  set bK := stdOrthonormalBasis ℂ K
  have honV : Orthonormal ℂ (fun j => (bV j : E)) := bV.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have honK : Orthonormal ℂ (fun i => (bK i : E)) := bK.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hlow : ∀ j : Fin (Module.finrank ℂ V),
      κ ≤ ∑ i : Fin (Module.finrank ℂ K), ‖⟪(bV j : E), (bK i : E)⟫_ℂ‖ ^ 2 := by
    intro j
    have h := hconc (bV j : E) (bV j).2
    rwa [honV.1 j, one_pow, mul_one] at h
  have hsumV : (Module.finrank ℂ V : ℝ) * κ ≤
      ∑ j : Fin (Module.finrank ℂ V),
        ∑ i : Fin (Module.finrank ℂ K), ‖⟪(bV j : E), (bK i : E)⟫_ℂ‖ ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun (j : Fin (Module.finrank ℂ V)) _ => hlow j
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  rw [Finset.sum_comm] at hsumV
  have hsumK : (∑ i : Fin (Module.finrank ℂ K),
      ∑ j : Fin (Module.finrank ℂ V), ‖⟪(bV j : E), (bK i : E)⟫_ℂ‖ ^ 2) ≤
        Module.finrank ℂ K := by
    have h1 : ∀ i : Fin (Module.finrank ℂ K),
        (∑ j : Fin (Module.finrank ℂ V), ‖⟪(bV j : E), (bK i : E)⟫_ℂ‖ ^ 2) ≤ 1 := by
      intro i
      have hb := honV.sum_inner_products_le (bK i : E) (s := Finset.univ)
      rwa [honK.1 i, one_pow] at hb
    have h2 := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin (Module.finrank ℂ K)) _ => h1 i
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h2
  exact hsumV.trans hsumK

/-- **Bessel–projection bound for subspaces concentrated along a constraint kernel
(`finrank_mul_le_sub_of_concentrated_ker`).**
If `W` is a finite-dimensional subspace of `E`, `Λ : W →ₗ[ℂ] C` is a linear constraint map,
`K = (LinearMap.ker Λ).map W.subtype`, and `V ≤ E` is `κ`-concentrated along `K`, then
`dim V · κ ≤ dim W − dim(range Λ)`. -/
theorem finrank_mul_le_sub_of_concentrated_ker {E C : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [AddCommGroup C] [Module ℂ C]
    (V W : Submodule ℂ E) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (Λ : W →ₗ[ℂ] C) {κ : ℝ}
    (hconc : ∀ x ∈ V,
      κ * ‖x‖ ^ 2 ≤
        ∑ i : Fin (Module.finrank ℂ ((LinearMap.ker Λ).map W.subtype)),
          ‖⟪x, (stdOrthonormalBasis ℂ ((LinearMap.ker Λ).map W.subtype) i : E)⟫_ℂ‖ ^ 2) :
    (Module.finrank ℂ V : ℝ) * κ ≤
      (Module.finrank ℂ W : ℝ) - (Module.finrank ℂ (LinearMap.range Λ) : ℝ) := by
  set K := (LinearMap.ker Λ).map W.subtype
  have h1 := finrank_mul_le_finrank_of_concentrated V K hconc
  have heq : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker Λ) :=
    (Submodule.equivMapOfInjective W.subtype Subtype.val_injective (LinearMap.ker Λ)).finrank_eq.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Λ
  have hsub : (Module.finrank ℂ K : ℝ) =
      (Module.finrank ℂ W : ℝ) - (Module.finrank ℂ (LinearMap.range Λ) : ℝ) := by
    rw [heq]
    have : (Module.finrank ℂ (LinearMap.range Λ) : ℝ) +
        (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) = (Module.finrank ℂ W : ℝ) := by
      exact_mod_cast hrn
    linarith
  linarith

/-- **The Two-Sided Landau–Widom Near-Radical Dimension Law
(`zeta_landau_widom_two_sided_dimension_law`).**
Unconditionally, for every `0 < η ≤ 1` there exists `L₀` such that for all `L ≥ L₀`:
1. **(Lower bound `(2 − η)e^{2L}`)** The Hodge-class tests at level `L` (`C²`, supported in
   `[−L, L]`, `f̂(±i/2) = 0`) contain a subspace `V_−` of dimension `≥ (2 − η)e^{2L}` on which
   `‖W_ζ(f, f)‖ ≤ exp(−η²e^{2L}/(300L)) ∫‖f‖²`.
2. **(Upper bound `(2 + η)e^{2L}` across all bandwidths `T ≥ 0`)** For every bandwidth `T ≥ 0`,
   every finite-dimensional bandwidth-`T` space `W` with `dim W ≤ 2TL/π` and every linear
   zero-constraint map `Λ : W →ₗ[ℂ] C` whose rank captures the cumulative zero count up to defect
   `≤ (η/2)e^{2L}` (`2 N(0, T) − (η/2)e^{2L} ≤ dim(range Λ)`), every subspace
   `V_+ ≤ LinearMap.ker Λ` satisfies `dim V_+ ≤ (2 + η)e^{2L}`. -/
theorem zeta_landau_widom_two_sided_dimension_law :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      (∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
        (2 - η) * Real.exp (2 * L) ≤ (Module.finrank ℂ V : ℝ) ∧
        (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
          paperFT f (-(I / 2)) = 0) ∧
        ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤
          Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) * ∫ u, ‖f u‖ ^ 2) ∧
      (∀ (T : ℝ), 0 ≤ T →
        ∀ {M C : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup C] [Module ℂ C]
          (W : Submodule ℂ M) [FiniteDimensional ℂ W] (Λ : W →ₗ[ℂ] C)
          (V : Submodule ℂ W),
          V ≤ LinearMap.ker Λ →
          (Module.finrank ℂ W : ℝ) ≤ 2 * T * L / π →
          2 * (zetaZeroConfig.N 0 T : ℝ) - (η / 2) * Real.exp (2 * L) ≤
            (Module.finrank ℂ (LinearMap.range Λ) : ℝ) →
          (Module.finrank ℂ V : ℝ) ≤ (2 + η) * Real.exp (2 * L)) := by
  intro η hη0 hη1
  obtain ⟨L₁, hL₁⟩ := RHTower.zeta_weil_near_radical_sharp_count η hη0 hη1
  obtain ⟨L₂, hL₂⟩ := Filter.eventually_atTop.mp
    (eventually_shannon_sub_zetaZeroCount_le (η / 2) (by positivity))
  refine ⟨max L₁ L₂, fun L hL => ⟨hL₁ L (le_trans (le_max_left _ _) hL), ?_⟩⟩
  intro T hT M C _ _ _ _ W _ Λ V hVle hWdim hΛrank
  have hsur := hL₂ L (le_trans (le_max_right _ _) hL) T hT
  have hrn := LinearMap.finrank_range_add_finrank_ker Λ
  have hVker : (Module.finrank ℂ V : ℝ) ≤ (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) := by
    exact_mod_cast Submodule.finrank_mono hVle
  have hker_eq : (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) =
      (Module.finrank ℂ W : ℝ) - (Module.finrank ℂ (LinearMap.range Λ) : ℝ) := by
    have : (Module.finrank ℂ (LinearMap.range Λ) : ℝ) +
        (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) = (Module.finrank ℂ W : ℝ) := by
      exact_mod_cast hrn
    linarith
  linarith

/-! ### 4. The Landau–Widom rate `−log μ(L) ≍ 2π² N(T*)/log N(T*)` and critical-line coercivity -/

/-- Exact value of the Riemann–von Mangoldt main term at the Landau height `edgeRate L = 2πe^{2L}`:
`zeroCountMain (edgeRate L) = e^{2L}(2L − 1)`. -/
theorem zeroCountMain_edgeRate_eq (L : ℝ) :
    RHTower.zeroCountMain (RHTower.edgeRate L) = Real.exp (2 * L) * (2 * L - 1) := by
  unfold RHTower.zeroCountMain RHTower.edgeRate
  have hpi := Real.pi_pos
  have hdiv : 2 * π * Real.exp (2 * L) / (2 * π) = Real.exp (2 * L) := by field_simp
  rw [hdiv, Real.log_exp]

/-- **Exact two-sided bridge `(1/2)e^{2L} ≤ F(T*)/log F(T*) ≤ e^{2L}` for all `L ≥ 1`.**
At the Landau height `T* = edgeRate L = 2πe^{2L}`, `F(T*) = zeroCountMain T*` satisfies
`(1/2)e^{2L} ≤ F(T*)/log F(T*) ≤ e^{2L}` for every `L ≥ 1`. -/
theorem zeroCountMain_edgeRate_div_log_bounds {L : ℝ} (hL : 1 ≤ L) :
    1 / 2 * Real.exp (2 * L) ≤
        RHTower.zeroCountMain (RHTower.edgeRate L) /
          Real.log (RHTower.zeroCountMain (RHTower.edgeRate L)) ∧
      RHTower.zeroCountMain (RHTower.edgeRate L) /
          Real.log (RHTower.zeroCountMain (RHTower.edgeRate L)) ≤
        Real.exp (2 * L) := by
  rw [zeroCountMain_edgeRate_eq]
  set x := 2 * L - 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hx0 : 0 < x := by linarith
  have hE := Real.exp_pos (2 * L)
  have hlog : Real.log (Real.exp (2 * L) * x) = 2 * L + Real.log x := by
    rw [Real.log_mul hE.ne' hx0.ne', Real.log_exp]
  rw [hlog]
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogx_le : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hden_pos : 0 < 2 * L + Real.log x := by linarith
  have hden_lo : x ≤ 2 * L + Real.log x := by linarith
  have hden_hi : 2 * L + Real.log x ≤ 2 * x := by linarith
  constructor
  · rw [le_div_iff₀ hden_pos]
    nlinarith
  · rw [div_le_iff₀ hden_pos]
    nlinarith

/-- **Unconditional two-sided bridge `(1/3)e^{2L} ≤ N(0, T*)/log N(0, T*) ≤ 2e^{2L}` for the
actual cumulative zero count of `ζ` at the Landau height `T* = edgeRate L = 2πe^{2L}`.** -/
theorem eventually_zetaZeroCount_edgeRate_div_log_bounds :
    ∀ᶠ L : ℝ in atTop,
      1 < (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ) ∧
      1 / 3 * Real.exp (2 * L) ≤
        (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ) /
          Real.log (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ) ∧
      (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ) /
          Real.log (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ) ≤
        2 * Real.exp (2 * L) := by
  obtain ⟨C, T₁, hC0, hT₁, htwo⟩ := zeroCount_twoSided
  have he1 := RHTower.eventually_mul_pow_four_le_exp (K := 1 / 2) (by norm_num) (16 * C)
  have he2 := RHTower.eventually_mul_pow_four_le_exp (K := 2 * π) (by positivity) T₁
  filter_upwards [eventually_ge_atTop (2 : ℝ), he1, he2] with L hL2 hCerr hT₁_exp
  have hE := Real.exp_pos (2 * L)
  have hE1 : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
  have hTT₁ : T₁ ≤ RHTower.edgeRate L := by
    unfold RHTower.edgeRate
    have hp1 : 1 ≤ (1 + L) ^ 4 := one_le_pow₀ (by linarith)
    have : T₁ ≤ T₁ * (1 + L) ^ 4 := le_mul_of_one_le_right (by linarith) hp1
    linarith
  have h := htwo (RHTower.edgeRate L) hTT₁
  rw [zeroCountMain_edgeRate_eq] at h
  have hlogY : Real.log (RHTower.edgeRate L) ^ 2 ≤ 16 * (1 + L) ^ 4 := by
    unfold RHTower.edgeRate
    have hpi := RHTower.log_two_pi_lt_two
    have hl : Real.log (2 * π * Real.exp (2 * L)) = Real.log (2 * π) + 2 * L := by
      rw [Real.log_mul (by positivity) hE.ne', Real.log_exp]
    have hl0 : 0 ≤ Real.log (2 * π * Real.exp (2 * L)) := by
      rw [hl]; linarith [Real.log_nonneg (show 1 ≤ 2 * π by nlinarith [Real.pi_gt_three])]
    have hle : Real.log (2 * π * Real.exp (2 * L)) ≤ 4 * (1 + L) := by rw [hl]; linarith
    calc Real.log (2 * π * Real.exp (2 * L)) ^ 2 ≤ (4 * (1 + L)) ^ 2 :=
          pow_le_pow_left₀ hl0 hle 2
      _ = 16 * (1 + L) ^ 2 := by ring
      _ ≤ 16 * (1 + L) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hC_bound : C * Real.log (RHTower.edgeRate L) ^ 2 ≤ 1 / 2 * Real.exp (2 * L) := by
    calc C * Real.log (RHTower.edgeRate L) ^ 2 ≤ C * (16 * (1 + L) ^ 4) :=
          mul_le_mul_of_nonneg_left hlogY hC0
      _ = 16 * C * (1 + L) ^ 4 := by ring
      _ ≤ 1 / 2 * Real.exp (2 * L) := hCerr
  set Nstar := (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ)
  have hN_lo : Real.exp (2 * L) * (2 * L - 3 / 2) ≤ Nstar := by
    have h1 := (abs_le.mp h).1
    linarith
  have hN_hi : Nstar ≤ Real.exp (2 * L) * (2 * L) := by
    have h1 := (abs_le.mp h).2
    linarith
  have hN_gt1 : 1 < Nstar := by
    have : 2 * Real.exp (2 * L) ≤ Real.exp (2 * L) * (2 * L - 3 / 2) := by nlinarith
    linarith
  have hlogN_pos : 0 < Real.log Nstar := Real.log_pos hN_gt1
  have hlogN_lo : 2 * L ≤ Real.log Nstar := by
    rw [← Real.log_exp (2 * L)]
    refine Real.log_le_log hE ?_
    have : Real.exp (2 * L) * 1 ≤ Real.exp (2 * L) * (2 * L - 3 / 2) := by nlinarith
    linarith
  have hlogN_hi : Real.log Nstar ≤ 4 * L - 2 := by
    have h2L0 : 0 < 2 * L := by linarith
    have h1 : Real.log Nstar ≤ Real.log (Real.exp (2 * L) * (2 * L)) :=
      Real.log_le_log (by linarith) hN_hi
    rw [Real.log_mul hE.ne' h2L0.ne', Real.log_exp] at h1
    have h2 : Real.log (2 * L) ≤ 2 * L - 2 := by
      have := Real.log_le_sub_one_of_pos (x := L) (by linarith)
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num); linarith
      rw [Real.log_mul (by norm_num) (by linarith)]
      linarith
    linarith
  refine ⟨hN_gt1, ?_, ?_⟩
  · rw [le_div_iff₀ hlogN_pos]
    have h1 : 1 / 3 * Real.exp (2 * L) * Real.log Nstar ≤
        1 / 3 * Real.exp (2 * L) * (4 * L - 2) :=
      mul_le_mul_of_nonneg_left hlogN_hi (by positivity)
    have h2 : 1 / 3 * Real.exp (2 * L) * (4 * L - 2) ≤ Real.exp (2 * L) * (2 * L - 3 / 2) := by
      nlinarith
    linarith
  · rw [div_le_iff₀ hlogN_pos]
    have h1 : Real.exp (2 * L) * (2 * L) ≤ 2 * Real.exp (2 * L) * (2 * L) := by nlinarith
    have h2 : 2 * Real.exp (2 * L) * (2 * L) ≤ 2 * Real.exp (2 * L) * Real.log Nstar :=
      mul_le_mul_of_nonneg_left hlogN_lo (by positivity)
    linarith

/-- **The Two-Sided Landau–Widom Rate Law `−log W(Φχ_L) ≍ 2π² N(T*)/log N(T*)`
(`exists_twoSided_truncKernel_log_energy_landauRate`).**
Unconditionally, for all sufficiently large `L`, the canonical near-null Weil energy
`W_L = Re W_ζ(Φχ_L, Φχ_L)` at aperture `L` is strictly positive and satisfies the two-sided
Landau–Widom rate law in terms of `N*(L) = N(0, 2πe^{2L})`:
`(1/(4π)) · (2π² N*(L)/log N*(L)) ≤ −log W_L ≤ (9/(2π)) · (2π² N*(L)/log N*(L))`. -/
theorem exists_twoSided_truncKernel_log_energy_landauRate :
    ∀ᶠ L : ℝ in atTop,
      let W_L := (zetaZeroConfig.W (fun u => (RHTower.riemannTruncKernel L u : ℂ))
        (fun u => (RHTower.riemannTruncKernel L u : ℂ))).re
      let Nstar := (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ)
      0 < W_L ∧
        1 / (4 * π) * (2 * π ^ 2 * Nstar / Real.log Nstar) ≤ -Real.log W_L ∧
        -Real.log W_L ≤ 9 / (2 * π) * (2 * π ^ 2 * Nstar / Real.log Nstar) := by
  obtain ⟨K, hKpos, htwo⟩ := RHTower.exists_twoSided_truncKernel_energy
  have he1 := RHTower.eventually_mul_pow_four_le_exp (K := π) Real.pi_pos
    (9 + |Real.log K| + 3)
  filter_upwards [eventually_ge_atTop (1 : ℝ), htwo,
    eventually_zetaZeroCount_edgeRate_div_log_bounds, he1] with L hL1 hW hN hlin
  obtain ⟨hW_lo, hW_hi⟩ := hW
  obtain ⟨hN1, hN_lo, hN_hi⟩ := hN
  set W_L := (zetaZeroConfig.W (fun u => (RHTower.riemannTruncKernel L u : ℂ))
    (fun u => (RHTower.riemannTruncKernel L u : ℂ))).re
  set Nstar := (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ)
  have hEL := RHTower.kernelEnvelope_pos L
  have hY := RHTower.edgeRate_pos L
  have hW_pos : 0 < W_L := lt_of_lt_of_le (div_pos (sq_pos_of_pos hEL) hY) hW_lo
  have hlogE : Real.log (RHTower.kernelEnvelope L ^ 2) =
      9 * L - 2 * π * Real.exp (2 * L) := by
    unfold RHTower.kernelEnvelope
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    push_cast
    ring
  have hlogY : Real.log (RHTower.edgeRate L) ≤ 2 + 2 * L := by
    unfold RHTower.edgeRate
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have := RHTower.log_two_pi_lt_two
    linarith
  have hpow : L ≤ (1 + L) ^ 4 := by
    have : (1 + L) ^ 1 ≤ (1 + L) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hp1 : 1 ≤ (1 + L) ^ 4 := one_le_pow₀ (by linarith)
  have h9L : 9 * L + |Real.log K| + 3 * L ≤ π * Real.exp (2 * L) := by
    have h1 : 9 * L + |Real.log K| + 3 * L ≤ (9 + |Real.log K| + 3) * (1 + L) ^ 4 := by
      have := abs_nonneg (Real.log K)
      nlinarith
    exact h1.trans hlin
  have hlogW_hi : Real.log W_L ≤ Real.log K + 9 * L - 2 * π * Real.exp (2 * L) := by
    have h1 := Real.log_le_log hW_pos hW_hi
    rw [Real.log_mul hKpos.ne' (sq_pos_of_pos hEL).ne', hlogE] at h1
    linarith
  have hlogW_lo : 9 * L - 2 * π * Real.exp (2 * L) - (2 + 2 * L) ≤ Real.log W_L := by
    have h1 := Real.log_le_log (div_pos (sq_pos_of_pos hEL) hY) hW_lo
    rw [Real.log_div (sq_pos_of_pos hEL).ne' hY.ne', hlogE] at h1
    linarith
  have hneg_lo : π * Real.exp (2 * L) ≤ -Real.log W_L := by
    have := le_abs_self (Real.log K)
    linarith
  have hneg_hi : -Real.log W_L ≤ 3 * π * Real.exp (2 * L) := by
    have := abs_nonneg (Real.log K)
    linarith
  have hpi := Real.pi_pos
  refine ⟨hW_pos, ?_, ?_⟩
  · have h1 : 1 / (4 * π) * (2 * π ^ 2 * Nstar / Real.log Nstar) =
        π / 2 * (Nstar / Real.log Nstar) := by field_simp; ring
    rw [h1]
    have h2 : π / 2 * (Nstar / Real.log Nstar) ≤ π / 2 * (2 * Real.exp (2 * L)) :=
      mul_le_mul_of_nonneg_left hN_hi (by positivity)
    linarith
  · have h1 : 9 / (2 * π) * (2 * π ^ 2 * Nstar / Real.log Nstar) =
        9 * π * (Nstar / Real.log Nstar) := by field_simp
    rw [h1]
    have h2 : 9 * π * (1 / 3 * Real.exp (2 * L)) ≤ 9 * π * (Nstar / Real.log Nstar) :=
      mul_le_mul_of_nonneg_left hN_lo (by positivity)
    linarith

/-- On the smooth near-radical subspace of `zeta_weil_near_radical_dimension_smooth`
(`dim V ≥ e^{2L − 2}/20`), every `f ∈ V` has Weil energy exponentially small at the
Landau–Widom rate `2π² N(0, T*)/log N(0, T*)`. -/
theorem eventually_near_radical_subspace_landauRate :
    ∀ᶠ L : ℝ in atTop,
      let Nstar := (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ)
      ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
        1 / (40 * Real.exp 2) * (Nstar / Real.log Nstar) ≤ (Module.finrank ℂ V : ℝ) ∧
        (∀ f ∈ V, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
          paperFT f (-(I / 2)) = 0) ∧
        ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤
          Real.exp (-(1 / (4 * π ^ 2 * Real.exp 2) * (2 * π ^ 2 * Nstar / Real.log Nstar))) *
            ∫ u, ‖f u‖ ^ 2 := by
  obtain ⟨L₀, hL₀⟩ := RHTower.zeta_weil_near_radical_dimension_smooth
  filter_upwards [eventually_ge_atTop L₀,
    eventually_zetaZeroCount_edgeRate_div_log_bounds] with L hL hN
  obtain ⟨hN1, hN_lo, hN_hi⟩ := hN
  obtain ⟨V, hVfin, hdim, hV, hW⟩ := hL₀ L hL
  set Nstar := (zetaZeroConfig.N 0 (RHTower.edgeRate L) : ℝ)
  have hexp : Real.exp (2 * L - 2) = Real.exp (2 * L) / Real.exp 2 := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
  refine ⟨V, hVfin, ?_, hV, fun f hf => (hW f hf).trans ?_⟩
  · have h1 : 1 / (40 * Real.exp 2) * (Nstar / Real.log Nstar) ≤
        1 / (40 * Real.exp 2) * (2 * Real.exp (2 * L)) :=
      mul_le_mul_of_nonneg_left hN_hi (by positivity)
    have h2 : 1 / (40 * Real.exp 2) * (2 * Real.exp (2 * L)) = Real.exp (2 * L - 2) / 20 := by
      rw [hexp]; ring
    linarith
  · apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_pos
    have h1 : 1 / (4 * π ^ 2 * Real.exp 2) * (2 * π ^ 2 * Nstar / Real.log Nstar) =
        1 / (2 * Real.exp 2) * (Nstar / Real.log Nstar) := by field_simp; ring
    rw [h1, hexp]
    have h2 : 1 / (2 * Real.exp 2) * (Nstar / Real.log Nstar) ≤
        1 / (2 * Real.exp 2) * (2 * Real.exp (2 * L)) :=
      mul_le_mul_of_nonneg_left hN_hi (by positivity)
    have h3 : 1 / (2 * Real.exp 2) * (2 * Real.exp (2 * L)) = Real.exp (2 * L) / Real.exp 2 := by
      ring
    linarith

/-- **Critical-line zero-side coercivity (`Wsummand_re_eq_of_re_eq_half`,
`sum_norm_sq_paperFT_le_re_W_of_criticalLine`).**
At any zero `ρ` on the critical line (`ρ.re = 1/2`), `gammaOf ρ = ρ.im` is real and
`Re (Wsummand f f ρ) = mult(ρ) ‖f̂(ρ.im)‖² ≥ 0`. -/
theorem Wsummand_re_eq_of_re_eq_half (Z : ZeroConfig) (f : ℝ → ℂ) (ρ : Z.carrier)
    (hre : (ρ : ℂ).re = 1 / 2) :
    (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * ‖paperFT f ((ρ : ℂ).im : ℂ)‖ ^ 2 := by
  unfold ZeroConfig.Wsummand
  have hγ : gammaOf (ρ : ℂ) = ((ρ : ℂ).im : ℂ) := by
    unfold gammaOf
    apply Complex.ext
    · simp
    · simp [hre]
  rw [hγ, Complex.conj_ofReal, mul_assoc, Complex.mul_conj, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- For a configuration `Z` on the critical line (`∀ ρ ∈ Z.carrier, ρ.re = 1/2`) whose Weil series
is summable at `f`, the real part of `Z.W f f` dominates every finite partial sum of
`mult(ρ) ‖f̂(ρ.im)‖²`. -/
theorem sum_norm_sq_paperFT_le_re_W_of_criticalLine (Z : ZeroConfig)
    (hline : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) (f : ℝ → ℂ)
    (hsum : Summable (fun ρ : Z.carrier => Z.Wsummand f f ρ))
    (S : Finset Z.carrier) :
    (∑ ρ ∈ S, (Z.mult ρ : ℝ) * ‖paperFT f ((ρ : ℂ).im : ℂ)‖ ^ 2) ≤ (Z.W f f).re := by
  have hsum_re : Summable (fun ρ : Z.carrier => (Z.Wsummand f f ρ).re) :=
    Complex.reCLM.summable hsum
  have hre_eq : (Z.W f f).re = ∑' ρ : Z.carrier, (Z.Wsummand f f ρ).re := by
    unfold ZeroConfig.W
    exact (Complex.re_tsum hsum)
  rw [hre_eq]
  have hterm : ∀ ρ : Z.carrier,
      (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * ‖paperFT f ((ρ : ℂ).im : ℂ)‖ ^ 2 :=
    fun ρ => Wsummand_re_eq_of_re_eq_half Z f ρ (hline ρ ρ.2)
  have hnonneg : ∀ ρ : Z.carrier, 0 ≤ (Z.Wsummand f f ρ).re := fun ρ => by
    rw [hterm ρ]
    positivity
  calc (∑ ρ ∈ S, (Z.mult ρ : ℝ) * ‖paperFT f ((ρ : ℂ).im : ℂ)‖ ^ 2)
      = ∑ ρ ∈ S, (Z.Wsummand f f ρ).re := Finset.sum_congr rfl fun ρ _ => (hterm ρ).symm
    _ ≤ ∑' ρ : Z.carrier, (Z.Wsummand f f ρ).re := hsum_re.sum_le_tsum S fun ρ _ => hnonneg ρ

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
