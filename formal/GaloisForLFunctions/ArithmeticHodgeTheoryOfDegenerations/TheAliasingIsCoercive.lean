import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalMultipleOfAWindow
import GaloisForLFunctions.BiScaleUncertainty.EffectiveTranslatedPairingAndMultiplicityDefect

/-!
# The aliasing is coercive

The upper half of the horizon theorem bounds the aliasing part of a horizon block by `O(log N/c^p)`.
For the tilted spline the bound is sharp in order. Its transform is bounded below,
`‖φ̂(u)‖² ≥ (sinh⁸ 1/64)(1 + |u|)^{−8}`; the symbol is positive above the archimedean horizon,
`ν(τ) ≥ (log(1 + |τ|/4) − 10)/(2π) − X²/π`; and the mean-value theorem holds from below on long
windows, `∫_U^{2U} |D_x|² ≥ U Σ x_n² − 208 Σ n x_n²`, with `Σ x_n² → ∫ h²` (a Riemann sum).
On one dyadic window above the grid the aliasing integral is therefore at least `a log N/c⁸`:

* **Coercivity** (`horizon_layer_coercive`): for a nonzero `C²` window profile `h` there is `a > 0`
  such that along every schedule with `c_N ≥ 1`, `c_N/N → 0`, eventually
  `c_N⁻¹ ⟨W x, x⟩ ≥ κ Q(H) − ε + a log N/c_N⁸`.
* **The second-order term at the critical curve** (`horizon_layer_criticalCurve_sandwich`): along
  `c⁸/log N → K`, eventually `κ Q(H) + a/K − ε ≤ c⁻¹⟨W x, x⟩ ≤ κ Q(H) + b/K + ε`.
* **Subcritical positivity** (`eventually_horizon_pos_of_small_multiple`): every horizon block is
  eventually positive at every multiple `K < a/(κ max(0, −Q(H)))` of the critical curve.

The second-order term of the degeneration on a horizon window is Weil's form of the synthesized
test plus a coercive aliasing part of exact order `1/K`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory

variable {h : ℝ → ℝ} {A : ℝ}

/-! ### Lower bounds for the ingredients -/

/-- **Mean value from below.** -/
theorem integral_window_ge (N : ℕ) (x : ℕ → ℝ) (U : ℝ) :
    U * ∑ n ∈ Icc 1 N, x n ^ 2 - 208 * ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 ≤
      ∫ τ in U..(2 * U), ‖dirichletPoly N x τ‖ ^ 2 := by
  have h := RHTower.Sieve.dirichlet_meanValue_sharp_window N
    (fun i => (x ((i : ℕ) + 1) : ℂ)) U (2 * U)
  rw [sum_fin_norm_sq, sum_fin_mul_norm_sq, show 2 * U - U = U by ring] at h
  simp only [← dirichletPoly_eq_dirPoly] at h
  have := (abs_le.mp h).1
  linarith

/-- The tilted spline's transform is bounded below: `‖φ̂(u)‖² ≥ (sinh⁸ 1/64)(1 + |u|)^{−8}`. -/
theorem tiltedUnitSpline_lower (u : ℝ) :
    Real.sinh 1 ^ 8 / 64 * ((1 + |u|) ^ 8)⁻¹ ≤ ‖paperFT (cx tiltedUnitSpline) u‖ ^ 2 := by
  have h1 := norm_paperFT_tiltedUnitSpline_eq u
  have h2 := BiScaleUncertainty.ChebyshevGauge.le_norm_paperFT_splineProbe_ofReal (u / 8)
  have hq : 1 + (u / 8) ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hq0 : 0 < 1 + (u / 8) ^ 2 := by positivity
  have hs : 0 ≤ Real.sinh 1 := (Real.sinh_pos_iff.mpr one_pos).le
  have hge : (1 / 8) * (Real.sinh 1 ^ 4 / ((1 + |u|) ^ 2) ^ 2) ≤
      ‖paperFT (cx tiltedUnitSpline) u‖ := by
    rw [h1]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ h2) (by norm_num)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hq0.le hq 2)
  have hsq := pow_le_pow_left₀ (by positivity) hge 2
  calc Real.sinh 1 ^ 8 / 64 * ((1 + |u|) ^ 8)⁻¹
      = ((1 / 8) * (Real.sinh 1 ^ 4 / ((1 + |u|) ^ 2) ^ 2)) ^ 2 := by
        generalize 1 + |u| = q
        rw [div_eq_mul_inv (Real.sinh 1 ^ 4), mul_pow, mul_pow, inv_pow]
        ring
    _ ≤ _ := hsq

/-- The symbol from below: `ν_X(τ) ≥ (log(1 + |τ|/4) − 10)/(2π) − X²/π`. -/
theorem nuSymbol_ge {X : ℝ} (hX : 0 ≤ X) (τ : ℝ) :
    (Real.log (1 + |τ| / 4) - 10) / (2 * Real.pi) - X ^ 2 / Real.pi ≤ nuSymbol X τ := by
  have h1 := RHTower.mu_ge_log τ
  have h2 := RHTower.Littlewood.abs_PX_le hX τ
  unfold nuSymbol
  linarith [(abs_le.mp h2).1]

/-- The real Riemann-sum profile `h(log x)²/x`. -/
def sqProfile (h : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then h (Real.log x) ^ 2 / x else 0

theorem continuous_sqProfile (hh : Continuous h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    Continuous (sqProfile h) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge (0 : ℝ) x with hx | hx
  · have hev : sqProfile h =ᶠ[𝓝 x] fun t => h (Real.log t) ^ 2 / t :=
      (lt_mem_nhds hx).mono fun t ht => by simp only [sqProfile, if_pos ht]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((hh.continuousAt.comp (Real.continuousAt_log hx.ne')).pow 2).div continuousAt_id hx.ne'
  · have hev : sqProfile h =ᶠ[𝓝 x] fun _ => 0 := by
      refine (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht => ?_
      unfold sqProfile
      split_ifs with h0
      · have : Real.log t < -A := by rw [Real.log_lt_iff_lt_exp h0]; exact ht
        rw [hsupp _ (fun hm => by linarith [hm.1])]; simp
      · rfl
    exact ContinuousAt.congr continuousAt_const hev.symm

theorem sqProfile_eq_zero_of_notMem (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) 1) : sqProfile h x = 0 := by
  unfold sqProfile
  split_ifs with h0
  · have h1 : 1 < x := by by_contra hc; exact hx ⟨h0.le, not_lt.mp hc⟩
    rw [hsupp _ (fun hm => by linarith [hm.2, Real.log_pos h1])]; simp
  · rfl

theorem integral_sqProfile (hh : Continuous h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) : ∫ x, sqProfile h x = ∫ y, h y ^ 2 := by
  have hcont := continuous_sqProfile hh hsupp
  have hL : ∫ x, sqProfile h x = ∫ x in Real.exp (-A)..Real.exp 0, sqProfile h x := by
    rw [intervalIntegral.integral_of_le (Real.exp_le_exp.mpr (by linarith)),
      ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rcases lt_or_ge x (Real.exp (-A)) with h1 | h1
    · unfold sqProfile
      split_ifs with h0
      · have : Real.log x < -A := by rw [Real.log_lt_iff_lt_exp h0]; exact h1
        rw [hsupp _ (fun hm => by linarith [hm.1])]; simp
      · rfl
    · refine sqProfile_eq_zero_of_notMem hsupp fun hm => hx ⟨h1, ?_⟩
      rw [Real.exp_zero]; exact hm.2
  have hR : ∫ y, h y ^ 2 = ∫ y in (-A)..0, h y ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [hsupp y hy]; simp
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := -A) (b := 0) (f := Real.exp)
    (f' := Real.exp) (g := sqProfile h) (fun y _ => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn hcont
  rw [hL, hR, ← hsub]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [Function.comp_apply, sqProfile, if_pos (Real.exp_pos y), Real.log_exp, smul_eq_mul]
  field_simp

/-- **The mass of a horizon block**: `Σ x_n² → ∫ h²`. -/
theorem tendsto_sum_horizonWeights_sq (hh : Continuous h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2) atTop (𝓝 (∫ y, h y ^ 2)) := by
  rw [← integral_sqProfile hh hsupp hA]
  refine (RHTower.tendsto_riemannSum_Icc (continuous_sqProfile hh hsupp)
    fun x hx => sqProfile_eq_zero_of_notMem hsupp hx).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  rw [sqProfile, if_pos (div_pos hr0 hN0), horizonWeights, div_pow, Real.sq_sqrt hr0.le,
    Real.log_div hr0.ne' hN0.ne']
  field_simp

/-! ### Coercivity of the aliasing part -/

/-- On a window `[U, 2U]` above the grid the integrand is at least `w_min ν_min |D_x|²/N`. -/
theorem integral_window_symbol_ge {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) (L : ℝ) {U : ℝ}
    (hU : 0 < U) {Wm νm : ℝ}
    (hWm : Wm = Real.sinh 1 ^ 8 / 64 * (((1 + 2 * (c / N) * U)) ^ 8)⁻¹)
    (hνm : νm = (Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi) (hνm0 : 0 ≤ νm) :
    Wm * νm * ((∫ τ in U..(2 * U), ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2) / N) ≤
      ∫ τ in U..(2 * U), horizonSymbolIntegrand tiltedUnitSpline h c N (Real.exp L) τ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos (by linarith) hN0
  have hWm0 : 0 ≤ Wm := by rw [hWm]; positivity
  have hUle : U ≤ 2 * U := by linarith
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hUle
    (((continuous_norm_sq_dirichletPoly N (horizonWeights h N)).div_const _).const_mul _
      |>.intervalIntegrable _ _) ?_ fun τ hτ => ?_
  · exact (integrable_horizonSymbolIntegrand contDiff_tiltedUnitSpline tiltedUnitSpline_support h
      (by linarith) hN L).intervalIntegrable
  · have hτ0 : 0 < τ := lt_of_lt_of_le hU hτ.1
    have hl := tiltedUnitSpline_lower (c / N * τ)
    have hwt : Wm ≤ ‖paperFT (cx tiltedUnitSpline) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 := by
      rw [hWm]
      refine le_trans ?_ (by push_cast at hl ⊢; exact hl)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 8)
      rw [abs_of_pos (mul_pos hw hτ0)]
      nlinarith [hτ.2]
    have hν : νm ≤ nuSymbol (Real.exp L) τ := by
      refine le_trans ?_ (nuSymbol_ge (Real.exp_pos L).le τ)
      rw [hνm, abs_of_pos hτ0]
      gcongr
      exact hτ.1
    have hD : 0 ≤ ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N := by positivity
    simp only [horizonSymbolIntegrand]
    calc Wm * νm * (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)
        = Wm * (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) * νm := by ring
      _ ≤ ‖paperFT (cx tiltedUnitSpline) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) * nuSymbol (Real.exp L) τ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hwt hD) hν hνm0 (by positivity)

/-- Above the archimedean horizon the symbol integrand is nonnegative. -/
theorem symbol_nonneg_off_window (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) (L : ℝ) {T₀ : ℝ}
    (hT₀ : 4 * Real.exp (10 + 2 * Real.exp L ^ 2) ≤ T₀) :
    ∀ τ ∈ (Set.Icc (-T₀) T₀)ᶜ, 0 ≤ horizonSymbolIntegrand φ h c N (Real.exp L) τ := by
  intro τ hτ
  have hT0 : 0 < T₀ := lt_of_lt_of_le (by positivity) hT₀
  have hτT : T₀ < |τ| := by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hτ
    rcases hτ with hτ | hτ
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hν := nuSymbol_ge (Real.exp_pos L).le τ
  have hlog : 10 + 2 * Real.exp L ^ 2 ≤ Real.log (1 + |τ| / 4) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith
  have hν0 : 0 ≤ nuSymbol (Real.exp L) τ := by
    refine le_trans ?_ hν
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [sub_nonneg, div_le_div_iff₀ hpi (by positivity)]
    nlinarith
  simp only [horizonSymbolIntegrand]
  positivity

/-- A window above the grid carries less than the whole off-window integral. -/
theorem window_le_off_window {S : ℝ → ℝ} (hSi : Integrable S) {T₀ U : ℝ} (hT₀U : T₀ ≤ U)
    (hU : 0 < U) (hS0 : ∀ τ ∈ (Set.Icc (-T₀) T₀)ᶜ, 0 ≤ S τ) :
    ∫ τ in U..(2 * U), S τ ≤ ∫ τ in (Set.Icc (-T₀) T₀)ᶜ, S τ := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hsub : Set.Ioc U (2 * U) ⊆ (Set.Icc (-T₀) T₀)ᶜ := fun τ hτ => by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
    right; linarith [hτ.1]
  exact setIntegral_mono_set hSi.integrableOn
    ((ae_restrict_iff' measurableSet_Icc.compl).mpr (Eventually.of_forall hS0)) hsub.eventuallyLE

/-- The symbol on the window `[2^j N e^{−A}, ·]` is at least `log N/(4π)`. -/
theorem nuMin_ge {A X : ℝ} {N : ℕ} (hN : 1 ≤ N) (j : ℕ)
    (hlog : 2 * (A + 12 + 2 * X ^ 2) ≤ Real.log N) :
    Real.log N / (4 * Real.pi) ≤
      (Real.log (1 + 2 ^ j * (N * Real.exp (-A)) / 4) - 10) / (2 * Real.pi) - X ^ 2 / Real.pi := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogU : Real.log N - A - 2 ≤ Real.log (1 + 2 ^ j * (N * Real.exp (-A)) / 4) := by
    have h4 : Real.log 4 ≤ 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    calc Real.log N - A - 2 ≤ Real.log N - A - Real.log 4 + j * Real.log 2 := by
          have : 0 ≤ (j : ℝ) * Real.log 2 := by positivity
          linarith
      _ = Real.log (2 ^ j * (N * Real.exp (-A)) / 4) := by
          rw [Real.log_div (by positivity) (by norm_num),
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
          ring
      _ ≤ _ := Real.log_le_log (by positivity) (by linarith)
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_sub_div _ _ (by positivity) hpi.ne', le_div_iff₀ (by positivity)]
  have : Real.log N / (4 * Real.pi) * (2 * Real.pi * Real.pi) = Real.log N * Real.pi / 2 := by
    field_simp; ring
  rw [this]
  nlinarith

/-- The mean square of the block on one window above the grid. -/
theorem meanSquare_window_ge {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 0 < s)
    (hS1 : s / 2 < ∑ n ∈ Finset.Icc 1 N, horizonWeights h N n ^ 2) {j : ℕ}
    (hj : 832 * Bh ^ 2 * Real.exp A / s < 2 ^ j) :
    2 ^ j * Real.exp (-A) * s / 4 ≤
      (∫ τ in (2 ^ j * (N * Real.exp (-A)))..(2 * (2 ^ j * (N * Real.exp (-A)))),
        ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hMV := integral_window_ge N (horizonWeights h N) (2 ^ j * (N * Real.exp (-A)))
  have hS2 := sum_mul_horizonWeights_sq_le hB N (h := h)
  rw [le_div_iff₀ hN0]
  have hj' : 208 * Bh ^ 2 < 2 ^ j * Real.exp (-A) * s / 4 := by
    rw [div_lt_iff₀ hs] at hj
    have he : Real.exp A * Real.exp (-A) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-A)]
  have hU0 : 0 < 2 ^ j * ((N : ℝ) * Real.exp (-A)) := by positivity
  have hUS := mul_le_mul_of_nonneg_left hS1.le hU0.le
  nlinarith

/-- The atom weight on the window: `(1 + 2(c/N)U)^{−8} ≥ (q c)^{−8}`, `q = 1 + 2^{j+1}e^{−A}`. -/
theorem windowWeight_ge {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) (A : ℝ) (j : ℕ) :
    Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ * (c ^ (8 : ℝ))⁻¹ ≤
      Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c / N) * (2 ^ j * (N * Real.exp (-A)))) ^ 8)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcq : 1 + 2 * (c / N) * (2 ^ j * (N * Real.exp (-A))) ≤
      (1 + 2 ^ (j + 1) * Real.exp (-A)) * c := by
    have : 2 * (c / N) * (2 ^ j * (N * Real.exp (-A))) = 2 ^ (j + 1) * Real.exp (-A) * c := by
      field_simp; ring
    rw [this]
    nlinarith [Real.exp_pos (-A), pow_pos (two_pos (α := ℝ)) (j + 1)]
  have hpow : (c ^ (8 : ℝ)) = c ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow, mul_assoc, ← mul_inv, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
    hcq 8)) (by positivity)

/-- **The aliasing lower bound** on the off-window part of the symbol integral. -/
theorem aliasing_lower {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) (L : ℝ) {s : ℝ}
    (hs : 0 < s) (hS1 : s / 2 < ∑ n ∈ Finset.Icc 1 N, horizonWeights h N n ^ 2) {j : ℕ}
    (hj : 832 * Bh ^ 2 * Real.exp A / s < 2 ^ j)
    (hlog : 2 * (A + 12 + 2 * Real.exp L ^ 2) ≤ Real.log N)
    (hT : 4 * Real.exp (10 + 2 * Real.exp L ^ 2) ≤ N * Real.exp (-A)) :
    Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ * (1 / (4 * Real.pi)) *
        (2 ^ j * Real.exp (-A) * s / 4) * Real.log N / c ^ (8 : ℝ) ≤
      ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        horizonSymbolIntegrand tiltedUnitSpline h c N (Real.exp L) τ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : 0 < (N : ℝ) * Real.exp (-A) := by positivity
  set U : ℝ := 2 ^ j * ((N : ℝ) * Real.exp (-A)) with hU
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hTU : (N : ℝ) * Real.exp (-A) ≤ U := by rw [hU]; nlinarith
  have hU0 : 0 < U := by linarith
  have hSi := integrable_horizonSymbolIntegrand contDiff_tiltedUnitSpline tiltedUnitSpline_support
    h (by linarith : (0 : ℝ) < c) hN L
  have hwin := window_le_off_window hSi hTU hU0
    (symbol_nonneg_off_window tiltedUnitSpline h c N L hT)
  have hνm := nuMin_ge (X := Real.exp L) hN j hlog
  have hνm0 : 0 ≤ (Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi :=
    le_trans (by have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); positivity) hνm
  have hW := integral_window_symbol_ge (h := h) hc1 hN L hU0 rfl rfl hνm0
  have hD := meanSquare_window_ge (A := A) hB hN hs hS1 hj
  have hWt := windowWeight_ge hc1 hN A j
  refine le_trans ?_ (hW.trans hwin)
  have hcp : 0 < c ^ (8 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ * (1 / (4 * Real.pi)) *
        (2 ^ j * Real.exp (-A) * s / 4) * Real.log N / c ^ (8 : ℝ)
      = (Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ * (c ^ (8 : ℝ))⁻¹) *
          (Real.log N / (4 * Real.pi)) * (2 ^ j * Real.exp (-A) * s / 4) := by
        field_simp
    _ ≤ _ := mul_le_mul (mul_le_mul hWt hνm (by positivity) (by positivity)) hD
        (by positivity) (by positivity)

/-- The final arithmetic of the coercivity bound. -/
theorem final_assembly {M P P0 G G0 I2 Off a l cp ε : ℝ} (hM0 : 0 < M)
    (h1 : |M⁻¹ * P - M⁻¹ * (I2 * P0)| < ε / 2) (h2 : |M⁻¹ * G - M⁻¹ * (I2 * G0)| < ε / 2)
    (hal : a * l / cp ≤ Off) :
    I2 / M * (P0 + G0) - ε + a / M * l / cp ≤ P / M + M⁻¹ * (G + Off) := by
  have e1 := (abs_lt.mp h1).1
  have e2 := (abs_lt.mp h2).1
  have hMi : 0 < M⁻¹ := inv_pos.mpr hM0
  have h3 : M⁻¹ * (a * l / cp) ≤ M⁻¹ * Off := mul_le_mul_of_nonneg_left hal hMi.le
  have eq1 : a / M * l / cp = M⁻¹ * (a * l / cp) := by ring
  have eq2 : P / M = M⁻¹ * P := by ring
  have eq3 : I2 / M * (P0 + G0) = M⁻¹ * (I2 * P0) + M⁻¹ * (I2 * G0) := by ring
  rw [eq1, eq2, eq3, mul_add]
  linarith

/-- **Coercivity of the aliasing part.** For a nonzero `C²` window profile `h` there is `a > 0` such
that along every schedule with `c_N ≥ 1` and `c_N/N → 0`, eventually
`c_N⁻¹ ⟨W x, x⟩ ≥ κ Q(H) − ε + a log N/c_N⁸` (tilted spline). -/
theorem horizon_layer_coercive (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hpos : 0 < ∫ y, h y ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) - ε +
          a * Real.log N / c N ^ (8 : ℝ) ≤
        (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  set M := ∫ u, tiltedUnitSpline u ^ 2 with hM
  set L := 2 * (A + 1) with hL
  have hM0 : 0 < M := integral_tiltedUnitSpline_sq_pos
  obtain ⟨Bh, Lh, hB, hLip⟩ := exists_bound_lipschitz hh hsupp
  set s := ∫ y, h y ^ 2 with hs
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 832 * Bh ^ 2 * Real.exp A / s < 2 ^ j :=
    pow_unbounded_of_one_lt _ one_lt_two
  have hsh : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  set a₀ : ℝ := Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ *
    (1 / (4 * Real.pi)) * (2 ^ j * Real.exp (-A) * s / 4) with ha₀
  have ha₀0 : 0 < a₀ := by
    have : 0 < Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ :=
      mul_pos (div_pos (pow_pos hsh 8) (by norm_num)) (inv_pos.mpr (by positivity))
    rw [ha₀]; positivity
  refine ⟨a₀ / M, div_pos ha₀0 hM0, fun c hc1 hcN ε hε => ?_⟩
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hpole := tendsto_polePart contDiff_tiltedUnitSpline.continuous
    hasCompactSupport_tiltedUnitSpline hh.continuous hsupp hA hcN
  have hlow := tendsto_lowFrequency contDiff_tiltedUnitSpline tiltedUnitSpline_support hh hA hsupp
    hc0 hcN
  have hev1 := (hpole.const_mul M⁻¹).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hev2 := (hlow.const_mul M⁻¹).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hev3 := (tendsto_sum_horizonWeights_sq hh.continuous hsupp hA).eventually
    (lt_mem_nhds (half_lt_self hpos))
  have hev4 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 * (A + 12 + 2 * Real.exp L ^ 2)))
  have hev5 := (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos (-A))).eventually
    (eventually_ge_atTop (4 * Real.exp (10 + 2 * Real.exp L ^ 2)))
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_one hN0] at h1
    exact h1.le
  filter_upwards [hev1, hev2, hev3, hev4, hev5, hcle, eventually_ge_atTop 1] with
    N h1 h2 h3 h4 h5 h6 hN
  rw [Real.dist_eq] at h1 h2
  rw [horizonForm_eq contDiff_tiltedUnitSpline tiltedUnitSpline_support hM0 hsupp hA (hc0 N) hN h6,
    weilQuad_halfWeight_eq hh hsupp hA]
  have hal := aliasing_lower (A := A) hB (hc1 N) hN L hpos h3 hj h4 h5
  rw [← ha₀] at hal
  have hSi := integrable_horizonSymbolIntegrand contDiff_tiltedUnitSpline tiltedUnitSpline_support
    h (hc0 N) hN L
  rw [(integral_add_compl (s := Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
    measurableSet_Icc hSi).symm]
  exact final_assembly hM0 h1 h2 hal

/-- **The lower half at the critical curve.** Along `c⁸/log N → K`, eventually
`c⁻¹⟨W x, x⟩ ≥ κ Q(H) + a/K − ε`. -/
theorem horizon_layer_lower_criticalCurve (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hpos : 0 < ∫ y, h y ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ K : ℝ, 0 < K → Tendsto (fun N : ℕ => c N ^ (8 : ℝ) / Real.log N) atTop (𝓝 K) →
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
          a / K - ε ≤
        (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  obtain ⟨a, ha, hco⟩ := horizon_layer_coercive hh hA hsupp hpos
  refine ⟨a, ha, fun c hc1 hcN K hK hcrit ε hε => ?_⟩
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (8 : ℝ)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by simp only [inv_div]
  have hev := (hinv.const_mul a).eventually (lt_mem_nhds (show a * K⁻¹ - ε / 2 < a * K⁻¹ by
    linarith))
  filter_upwards [hco c hc1 hcN (ε / 2) (half_pos hε), hev] with N h1 h2
  have : a * Real.log N / c N ^ (8 : ℝ) = a * (Real.log N / c N ^ (8 : ℝ)) := by ring
  rw [div_eq_mul_inv a K]
  linarith

/-- **Subcritical positivity.** If `κ Q(H) + a/K > 0`, the horizon block is eventually positive at
the multiple `K` of the critical curve; every horizon block is positive at every sufficiently small
multiple. -/
theorem eventually_horizon_pos_of_small_multiple (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hpos : 0 < ∫ y, h y ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ K : ℝ, 0 < K → Tendsto (fun N : ℕ => c N ^ (8 : ℝ) / Real.log N) atTop (𝓝 K) →
      0 < (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
        a / K →
      ∀ᶠ N : ℕ in atTop, 0 < (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  obtain ⟨a, ha, hlow⟩ := horizon_layer_lower_criticalCurve hh hA hsupp hpos
  refine ⟨a, ha, fun c hc1 hcN K hK hcrit hgap => ?_⟩
  filter_upwards [hlow c hc1 hcN K hK hcrit _ (half_pos hgap)] with N hN
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
