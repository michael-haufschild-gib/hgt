import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Scaled smooth windows for short zero counts

The bump `Φ(u) = ϑ(1 − u²)` (`ϑ` the smooth transition) is smooth, even, `0 ≤ Φ ≤ 1`, vanishes for
`|u| ≥ 1` and has `Φ(0) = 1`.  Its rescaling `Φ_ℓ(u) = Φ(u/ℓ)` has `k`-th derivative
`Φ_ℓ^{(k)}(u) = Φ^{(k)}(u/ℓ)/ℓ^k` (`iteratedDeriv_scaled`), so

  `∫|Φ_ℓ^{(k)}| = ℓ^{1−k} ∫|Φ^{(k)}|`,   `∫(Φ_ℓ^{(k)})² = ℓ^{1−2k} ∫(Φ^{(k)})²`.

For the paper transform `ĥ(z) = ∫ h(u)e^{izu}du` of `Φ_ℓ` and of `Φ_ℓ′` on the real line:
* `|Φ̂_ℓ(y)| ≤ ℓA` and `|Φ̂_ℓ(y)| ≤ B₂/(ℓy²)`;
* `|(Φ_ℓ′)^(y)| ≤ A₁` and `|(Φ_ℓ′)^(y)| ≤ B₃/(ℓ²y²)`;
* `(Φ_ℓ′)^(z) = −iz·Φ̂_ℓ(z)`;
* Plancherel gives `∫|Φ̂_ℓ|² = 2πℓE` and `∫|(Φ_ℓ′)^|² = 2πF₁/ℓ`.

Here `A = ∫Φ`, `E = ∫Φ²`, `A₁ = ∫|Φ′|`, `F₁ = ∫Φ′²`, `B₂ = ∫|Φ″|`, `B₃ = ∫|Φ‴|`.  The windows
modulated by `e^{−iTu}` transform to `ĥ(z − T)` (`paperFT_window`).
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-! ## The bump -/

/-- The bump `Φ(u) = ϑ(1 − u²)`. -/
def bump (u : ℝ) : ℝ := Real.smoothTransition (1 - u ^ 2)

theorem contDiff_bump {n : ℕ∞} : ContDiff ℝ n bump :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem bump_nonneg (u : ℝ) : 0 ≤ bump u := Real.smoothTransition.nonneg _

theorem bump_le_one (u : ℝ) : bump u ≤ 1 := Real.smoothTransition.le_one _

theorem bump_eq_zero {u : ℝ} (hu : 1 ≤ |u|) : bump u = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 1 ≤ u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  linarith

theorem bump_zero : bump 0 = 1 := by
  simp [bump, Real.smoothTransition.one_of_one_le]

/-- Every iterated derivative of the bump vanishes for `|u| > 1`. -/
theorem iteratedDeriv_bump_eq_zero (k : ℕ) {u : ℝ} (hu : 1 < |u|) :
    iteratedDeriv k bump u = 0 := by
  have h : bump =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {v : ℝ | 1 < |v|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact bump_eq_zero (le_of_lt hv)
  rw [h.iteratedDeriv_eq]
  induction k with
  | zero => simp
  | succ k _ => simp

theorem contDiff_iteratedDeriv_bump (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (iteratedDeriv k bump) := by
  rw [iteratedDeriv_eq_iterate]
  exact (ContDiff.iterate_deriv k (contDiff_bump (n := ⊤))).of_le (by exact_mod_cast le_top)

/-! ## Rescaling -/

/-- `Φ_ℓ^{(k)}(u) = Φ^{(k)}(u/ℓ)/ℓ^k`. -/
def sc (ℓ : ℝ) (k : ℕ) (u : ℝ) : ℝ := iteratedDeriv k bump (u / ℓ) / ℓ ^ k

theorem iteratedDeriv_scaled (ℓ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun u => bump (u / ℓ)) = sc ℓ k := by
  have h := iteratedDeriv_comp_const_mul (n := k) (f := bump) (contDiff_bump (n := k)) ℓ⁻¹
  have e : (fun u => bump (u / ℓ)) = fun u => bump (ℓ⁻¹ * u) := by
    funext u; rw [div_eq_inv_mul]
  rw [e, h]
  funext u
  simp only [sc, div_eq_inv_mul, inv_pow]

theorem sc_zero (ℓ u : ℝ) : sc ℓ 0 u = bump (u / ℓ) := by simp [sc]

theorem contDiff_sc (ℓ : ℝ) (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (sc ℓ k) := by
  have h : sc ℓ k = fun u => iteratedDeriv k bump (u / ℓ) * (ℓ ^ k)⁻¹ := by
    funext u; simp [sc, div_eq_mul_inv]
  rw [h]
  exact ((contDiff_iteratedDeriv_bump k).comp (contDiff_id.div_const ℓ)).mul contDiff_const

theorem hasDerivAt_sc (ℓ : ℝ) (k : ℕ) (u : ℝ) : HasDerivAt (sc ℓ k) (sc ℓ (k + 1) u) u := by
  have hd : Differentiable ℝ (sc ℓ k) := (contDiff_sc ℓ k (n := 1)).differentiable (by norm_num)
  have he : deriv (sc ℓ k) = sc ℓ (k + 1) := by
    rw [← iteratedDeriv_scaled, ← iteratedDeriv_scaled, iteratedDeriv_succ]
  rw [← he]
  exact (hd u).hasDerivAt

theorem sc_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) {u : ℝ} (hu : ℓ < |u|) : sc ℓ k u = 0 := by
  have h : 1 < |u / ℓ| := by
    rw [abs_div, abs_of_pos hℓ, lt_div_iff₀ hℓ, one_mul]; exact hu
  simp [sc, iteratedDeriv_bump_eq_zero k h]

/-- `∫ g(u/ℓ) du = ℓ ∫ g` for `ℓ > 0`. -/
theorem integral_comp_div_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ → ℝ) :
    ∫ u, g (u / ℓ) = ℓ * ∫ v, g v := by
  rw [Measure.integral_comp_div g ℓ, abs_of_pos hℓ, smul_eq_mul]

theorem integral_abs_sc {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ∫ u, |sc ℓ k u| = ℓ ^ (1 - (k : ℤ)) * ∫ v, |iteratedDeriv k bump v| := by
  have h : (fun u => |sc ℓ k u|) = fun u => |iteratedDeriv k bump (u / ℓ)| * (ℓ ^ k)⁻¹ := by
    funext u
    rw [sc, abs_div, abs_of_pos (pow_pos hℓ k), div_eq_mul_inv]
  rw [h, integral_mul_const, integral_comp_div_pos hℓ (fun v => |iteratedDeriv k bump v|),
    zpow_sub₀ hℓ.ne', zpow_one, zpow_natCast]
  field_simp

theorem integral_sq_sc {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ∫ u, sc ℓ k u ^ 2 = ℓ ^ (1 - 2 * (k : ℤ)) * ∫ v, iteratedDeriv k bump v ^ 2 := by
  have h : (fun u => sc ℓ k u ^ 2) = fun u => iteratedDeriv k bump (u / ℓ) ^ 2 * ((ℓ ^ k) ^ 2)⁻¹ := by
    funext u
    rw [sc, div_pow, div_eq_mul_inv]
  rw [h, integral_mul_const, integral_comp_div_pos hℓ (fun v => iteratedDeriv k bump v ^ 2),
    zpow_sub₀ hℓ.ne', zpow_one, zpow_mul, zpow_natCast]
  field_simp
  ring

/-! ## Complex windows -/

/-- The complex window `u ↦ Φ_ℓ^{(k)}(u)`. -/
def cb (ℓ : ℝ) (k : ℕ) (u : ℝ) : ℂ := ((sc ℓ k u : ℝ) : ℂ)

theorem contDiff_cb (ℓ : ℝ) (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (cb ℓ k) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_sc ℓ k)

theorem deriv_cb (ℓ : ℝ) (k : ℕ) : deriv (cb ℓ k) = cb ℓ (k + 1) := by
  funext u
  exact ((hasDerivAt_sc ℓ k u).ofReal_comp).deriv

theorem cb_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) {u : ℝ} (hu : ℓ < |u|) : cb ℓ k u = 0 := by
  simp [cb, sc_eq_zero hℓ k hu]

theorem cb_support {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : ∀ u, cb ℓ k u ≠ 0 → |u| ≤ ℓ := by
  intro u hu
  by_contra h
  exact hu (cb_eq_zero hℓ k (not_le.mp h))

theorem hasCompactSupport_cb {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : HasCompactSupport (cb ℓ k) :=
  hasCompactSupport_of_support_subset_abs (cb_support hℓ k)

theorem integrable_cb {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : Integrable (cb ℓ k) :=
  (contDiff_cb ℓ k (n := 0)).continuous.integrable_of_hasCompactSupport (hasCompactSupport_cb hℓ k)

theorem integral_norm_cb {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ∫ u, ‖cb ℓ k u‖ = ℓ ^ (1 - (k : ℤ)) * ∫ v, |iteratedDeriv k bump v| := by
  simp only [cb, Complex.norm_real, Real.norm_eq_abs]
  exact integral_abs_sc hℓ k

/-- `(Φ_ℓ′)^(z) = −iz·Φ̂_ℓ(z)`. -/
theorem paperFT_cb_succ {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (z : ℂ) :
    paperFT (cb ℓ (k + 1)) z = -(I * z) * paperFT (cb ℓ k) z := by
  rw [← deriv_cb]
  exact paperFT_deriv (contDiff_cb ℓ k) (hasCompactSupport_cb hℓ k) z

/-- `|ĥ(y)| ≤ ∫|h|` on the real line. -/
theorem norm_paperFT_cb_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (y : ℝ) :
    ‖paperFT (cb ℓ k) y‖ ≤ ℓ ^ (1 - (k : ℤ)) * ∫ v, |iteratedDeriv k bump v| := by
  have h := norm_paperFT_le (integrable_cb hℓ k) (cb_support hℓ k) (y : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at h
  rw [← integral_norm_cb hℓ k]
  exact h

/-- `|ĥ(y)| ≤ ∫|h″|/y²` on the real line. -/
theorem norm_paperFT_cb_le_div {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    ‖paperFT (cb ℓ k) y‖ ≤
      (ℓ ^ (1 - ((k + 2 : ℕ) : ℤ)) * ∫ v, |iteratedDeriv (k + 2) bump v|) / y ^ 2 := by
  have h := norm_paperFT_le_div (contDiff_cb ℓ k) (cb_support hℓ k)
    (z := (y : ℂ)) (by exact_mod_cast hy)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [deriv_cb, deriv_cb, integral_norm_cb hℓ (k + 1 + 1)] at h
  exact h

/-- **Plancherel for the windows.** -/
theorem integral_norm_sq_paperFT_cb {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ∫ τ : ℝ, ‖paperFT (cb ℓ k) τ‖ ^ 2 =
      2 * Real.pi * (ℓ ^ (1 - 2 * (k : ℤ)) * ∫ v, iteratedDeriv k bump v ^ 2) := by
  have hts : tsupport (cb ℓ k) ⊆ Icc (-ℓ) ℓ := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have := cb_support hℓ k u hu
    exact abs_le.mp this
  rw [integral_norm_sq_paperFT_eq (contDiff_cb ℓ k) hts, ← integral_sq_sc hℓ k]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp [cb, Complex.norm_real, sq_abs]

/-! ## Modulated windows -/

/-- The window `Φ_ℓ^{(k)}(u) e^{−iTu}`. -/
def window (ℓ T : ℝ) (k : ℕ) (u : ℝ) : ℂ := cb ℓ k u * cexp (-(I * T * u))

theorem paperFT_window (ℓ T : ℝ) (k : ℕ) (z : ℂ) :
    paperFT (window ℓ T k) z = paperFT (cb ℓ k) (z - T) := by
  simp only [paperFT, window]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem contDiff_window (ℓ T : ℝ) (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (window ℓ T k) := by
  have h : ContDiff ℝ n (fun u : ℝ => -(I * (T : ℂ) * (u : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  exact (contDiff_cb ℓ k).mul h.cexp

theorem tsupport_window {ℓ : ℝ} (hℓ : 0 < ℓ) (T : ℝ) (k : ℕ) :
    tsupport (window ℓ T k) ⊆ Icc (-((2 * ℓ) / 2)) ((2 * ℓ) / 2) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have hne : cb ℓ k u ≠ 0 := by
    intro h; apply hu; simp [window, h]
  have := cb_support hℓ k u hne
  rw [show 2 * ℓ / 2 = ℓ by ring]
  exact abs_le.mp this

end

end RHTower.Littlewood
