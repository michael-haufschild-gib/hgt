import GaloisForLFunctions.HagedornBootstrap.TanhGaussianFloor
import GaloisForLFunctions.RHTower.LegStripEdge
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The `U(1)^c` twin: sheet map, tanh law, Curie point and the band offset

For theories with `U(1)^c` currents the bootstrap functionals are radial `−1` Fourier
eigenfunctions on `ℝ^{2c}`. At large `c` they are WKB sums of characters, and the Fourier transform
acts on the local data `(ξ, τ)` (position `ξ = Δ/c`, local modular parameter `τ`) by the

* **sheet map** `Ŝ(ξ, τ) = (τ²ξ + τ/(2πi), −1/τ)`, an involution. In the coordinates
  `ρ = i/(2πξ) − τ`, `w = π²ξρ` it becomes the affine involution `(ρ, w) ↦ (−1/ρ, iπ/2 − w)`;
* the invariant curves are graphs `ρ = F(w)` with `F(w + iπ/2) = 1/F(w)`, solved by `F = tanh`;
* on the real axis this is the **Curie–Weiss law** `ρ = tanh(π²ξρ)`: a positive density of double
  zeros exists iff `ξ > 1/π²` (the slope `π²` of the `U(1)^c` bound), and the density obeys the
  mean-field floor `ρ² ≥ 3(k − 1)/k³`, `k = π²ξ`;
* **the band offset** `Δ_n = n + c/8` deep in the band rests on
  `∫₀¹ artanh(ρ)/ρ dρ = π²/8`, which follows from the corpus odd Basel sum;
* the `S`-image of the vacuum is the continuum `ρ₀(Δ) = (2π)^c Δ^{c−1}/Γ(c)`:
  `∫₀^∞ ρ₀(Δ) e^{−2πβΔ} dΔ = β^{−c}`.
-/

noncomputable section

open Real Set MeasureTheory

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The sheet map -/

/-- The sheet map `(ξ, τ) ↦ (τ²ξ + τ/(2πi), −1/τ)`. -/
def sheetMap (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.2 ^ 2 * p.1 + p.2 / (2 * π * Complex.I), -1 / p.2)

/-- **The sheet map is an involution.** -/
theorem sheetMap_sheetMap {p : ℂ × ℂ} (hτ : p.2 ≠ 0) : sheetMap (sheetMap p) = p := by
  obtain ⟨ξ, τ⟩ := p
  simp only at hτ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [sheetMap, Prod.mk.injEq]
  constructor
  · field_simp
    ring
  · field_simp

/-- The density coordinate `ρ = i/(2πξ) − τ`. -/
def sheetRho (p : ℂ × ℂ) : ℂ := Complex.I / (2 * π * p.1) - p.2

/-- The affine coordinate `w = π²ξρ`. -/
def sheetW (p : ℂ × ℂ) : ℂ := π ^ 2 * p.1 * sheetRho p

/-- With `τ = i/(2πξ) − ρ`, the image position is `ξ' = −ρξτ`. -/
theorem sheetMap_fst {ξ ρ : ℂ} (hξ : ξ ≠ 0) :
    let τ := Complex.I / (2 * π * ξ) - ρ
    (sheetMap (ξ, τ)).1 = -(ρ * ξ * τ) := by
  intro τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero
  have hinv : 1 / (2 * π * Complex.I) = -Complex.I / (2 * π) := by
    rw [div_eq_div_iff hI (mul_ne_zero two_ne_zero hπ)]
    linear_combination (2 * (π : ℂ)) * Complex.I_sq
  have hτξ : τ * ξ = Complex.I / (2 * π) - ρ * ξ := by
    simp only [τ]; field_simp
  simp only [sheetMap]
  calc τ ^ 2 * ξ + τ / (2 * π * Complex.I) = τ * (τ * ξ + 1 / (2 * π * Complex.I)) := by ring
    _ = τ * (Complex.I / (2 * π) - ρ * ξ + -Complex.I / (2 * π)) := by rw [hτξ, hinv]
    _ = -(ρ * ξ * τ) := by ring

/-- **In the coordinates `(ρ, w)` the sheet map is `(ρ, w) ↦ (−1/ρ, iπ/2 − w)`.** -/
theorem sheetMap_rho_w {ξ ρ : ℂ} (hξ : ξ ≠ 0) (hρ : ρ ≠ 0)
    (hτ : Complex.I / (2 * π * ξ) - ρ ≠ 0) :
    let τ := Complex.I / (2 * π * ξ) - ρ
    sheetRho (sheetMap (ξ, τ)) = -1 / ρ ∧
      sheetW (sheetMap (ξ, τ)) = π * Complex.I / 2 - π ^ 2 * ξ * ρ := by
  intro τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 := sheetMap_fst (ρ := ρ) hξ
  simp only at h1
  have hξ' : ρ * ξ * τ ≠ 0 := mul_ne_zero (mul_ne_zero hρ hξ) hτ
  have hkey : 2 * π * ξ * τ = Complex.I - 2 * π * ξ * ρ := by
    simp only [τ]; field_simp
  have hrho : sheetRho (sheetMap (ξ, τ)) = -1 / ρ := by
    unfold sheetRho
    rw [h1]
    simp only [sheetMap]
    rw [div_sub_div _ _ (by simpa using mul_ne_zero (mul_ne_zero two_ne_zero hπ) (neg_ne_zero.mpr hξ')) hτ,
      div_eq_div_iff (mul_ne_zero (by simpa using mul_ne_zero (mul_ne_zero two_ne_zero hπ)
        (neg_ne_zero.mpr hξ')) hτ) hρ]
    linear_combination (-(ρ * τ)) * hkey
  refine ⟨hrho, ?_⟩
  unfold sheetW
  rw [hrho, h1]
  field_simp
  linear_combination (-(π : ℂ) / 2) * hkey

/-! ### The tanh functional equation -/

/-- **`tanh(w + iπ/2) = 1/tanh w`.** -/
theorem tanh_add_pi_half_I (w : ℂ) :
    Complex.tanh (w + π / 2 * Complex.I) = (Complex.tanh w)⁻¹ := by
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh, Complex.sinh_add,
    Complex.cosh_add, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_div, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two, inv_div]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, zero_add, one_mul]
  rw [mul_div_mul_right _ _ Complex.I_ne_zero]

/-- The invariant curve: `F(iπ/2 − w) F(w) = −1` for the odd solution `F = tanh`. -/
theorem tanh_reflection (w : ℂ) (hw : Complex.tanh w ≠ 0) :
    Complex.tanh (π / 2 * Complex.I - w) * Complex.tanh w = -1 := by
  have h := tanh_add_pi_half_I (-w)
  rw [Complex.tanh_neg] at h
  rw [show (π : ℂ) / 2 * Complex.I - w = -w + π / 2 * Complex.I by ring, h, inv_neg]
  field_simp

/-! ### The Curie point -/

theorem tanh_lt_self {x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  have h1 := GaloisForLFunctions.HTGeometry.tanh_le_self hx.le
  rcases h1.lt_or_eq with h | h
  · exact h
  · -- `tanh x = x` is impossible for `x > 0`: the cubic floor is not saturated
    exfalso
    have hc : Real.tanh x < x := by
      rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos x)]
      have := GaloisForLFunctions.HTGeometry.sinh_le_mul_cosh hx.le
      -- strict: `sinh x < x cosh x` for `x > 0`
      have hd : ∀ y, HasDerivAt (fun y => y * Real.cosh y - Real.sinh y) (y * Real.sinh y) y := by
        intro y
        refine ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y) |>.sub (Real.hasDerivAt_sinh y)).congr_deriv ?_
        simp
      have hmono : StrictMonoOn (fun y => y * Real.cosh y - Real.sinh y) (Ici 0) := by
        apply strictMonoOn_of_deriv_pos (convex_Ici 0)
        · exact fun y _ => (hd y).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Ici] at hy
          rw [(hd y).deriv]
          exact mul_pos hy (Real.sinh_pos_iff.mpr hy)
      have := hmono Set.self_mem_Ici (mem_Ici.mpr hx.le) hx
      simp at this
      linarith
    linarith
  
/-- **The Curie point.** For `k > 0`, `ρ = tanh(kρ)` has a positive solution iff `k > 1`. -/
theorem exists_pos_tanh_fixed_iff {k : ℝ} (hk : 0 < k) :
    (∃ ρ : ℝ, 0 < ρ ∧ Real.tanh (k * ρ) = ρ) ↔ 1 < k := by
  constructor
  · rintro ⟨ρ, hρ, hfix⟩
    by_contra hle
    push Not at hle
    have := tanh_lt_self (mul_pos hk hρ)
    nlinarith
  · intro hk1
    -- `g(ρ) = tanh(kρ) − ρ` is positive near `0⁺` and negative at `1`
    set ρ0 := min (1 / 2) (Real.sqrt (3 * (k - 1) / k ^ 3) / 2) with hρ0
    have hpos : 0 < 3 * (k - 1) / k ^ 3 := by have : 0 < k - 1 := by linarith
                                              positivity
    have hρ0pos : 0 < ρ0 := lt_min (by norm_num) (by have := Real.sqrt_pos.mpr hpos; linarith)
    have hρ0le : ρ0 ≤ Real.sqrt (3 * (k - 1) / k ^ 3) / 2 := min_le_right _ _
    have hsq : ρ0 ^ 2 < 3 * (k - 1) / k ^ 3 := by
      have h2 : ρ0 < Real.sqrt (3 * (k - 1) / k ^ 3) := by
        have := Real.sqrt_pos.mpr hpos; linarith
      have := pow_lt_pow_left₀ h2 hρ0pos.le (by norm_num : (2 : ℕ) ≠ 0)
      rwa [Real.sq_sqrt hpos.le] at this
    have hg0 : 0 < Real.tanh (k * ρ0) - ρ0 := by
      have hcub := sub_cube_div_three_le_tanh (mul_pos hk hρ0pos).le
      have : k ^ 3 * ρ0 ^ 2 < 3 * (k - 1) := by
        rw [lt_div_iff₀ (by positivity)] at hsq; linarith
      nlinarith
    have hg1 : Real.tanh (k * 1) - 1 < 0 := by linarith [Real.tanh_lt_one (k * 1)]
    have htanh : Continuous fun ρ : ℝ => Real.tanh (k * ρ) := by
      simp_rw [Real.tanh_eq_sinh_div_cosh]
      exact Continuous.div (by fun_prop) (by fun_prop) (fun x => (Real.cosh_pos _).ne')
    have hcont : ContinuousOn (fun ρ => Real.tanh (k * ρ) - ρ) (Icc ρ0 1) :=
      (htanh.sub continuous_id).continuousOn
    have hρ01 : ρ0 ≤ 1 := (min_le_left _ _).trans (by norm_num)
    obtain ⟨ρ, hρ, hroot⟩ := intermediate_value_Icc' hρ01 hcont ⟨hg1.le, hg0.le⟩
    exact ⟨ρ, hρ0pos.trans_le hρ.1, by simpa [sub_eq_zero] using hroot⟩

/-- **The `U(1)^c` slope:** a positive band density exists at `ξ` iff `ξ > 1/π²`. -/
theorem curie_point {ξ : ℝ} (hξ : 0 < ξ) :
    (∃ ρ : ℝ, 0 < ρ ∧ ρ = Real.tanh (π ^ 2 * ξ * ρ)) ↔ 1 / π ^ 2 < ξ := by
  have hk : 0 < π ^ 2 * ξ := by positivity
  have := exists_pos_tanh_fixed_iff hk
  rw [div_lt_iff₀ (by positivity), mul_comm] at *
  constructor
  · rintro ⟨ρ, hρ, h⟩; exact this.mp ⟨ρ, hρ, h.symm⟩
  · intro h; obtain ⟨ρ, hρ, h'⟩ := this.mpr h; exact ⟨ρ, hρ, h'.symm⟩

/-- **Mean-field floor:** a positive solution of `ρ = tanh(kρ)` has `k³ρ² ≥ 3(k − 1)`. -/
theorem curieWeiss_floor {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) (hfix : Real.tanh (k * ρ) = ρ) :
    3 * (k - 1) ≤ k ^ 3 * ρ ^ 2 := by
  have hcub := sub_cube_div_three_le_tanh (mul_pos hk hρ).le
  rw [hfix] at hcub
  have : ρ * (3 * (k - 1) - k ^ 3 * ρ ^ 2) ≤ 0 := by nlinarith
  nlinarith

/-! ### The band offset `c/8` -/

theorem artanh_eq_half_log {x : ℝ} (h : |x| < 1) :
    Real.artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  have h1 : 0 < 1 + x := by linarith [(abs_lt.mp h).1]
  have h2 : 0 < 1 - x := by linarith [(abs_lt.mp h).2]
  rw [Real.artanh, Real.log_sqrt (by positivity), Real.log_div h1.ne' h2.ne']

/-- `artanh(ρ)/ρ = Σ ρ^{2k}/(2k + 1)` on `(0, 1)`. -/
theorem hasSum_artanh_div {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    HasSum (fun k : ℕ => ρ ^ (2 * k) / (2 * k + 1)) (Real.artanh ρ / ρ) := by
  have habs : |ρ| < 1 := by rw [abs_of_pos h0]; exact h1
  have hs := (Real.hasSum_log_sub_log_of_abs_lt_one habs).div_const (2 * ρ)
  have e : (fun k : ℕ => ρ ^ (2 * k) / (2 * k + 1)) =
      fun k : ℕ => 2 * (1 / (2 * (k : ℝ) + 1)) * ρ ^ (2 * k + 1) / (2 * ρ) := by
    funext k; rw [pow_succ]; field_simp
  rw [e, artanh_eq_half_log habs, div_div]
  exact hs

/-- **`∫₀¹ artanh(ρ)/ρ dρ = π²/8`**, from the corpus odd Basel sum. -/
theorem integral_artanh_div : ∫ ρ in (0 : ℝ)..1, Real.artanh ρ / ρ = π ^ 2 / 8 := by
  set F : ℕ → ℝ → ℝ := fun k ρ => ρ ^ (2 * k) / (2 * k + 1) with hF
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioo 0 1)) := fun k =>
    (Continuous.integrableOn_Ioc (by simp only [hF]; fun_prop)).mono_set Ioo_subset_Ioc_self
  have hval : ∀ k, ∫ ρ in Ioo (0 : ℝ) 1, F k ρ = 1 / (2 * k + 1) ^ 2 := by
    intro k
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    simp only [hF]
    rw [intervalIntegral.integral_div, integral_pow]
    push_cast
    field_simp
    ring
  have hnorm : ∀ k, ∫ ρ in Ioo (0 : ℝ) 1, ‖F k ρ‖ = ∫ ρ in Ioo (0 : ℝ) 1, F k ρ := fun k => by
    refine setIntegral_congr_fun measurableSet_Ioo (fun ρ hρ => ?_)
    exact Real.norm_of_nonneg (by simp only [hF]; have := hρ.1.le; positivity)
  have hbasel := RHTower.hasSum_odd_basel
  have hsum : HasSum (fun k => ∫ ρ in Ioo (0 : ℝ) 1, F k ρ) (π ^ 2 / 8) := by
    simp_rw [hval]; exact hbasel
  have hswap := integral_tsum_of_summable_integral_norm hint (by simp_rw [hnorm]; exact hsum.summable)
  rw [hsum.tsum_eq] at hswap
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hswap]
  refine setIntegral_congr_fun measurableSet_Ioo (fun ρ hρ => ?_)
  exact (hasSum_artanh_div hρ.1 hρ.2).tsum_eq.symm

/-- **The band offset:** `(1/π²)∫₀¹ artanh(ρ)/ρ dρ = 1/8`, the `c/8` in `Δ_n = n + c/8`. -/
theorem band_offset : 1 / π ^ 2 * ∫ ρ in (0 : ℝ)..1, Real.artanh ρ / ρ = 1 / 8 := by
  rw [integral_artanh_div]
  have : π ^ 2 ≠ 0 := by positivity
  field_simp

/-! ### The vacuum continuum of the twin -/

/-- **`S`-image of the vacuum:** `∫₀^∞ (2π)^c Δ^{c−1}/Γ(c) e^{−2πβΔ} dΔ = β^{−c}`. -/
theorem laplace_twin_vacuum {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    ∫ Δ in Ioi 0, (2 * π) ^ c * Δ ^ (c - 1) / Real.Gamma c * Real.exp (-(2 * π * β * Δ)) =
      β ^ (-c) := by
  have hr : 0 < 2 * π * β := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hc hr
  have hΓ : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have e : (fun Δ => (2 * π) ^ c * Δ ^ (c - 1) / Real.Gamma c * Real.exp (-(2 * π * β * Δ))) =
      fun Δ => (2 * π) ^ c / Real.Gamma c * (Δ ^ (c - 1) * Real.exp (-(2 * π * β * Δ))) := by
    funext Δ; ring
  rw [e, integral_const_mul, h, Real.div_rpow (by norm_num) hr.le, Real.one_rpow,
    Real.mul_rpow (by positivity) hβ.le, Real.rpow_neg hβ.le]
  have : (2 * π) ^ c ≠ 0 := by positivity
  field_simp

end GaloisForLFunctions.HagedornBootstrap
