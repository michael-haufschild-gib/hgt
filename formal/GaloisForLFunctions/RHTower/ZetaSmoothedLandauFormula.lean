import Zeta23.Final
import Zeta23.Poisson.PaperFT

/-!
# A smoothed Landau formula over all zeros of `ζ`

For a `C²` profile `w` supported in `[−1, 1]`, a height scale `T` and an integer `x ≥ 2`, the
Landau test `k(u) = T·w(T(u − log x))` has transform `h_k(z) = x^{iz}·ŵ(z/T)`
(`paperFT_landauTest`), so Weil's explicit formula (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`) reads

`Σ_ρ m_ρ x^{ρ − ½} ŵ(γ_ρ/T) = h_k(i/2) + h_k(−i/2) − T w(0) Λ(x)/√x + (Gamma term)`,

with `γ_ρ = (ρ − ½)/i`.  Only `n = x` survives in the prime sum once `T ≥ x + 2`
(`primeSum_landauTest`), and the pole terms are at most `2e·√x·‖w‖₁` (`norm_pole_landauTest_le`).
-/

open Complex MeasureTheory Real
open scoped Real

noncomputable section

namespace RHTower

open Zeta23

/-- The Landau test `u ↦ T·w(T(u − y))`: the profile `w` dilated to width `1/T` and centred at `y`. -/
def landauTest (w : ℝ → ℂ) (T y : ℝ) : ℝ → ℂ := fun u => (T : ℂ) * w (T * (u - y))

/-- `h_k(z) = e^{izy} ŵ(z/T)` for the Landau test. -/
theorem paperFT_landauTest (w : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (y : ℝ) (z : ℂ) :
    paperFT (landauTest w T y) z = Complex.exp (I * z * y) * paperFT w (z / T) := by
  unfold paperFT landauTest
  have hshift : (∫ u : ℝ, (T : ℂ) * w (T * (u - y)) * Complex.exp (I * z * u)) =
      ∫ u : ℝ, (T : ℂ) * w (T * u) * Complex.exp (I * z * (u + y)) := by
    rw [← integral_sub_right_eq_self (fun u : ℝ => (T : ℂ) * w (T * u) *
      Complex.exp (I * z * ((u : ℂ) + y))) y]
    congr 1; funext u
    simp only [ofReal_sub, sub_add_cancel]
  have hsplit : (fun u : ℝ => (T : ℂ) * w (T * u) * Complex.exp (I * z * ((u : ℂ) + y))) =
      fun u : ℝ => Complex.exp (I * z * y) *
        ((T : ℂ) * (fun v : ℝ => w v * Complex.exp (I * (z / T) * v)) (T * u)) := by
    funext u
    have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    simp only [ofReal_mul]
    rw [show I * z * ((u : ℂ) + y) = I * z * y + I * (z / T) * ((T : ℂ) * u) by field_simp; ring,
      Complex.exp_add]
    ring
  rw [hshift, hsplit, integral_const_mul, integral_const_mul,
    Measure.integral_comp_mul_left (fun v : ℝ => w v * Complex.exp (I * (z / T) * v)) T]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hT), Complex.real_smul, ← mul_assoc]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  rw [mul_inv_cancel₀ hT0, one_mul]

/-- The Landau test vanishes unless `|T(u − y)| ≤ 1`. -/
lemma landauTest_eq_zero {w : ℝ → ℂ} (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) {T y u : ℝ}
    (h : 1 < |T * (u - y)|) : landauTest w T y u = 0 := by
  unfold landauTest
  by_contra hne
  have := hsupp _ (right_ne_zero_of_mul hne)
  linarith

/-- `log(n/x)` is at least `1/(x + 1)` in size for integers `n ≠ x`, `n, x ≥ 1`. -/
lemma one_div_le_abs_log_sub_log {n x : ℕ} (hn : 1 ≤ n) (hx : 1 ≤ x) (hne : n ≠ x) :
    1 / ((x : ℝ) + 1) ≤ |Real.log n - Real.log x| := by
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hne with h | h
  · -- `n ≤ x − 1`: `log x − log n ≥ log(x/(x−1)) ≥ 1/x`
    have hle : (n : ℝ) + 1 ≤ x := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by
      have := Real.log_le_log (by linarith) (show (n : ℝ) ≤ x by linarith); linarith)]
    have hlog : Real.log ((n : ℝ) / x) ≤ (n : ℝ) / x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have h1 : (n : ℝ) / x - 1 ≤ -(1 / x) := by
      rw [div_sub_one (by linarith), neg_div', div_le_div_iff_of_pos_right (by linarith)]; linarith
    have h2 : 1 / ((x : ℝ) + 1) ≤ 1 / x := one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  · -- `n ≥ x + 1`: `log n − log x ≥ log((x+1)/x) ≥ 1/(x+1)`
    have hle : (x : ℝ) + 1 ≤ n := by exact_mod_cast h
    rw [abs_of_nonneg (by
      have := Real.log_le_log (by linarith) (show (x : ℝ) ≤ n by linarith); linarith)]
    have hlog : Real.log ((x : ℝ) / n) ≤ (x : ℝ) / n - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have h1 : (x : ℝ) / n - 1 ≤ -(1 / ((x : ℝ) + 1)) := by
      rw [div_sub_one (by linarith), neg_div', div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith

/-- **The prime sum of the Landau test**: for an integer `x ≥ 2` and `T ≥ x + 2`, only `n = x` survives:
`Σ_n Λ(n) n^{−1/2}(k(log n) + k(−log n)) = T w(0) Λ(x)/√x`. -/
theorem primeSum_landauTest {w : ℝ → ℂ} (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) {x : ℕ} (hx : 2 ≤ x)
    {T : ℝ} (hT : (x : ℝ) + 2 ≤ T) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (landauTest w T (Real.log x) (Real.log n) + landauTest w T (Real.log x) (-Real.log n)))
      = ((ArithmeticFunction.vonMangoldt x / Real.sqrt x : ℝ) : ℂ) * ((T : ℂ) * w 0) := by
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- the reflected point never meets the support
  have hneg : ∀ n : ℕ, landauTest w T (Real.log x) (-Real.log n) = 0 := by
    intro n
    apply landauTest_eq_zero hsupp
    have hn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [show T * (-Real.log n - Real.log x) = -(T * (Real.log n + Real.log x)) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
    nlinarith
  rw [tsum_eq_single x]
  · rw [hneg, add_zero]
    unfold landauTest
    simp
  · intro n hn
    rw [hneg, add_zero]
    by_cases hn0 : n = 0
    · subst hn0; simp
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    rw [landauTest_eq_zero hsupp, mul_zero]
    have hgap := one_div_le_abs_log_sub_log hn1 (by omega) hn
    have hTpos : 0 < T := by linarith
    rw [abs_mul, abs_of_pos hTpos]
    have h1 : 1 < T * (1 / ((x : ℝ) + 1)) := by
      rw [mul_one_div, lt_div_iff₀ (by linarith)]; linarith
    calc (1 : ℝ) < T * (1 / ((x : ℝ) + 1)) := h1
      _ ≤ T * |Real.log n - Real.log x| := mul_le_mul_of_nonneg_left hgap hTpos.le

/-- The `L¹` mass of the Landau test equals that of the profile. -/
theorem integral_norm_landauTest {w : ℝ → ℂ} {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ∫ u, ‖landauTest w T y u‖ = ∫ u, ‖w u‖ := by
  unfold landauTest
  have h1 : (fun u : ℝ => ‖(T : ℂ) * w (T * (u - y))‖) =
      fun u : ℝ => T * (fun v : ℝ => ‖w (T * v)‖) (u - y) := by
    funext u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  rw [h1, integral_const_mul, integral_sub_right_eq_self (fun v : ℝ => ‖w (T * v)‖) y,
    Measure.integral_comp_mul_left (fun v : ℝ => ‖w v‖) T, abs_of_pos (inv_pos.mpr hT),
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]

/-- **The pole terms**: `|h_k(±i/2)| ≤ e^{(y + 1/T)/2} ‖w‖₁`. -/
theorem norm_pole_landauTest_le {w : ℝ → ℂ} (hwi : Integrable w)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) {T : ℝ} (hT : 0 < T) {y : ℝ} (hy : 0 ≤ y) (s : ℂ)
    (hs : |s.im| ≤ 1 / 2) :
    ‖paperFT (landauTest w T y) s‖ ≤ Real.exp ((y + 1 / T) / 2) * ∫ u, ‖w u‖ := by
  have hki : Integrable (landauTest w T y) := by
    unfold landauTest
    have : Integrable (fun u : ℝ => w (T * (u - y))) := by
      have h := (hwi.comp_mul_left' hT.ne').comp_sub_right y
      simpa [Function.comp_def] using h
    exact this.const_mul _
  have hks : ∀ u, landauTest w T y u ≠ 0 → |u| ≤ y + 1 / T := by
    intro u hu
    by_contra hlt
    apply hu
    apply landauTest_eq_zero hsupp
    rw [abs_mul, abs_of_pos hT]
    have h1 : 1 / T < |u - y| := by
      have := abs_sub_abs_le_abs_sub u y
      rw [abs_of_nonneg hy] at this
      linarith [not_le.mp hlt]
    rw [div_lt_iff₀ hT] at h1
    linarith
  have h := norm_paperFT_le hki hks s
  rw [integral_norm_landauTest hT] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (integral_nonneg fun _ =>
    norm_nonneg _))
  have hyT : 0 ≤ y + 1 / T := by positivity
  calc |s.im| * (y + 1 / T) ≤ 1 / 2 * (y + 1 / T) := mul_le_mul_of_nonneg_right hs hyT
    _ = (y + 1 / T) / 2 := by ring

/-! ## Transforms on the real axis -/

open scoped FourierTransform

/-- The real-axis derivative of a transform: `d/ds h_f(s) = h_{iuf}(s)`. -/
theorem hasDerivAt_paperFT_ofReal {f : ℝ → ℂ} (hf : Integrable f)
    (hf' : Integrable (fun x : ℝ => x • f x)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => paperFT f s) (paperFT (fun u => I * u * f u) s) s := by
  have hfun : (fun s : ℝ => paperFT f s) = fun s : ℝ => 𝓕 f (-s / (2 * π)) :=
    funext fun s => paperFT_ofReal_eq_fourier f s
  rw [hfun]
  have h1 := Real.hasDerivAt_fourier hf hf' (-s / (2 * π))
  have h2 : HasDerivAt (fun s : ℝ => -s / (2 * π)) (-1 / (2 * π)) s := by
    simpa using ((hasDerivAt_id s).neg.div_const (2 * π))
  have h3 : HasDerivAt (fun s : ℝ => 𝓕 f (-s / (2 * π)))
      ((-1 / (2 * π)) • 𝓕 (fun x : ℝ => (-2 * π * I * x) • f x) (-s / (2 * π))) s := h1.scomp s h2
  refine h3.congr_deriv ?_
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have harg : -(2 * (π : ℂ) * ((-s / (2 * π) : ℝ) : ℂ)) = (s : ℂ) := by push_cast; field_simp
  rw [fourier_eq_paperFT, harg]
  simp only [paperFT, real_smul]
  rw [← integral_const_mul]
  congr 1; funext u
  simp only [smul_eq_mul]
  push_cast
  field_simp

/-- `|h_f(s)|(1 + s²) ≤ ‖f‖₁ + ‖f''‖₁` on the real axis. -/
theorem norm_paperFT_ofReal_mul_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (s : ℝ) :
    ‖paperFT f s‖ * (1 + s ^ 2) ≤ (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖ := by
  have hfi : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hsupp)
  have h0 := norm_paperFT_le hfi hsupp (s : ℂ)
  have h2 := norm_paperFT_mul_sq_le hf hsupp (s : ℂ)
  simp only [ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h0 h2
  nlinarith

/-! ## The Gamma density `μ` -/

/-- `|μ(τ)| ≤ A + log(2 + |τ|)`. -/
theorem exists_abs_mu_le : ∃ A : ℝ, ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|) := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    gammaFacts.smooth.continuous.continuousOn
  refine ⟨max (|C| + Real.log (2 * π)) B, fun τ => ?_⟩
  have hlog0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  rcases le_or_gt |τ| 1 with h | h
  · have hτ : τ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have := hB τ hτ
    rw [Real.norm_eq_abs] at this
    linarith [le_max_right (|C| + Real.log (2 * π)) B]
  · have h1 : 1 ≤ |τ| := h.le
    have hs := hC τ h1
    have hτ2 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith [sq_abs τ]
    have hCτ : C / τ ^ 2 ≤ |C| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self C, abs_nonneg C]
    have hpi : 0 < 2 * π := by positivity
    have hlogτ : 0 ≤ Real.log |τ| := Real.log_nonneg h1
    have hlogpi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have habs : |Real.log (|τ| / (2 * π))| ≤ Real.log (2 + |τ|) + Real.log (2 * π) := by
      rw [Real.log_div (by linarith) hpi.ne']
      have : Real.log |τ| ≤ Real.log (2 + |τ|) := Real.log_le_log (by linarith) (by linarith)
      rw [abs_le]; constructor <;> linarith
    have hfac : |(1 / (2 * π)) * Real.log (|τ| / (2 * π))| ≤ |Real.log (|τ| / (2 * π))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
      have : 1 / (2 * π) ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
      nlinarith [abs_nonneg (Real.log (|τ| / (2 * π)))]
    have := abs_sub_abs_le_abs_sub (mu τ) ((1 / (2 * π)) * Real.log (|τ| / (2 * π)))
    linarith [le_max_left (|C| + Real.log (2 * π)) B]

/-- `|μ'(τ)| ≤ D/(1 + |τ|)`. -/
theorem exists_abs_deriv_mu_le : ∃ D : ℝ, ∀ τ : ℝ, |deriv mu τ| ≤ D / (1 + |τ|) := by
  obtain ⟨C, hC⟩ := gammaFacts.deriv_bound
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    (gammaFacts.smooth.continuous_deriv (by simp)).continuousOn
  refine ⟨2 * max (max C B) 0, fun τ => ?_⟩
  have hM : 0 ≤ max (max C B) 0 := le_max_right _ _
  have hpos : 0 < 1 + |τ| := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_or_gt |τ| 1 with h | h
  · have hτ : τ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have := hB τ hτ
    rw [Real.norm_eq_abs] at this
    have hBM : B ≤ max (max C B) 0 := (le_max_right C B).trans (le_max_left _ _)
    nlinarith [abs_nonneg (deriv mu τ)]
  · have h1 : 1 ≤ |τ| := h.le
    have hd := hC τ h1
    have hCM : C ≤ max (max C B) 0 := (le_max_left C B).trans (le_max_left _ _)
    have hτpos : 0 < |τ| := by linarith
    rw [le_div_iff₀ hτpos] at hd
    nlinarith [abs_nonneg (deriv mu τ)]

/-! ## Elementary weights -/

/-- `(1 + |τ|)^{-3/2}` written through square roots. -/
lemma one_add_abs_rpow_neg_three_halves (τ : ℝ) :
    (1 + |τ|) ^ (-(3 / 2 : ℝ)) = 1 / ((1 + |τ|) * Real.sqrt (1 + |τ|)) := by
  have ha : 0 < 1 + |τ| := by positivity
  rw [Real.rpow_neg ha.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha,
    Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

/-- `T/(T² + τ²) ≤ 8√T (1 + |τ|)^{-3/2}` for `T ≥ 1`. -/
lemma div_sq_add_sq_le {T τ : ℝ} (hT : 1 ≤ T) :
    T / (T ^ 2 + τ ^ 2) ≤ 8 * Real.sqrt T * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
  rw [one_add_abs_rpow_neg_three_halves]
  set s := Real.sqrt T with hs
  set q := Real.sqrt (1 + |τ|) with hq
  have hs2 : s ^ 2 = T := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 1 + |τ| := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hT
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.mpr (by linarith [abs_nonneg τ])
  have hτ2 : τ ^ 2 = (q ^ 2 - 1) ^ 2 := by rw [hq2]; ring_nf; rw [sq_abs]
  have hden : 0 < T ^ 2 + τ ^ 2 := by positivity
  rw [div_le_iff₀ hden, mul_one_div, ← hq2, ← hs2]
  rw [show 8 * s / (q ^ 2 * q) * ((s ^ 2) ^ 2 + τ ^ 2) =
    8 * s * ((s ^ 2) ^ 2 + τ ^ 2) / (q ^ 2 * q) by ring]
  rw [le_div_iff₀ (by positivity), hτ2]
  -- `s q³ ≤ 8(s⁴ + (q² − 1)²)`, by cases on `q² ≤ 2s²`
  rcases le_or_gt (q ^ 2) (2 * s ^ 2) with h | h
  · have hq32 : q ≤ 3 / 2 * s := by nlinarith
    have : q ^ 3 ≤ (3 / 2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) hq32 3
    nlinarith [sq_nonneg (q ^ 2 - 1)]
  · have hsq : s < q := by nlinarith
    have hq4 : q ^ 4 ≤ 4 * (q ^ 2 - 1) ^ 2 := by nlinarith
    have h1 : s * q ^ 3 ≤ q ^ 4 := by
      have := mul_le_mul_of_nonneg_right hsq.le (pow_nonneg (by linarith : (0:ℝ) ≤ q) 3)
      nlinarith
    have h2 : s * q ^ 3 ≤ 8 * ((s ^ 2) ^ 2 + (q ^ 2 - 1) ^ 2) := by
      nlinarith [sq_nonneg (s ^ 2)]
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ s)
    nlinarith

/-- `T²/(T² + τ²) ≤ 2√T (1 + |τ|)^{-1/4}` for `T ≥ 1`. -/
lemma sq_div_sq_add_sq_le {T τ : ℝ} (hT : 1 ≤ T) :
    T ^ 2 / (T ^ 2 + τ ^ 2) ≤ 2 * Real.sqrt T * (1 + |τ|) ^ (-(1 / 4 : ℝ)) := by
  have ha : 0 < 1 + |τ| := by positivity
  set r := (1 + |τ|) ^ (1 / 4 : ℝ) with hr
  have hr4 : r ^ 4 = 1 + |τ| := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
  have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  rw [Real.rpow_neg ha.le, ← hr]
  set s := Real.sqrt T with hs
  have hs2 : s ^ 2 = T := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hT
  have hτ2 : τ ^ 2 = (r ^ 4 - 1) ^ 2 := by rw [hr4]; ring_nf; rw [sq_abs]
  have hden : 0 < T ^ 2 + τ ^ 2 := by positivity
  have hrpos : 0 < r := by linarith
  rw [div_le_iff₀ hden, ← hs2, hτ2]
  rw [show 2 * s * r⁻¹ * ((s ^ 2) ^ 2 + (r ^ 4 - 1) ^ 2) =
    2 * s * ((s ^ 2) ^ 2 + (r ^ 4 - 1) ^ 2) / r by field_simp]
  rw [le_div_iff₀ hrpos]
  -- `s³ r ≤ 2(s⁴ + (r⁴ − 1)²)`, by cases on `r⁴ ≤ 2s²`
  rcases le_or_gt (r ^ 4) (2 * s ^ 2) with h | h
  · have hrs : r ≤ 2 * s := by nlinarith [sq_nonneg (r ^ 2 - 2 * s), sq_nonneg (r - s)]
    nlinarith [pow_pos hrpos 3]
  · have hhalf : s ^ 2 < r ^ 4 / 2 := by linarith
    have hr8 : r ^ 8 ≤ 4 * (r ^ 4 - 1) ^ 2 := by nlinarith
    have hs_r : s < r ^ 2 := by nlinarith [sq_nonneg (s - r ^ 2)]
    have h3 : s ^ 3 ≤ r ^ 6 / 2 := by
      have := mul_le_mul hs_r.le hhalf.le (sq_nonneg s) (by positivity)
      nlinarith
    have h4 : s ^ 3 * r ≤ 2 * (r ^ 4 - 1) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h3 hrpos.le
      have h7 : r ^ 7 ≤ r ^ 8 := pow_le_pow_right₀ hr1 (by norm_num)
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ s)
    nlinarith [sq_nonneg (s ^ 2), pow_nonneg (by linarith : (0:ℝ) ≤ s) 5]

/-- `log(2 + t) ≤ 8(1 + t)^{1/4}` for `t ≥ 0`. -/
lemma log_two_add_le {t : ℝ} (ht : 0 ≤ t) : Real.log (2 + t) ≤ 8 * (1 + t) ^ (1 / 4 : ℝ) := by
  have h := Real.log_le_rpow_div (x := 2 + t) (by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 : (2 + t) ^ (1 / 4 : ℝ) ≤ (2 * (1 + t)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h2
  have h3 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 : 0 ≤ (1 + t) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc Real.log (2 + t) ≤ (2 + t) ^ (1 / 4 : ℝ) / (1 / 4) := h
    _ = 4 * (2 + t) ^ (1 / 4 : ℝ) := by ring
    _ ≤ 4 * (2 ^ (1 / 4 : ℝ) * (1 + t) ^ (1 / 4 : ℝ)) := by gcongr
    _ ≤ 8 * (1 + t) ^ (1 / 4 : ℝ) := by nlinarith

/-- `T²/(T² + τ²) ≤ 2T²(1 + |τ|)^{-2}` for `T ≥ 1`. -/
lemma sq_div_sq_add_sq_le_inv_sq {T τ : ℝ} (hT : 1 ≤ T) :
    T ^ 2 / (T ^ 2 + τ ^ 2) ≤ 2 * T ^ 2 * (1 + |τ|) ^ (-(2 : ℝ)) := by
  have ha : 0 < 1 + |τ| := by positivity
  rw [Real.rpow_neg ha.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    div_le_iff₀ (by positivity)]
  have h1 : (1 + |τ|) ^ 2 ≤ 2 * (T ^ 2 + τ ^ 2) := by
    nlinarith [sq_abs τ, sq_nonneg (|τ| - 1), abs_nonneg τ]
  have h2 : 0 < ((1 + |τ|) ^ 2)⁻¹ := by positivity
  calc T ^ 2 = 2 * T ^ 2 * ((1 + |τ|) ^ 2)⁻¹ * ((1 + |τ|) ^ 2 / 2) := by field_simp
    _ ≤ 2 * T ^ 2 * ((1 + |τ|) ^ 2)⁻¹ * (T ^ 2 + τ ^ 2) := by gcongr; linarith

/-! ## The Gamma term -/

section GammaTerm

variable {w : ℝ → ℂ}

/-- `u ↦ i u w(u)` is `C²` when `w` is. -/
lemma contDiff_I_mul_id_mul (hw : ContDiff ℝ 2 w) : ContDiff ℝ 2 (fun u : ℝ => I * u * w u) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).mul hw

/-- Decay of the transforms of `w` and of `u ↦ i u w(u)` on the real axis. -/
lemma exists_paperFT_decay (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖paperFT w s‖ ≤ C / (1 + s ^ 2) ∧
      ‖paperFT (fun u => I * u * w u) s‖ ≤ C / (1 + s ^ 2) := by
  have hgsupp : ∀ u, (fun u : ℝ => I * u * w u) u ≠ 0 → |u| ≤ 1 :=
    fun u hu => hsupp u (right_ne_zero_of_mul hu)
  set C₀ := (∫ u, ‖w u‖) + ∫ u, ‖deriv (deriv w) u‖
  set C₁ := (∫ u, ‖(fun u : ℝ => I * u * w u) u‖) +
    ∫ u, ‖deriv (deriv (fun u : ℝ => I * u * w u)) u‖
  have hC₀ : 0 ≤ C₀ :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨max C₀ C₁, hC₀.trans (le_max_left _ _), fun s => ⟨?_, ?_⟩⟩
  · rw [le_div_iff₀ (by positivity)]
    exact (norm_paperFT_ofReal_mul_le hw hsupp s).trans (le_max_left _ _)
  · rw [le_div_iff₀ (by positivity)]
    exact (norm_paperFT_ofReal_mul_le (contDiff_I_mul_id_mul hw) hgsupp s).trans (le_max_right _ _)

/-- Integration by parts against `e^{iyτ}`: `|∫ F(τ) e^{iyτ} dτ| ≤ ‖F'‖₁ / y`. -/
lemma norm_integral_mul_exp_le {F F' : ℝ → ℂ} (hFd : ∀ τ, HasDerivAt F (F' τ) τ)
    (hFi : Integrable F) (hF'i : Integrable F') {y : ℝ} (hy : 0 < y) :
    ‖∫ τ : ℝ, F τ * Complex.exp (I * y * τ)‖ ≤ (∫ τ, ‖F' τ‖) / y := by
  have hyC : I * (y : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hy.ne')
  set e : ℝ → ℂ := fun τ => Complex.exp (I * y * τ) with he
  set v : ℝ → ℂ := fun τ => e τ / (I * y) with hv
  have hvd : ∀ τ : ℝ, HasDerivAt v (e τ) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => I * (y : ℂ) * τ) (I * y * 1) τ :=
      (hasDerivAt_id τ).ofReal_comp.const_mul (I * y)
    have h2 := h1.cexp.div_const (I * y)
    rw [mul_one, mul_div_assoc, div_self hyC, mul_one] at h2
    exact h2
  have hen : ∀ τ : ℝ, ‖e τ‖ = 1 := by
    intro τ; rw [he, Complex.norm_exp]; simp
  have hvn : ∀ τ : ℝ, ‖v τ‖ = 1 / y := by
    intro τ
    rw [hv, norm_div, hen, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
  have hec : Continuous e := by rw [he]; fun_prop
  have hvc : Continuous v := hec.div_const _
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun τ => (hFd τ).continuousAt
  have h1 : Integrable (F * e) :=
    hFi.norm.mono' (hFc.mul hec).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by simp [hen])
  have h2 : Integrable (F' * v) :=
    (hF'i.norm.mul_const (1 / y)).mono' (hF'i.aestronglyMeasurable.mul hvc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.mul_apply, norm_mul, hvn, le_refl])
  have h3 : Integrable (F * v) :=
    (hFi.norm.mul_const (1 / y)).mono' (hFc.mul hvc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.mul_apply, norm_mul, hvn, le_refl])
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun τ _ => hFd τ)
    (fun τ _ => hvd τ) h1 h2 h3
  change ‖∫ τ : ℝ, F τ * e τ‖ ≤ _
  rw [hibp, norm_neg]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_mul, hvn]
  rw [integral_mul_const]
  ring

/-- The amplitude `ŵ(τ/T) μ(τ)` of the Gamma term of the Landau test. -/
def gammaAmp (w : ℝ → ℂ) (T τ : ℝ) : ℂ := paperFT w ((τ / T : ℝ) : ℂ) * (mu τ : ℂ)

/-- The derivative of `gammaAmp` in `τ`. -/
def gammaAmpDeriv (w : ℝ → ℂ) (T τ : ℝ) : ℂ :=
  ((1 / T : ℝ) : ℂ) * paperFT (fun u => I * u * w u) ((τ / T : ℝ) : ℂ) * (mu τ : ℂ) +
    paperFT w ((τ / T : ℝ) : ℂ) * ((deriv mu τ : ℝ) : ℂ)

lemma hasDerivAt_gammaAmp {w : ℝ → ℂ} (hwi : Integrable w)
    (hwi' : Integrable (fun x : ℝ => x • w x)) (T τ : ℝ) :
    HasDerivAt (gammaAmp w T) (gammaAmpDeriv w T τ) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => paperFT w ((τ / T : ℝ) : ℂ))
      ((1 / T : ℝ) • paperFT (fun u => I * u * w u) ((τ / T : ℝ) : ℂ)) τ := by
    have := (hasDerivAt_paperFT_ofReal hwi hwi' (τ / T)).scomp τ ((hasDerivAt_id τ).div_const T)
    simpa [Function.comp_def, one_div] using this
  have h2 : HasDerivAt (fun τ : ℝ => (mu τ : ℂ)) ((deriv mu τ : ℝ) : ℂ) τ :=
    ((gammaFacts.smooth.differentiable (by simp)) τ).hasDerivAt.ofReal_comp
  have e : gammaAmpDeriv w T τ = (1 / T : ℝ) • paperFT (fun u => I * u * w u) ((τ / T : ℝ) : ℂ) *
      (mu τ : ℂ) + paperFT w ((τ / T : ℝ) : ℂ) * ((deriv mu τ : ℝ) : ℂ) := by
    rw [gammaAmpDeriv, Complex.real_smul]
  rw [e]
  exact h1.mul h2

/-- `|μ(τ)| ≤ (|A| + 8)(1 + |τ|)^{1/4}` from `|μ(τ)| ≤ A + log(2 + |τ|)`. -/
lemma abs_mu_le_rpow {A : ℝ} (hA : ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|)) (τ : ℝ) :
    |mu τ| ≤ (|A| + 8) * (1 + |τ|) ^ (1 / 4 : ℝ) := by
  have h1 := hA τ
  have h2 := log_two_add_le (abs_nonneg τ)
  have h3 : 1 ≤ (1 + |τ|) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  nlinarith [le_abs_self A, abs_nonneg A]

/-- `‖ŵ(τ/T)‖ ≤ C T²/(T² + τ²)` from `‖ŵ(s)‖ ≤ C/(1 + s²)`. -/
lemma norm_paperFT_div_le {f : ℝ → ℂ} {C T : ℝ} (hT : 0 < T)
    (hC : ∀ s : ℝ, ‖paperFT f s‖ ≤ C / (1 + s ^ 2)) (τ : ℝ) :
    ‖paperFT f ((τ / T : ℝ) : ℂ)‖ ≤ C * (T ^ 2 / (T ^ 2 + τ ^ 2)) := by
  have e : C / (1 + (τ / T) ^ 2) = C * (T ^ 2 / (T ^ 2 + τ ^ 2)) := by field_simp
  rw [← e]; exact hC _

lemma rpow_mul_rpow_one_add_abs (τ a b : ℝ) :
    (1 + |τ|) ^ a * (1 + |τ|) ^ b = (1 + |τ|) ^ (a + b) :=
  (Real.rpow_add (by positivity) a b).symm

/-- The derivative of the amplitude decays like `√T (1 + |τ|)^{-5/4}`. -/
lemma norm_gammaAmpDeriv_le {w : ℝ → ℂ} {C A D T : ℝ} (hT : 1 ≤ T)
    (hC : ∀ s : ℝ, ‖paperFT w s‖ ≤ C / (1 + s ^ 2) ∧
      ‖paperFT (fun u => I * u * w u) s‖ ≤ C / (1 + s ^ 2)) (hC0 : 0 ≤ C)
    (hA : ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|)) (hD : ∀ τ : ℝ, |deriv mu τ| ≤ D / (1 + |τ|))
    (τ : ℝ) :
    ‖gammaAmpDeriv w T τ‖ ≤
      (8 * C * (|A| + 8) + 2 * C * |D|) * Real.sqrt T * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
  have hTpos : 0 < T := by linarith
  have ha : 0 < 1 + |τ| := by positivity
  have hW := norm_paperFT_div_le hTpos (fun s => (hC s).1) τ
  have hW₁ := norm_paperFT_div_le hTpos (fun s => (hC s).2) τ
  have hmu := abs_mu_le_rpow hA τ
  have hp1 := div_sq_add_sq_le (τ := τ) hT
  have hp2 := sq_div_sq_add_sq_le (τ := τ) hT
  have hfrac : 0 ≤ T ^ 2 / (T ^ 2 + τ ^ 2) := by positivity
  have hq1 : 0 ≤ (1 + |τ|) ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha.le _
  have t1 : ‖((1 / T : ℝ) : ℂ) * paperFT (fun u => I * u * w u) ((τ / T : ℝ) : ℂ) * (mu τ : ℂ)‖ ≤
      8 * C * (|A| + 8) * Real.sqrt T * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
    have hk : 1 / T * (C * (T ^ 2 / (T ^ 2 + τ ^ 2))) = C * (T / (T ^ 2 + τ ^ 2)) := by
      field_simp
    calc 1 / T * ‖paperFT (fun u => I * u * w u) ((τ / T : ℝ) : ℂ)‖ * |mu τ|
        ≤ 1 / T * (C * (T ^ 2 / (T ^ 2 + τ ^ 2))) * ((|A| + 8) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by
          gcongr
      _ = C * (T / (T ^ 2 + τ ^ 2)) * ((|A| + 8) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by rw [hk]
      _ ≤ C * (8 * Real.sqrt T * (1 + |τ|) ^ (-(3 / 2 : ℝ))) *
          ((|A| + 8) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * C * (|A| + 8) * Real.sqrt T *
          ((1 + |τ|) ^ (-(3 / 2 : ℝ)) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by ring
      _ = 8 * C * (|A| + 8) * Real.sqrt T * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
          rw [rpow_mul_rpow_one_add_abs]; norm_num
  have t2 : ‖paperFT w ((τ / T : ℝ) : ℂ) * ((deriv mu τ : ℝ) : ℂ)‖ ≤
      2 * C * |D| * Real.sqrt T * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hDτ : |deriv mu τ| ≤ |D| * (1 + |τ|) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (hD τ).trans (div_le_div_of_nonneg_right (le_abs_self D) ha.le)
    calc ‖paperFT w ((τ / T : ℝ) : ℂ)‖ * |deriv mu τ|
        ≤ C * (T ^ 2 / (T ^ 2 + τ ^ 2)) * (|D| * (1 + |τ|) ^ (-(1 : ℝ))) := by gcongr
      _ ≤ C * (2 * Real.sqrt T * (1 + |τ|) ^ (-(1 / 4 : ℝ))) * (|D| * (1 + |τ|) ^ (-(1 : ℝ))) := by
          gcongr
      _ = 2 * C * |D| * Real.sqrt T *
          ((1 + |τ|) ^ (-(1 / 4 : ℝ)) * (1 + |τ|) ^ (-(1 : ℝ))) := by ring
      _ = 2 * C * |D| * Real.sqrt T * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
          rw [rpow_mul_rpow_one_add_abs]; norm_num
  calc ‖gammaAmpDeriv w T τ‖ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

/-- The amplitude itself decays like `T² (1 + |τ|)^{-5/4}`. -/
lemma norm_gammaAmp_le {w : ℝ → ℂ} {C A T : ℝ} (hT : 1 ≤ T)
    (hC : ∀ s : ℝ, ‖paperFT w s‖ ≤ C / (1 + s ^ 2)) (hC0 : 0 ≤ C)
    (hA : ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|)) (τ : ℝ) :
    ‖gammaAmp w T τ‖ ≤ 2 * C * T ^ 2 * (|A| + 8) * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
  have hTpos : 0 < T := by linarith
  have ha : 0 < 1 + |τ| := by positivity
  have hW := norm_paperFT_div_le hTpos hC τ
  have hmu := abs_mu_le_rpow hA τ
  have hp := sq_div_sq_add_sq_le_inv_sq (τ := τ) hT
  have hq1 : 0 ≤ (1 + |τ|) ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha.le _
  have hm : (1 + |τ|) ^ (-(2 : ℝ) + 1 / 4) ≤ (1 + |τ|) ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by norm_num)
  unfold gammaAmp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖paperFT w ((τ / T : ℝ) : ℂ)‖ * |mu τ|
      ≤ C * (T ^ 2 / (T ^ 2 + τ ^ 2)) * ((|A| + 8) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by gcongr
    _ ≤ C * (2 * T ^ 2 * (1 + |τ|) ^ (-(2 : ℝ))) * ((|A| + 8) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by
        gcongr
    _ = 2 * C * T ^ 2 * (|A| + 8) * ((1 + |τ|) ^ (-(2 : ℝ)) * (1 + |τ|) ^ (1 / 4 : ℝ)) := by ring
    _ ≤ 2 * C * T ^ 2 * (|A| + 8) * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
        rw [rpow_mul_rpow_one_add_abs]; gcongr

/-- **The Gamma term of the Landau test**: `|∫ h_k(τ) μ(τ) dτ| ≤ K √T / y` for `T ≥ 1`, `y > 0`,
by one integration by parts against the phase `e^{iτy}`. -/
theorem exists_gammaTerm_landau_le (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ K : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 < y →
      ‖∫ τ : ℝ, paperFT (landauTest w T y) τ * (mu τ : ℂ)‖ ≤ K * Real.sqrt T / y := by
  obtain ⟨C, hC0, hC⟩ := exists_paperFT_decay hw hsupp
  obtain ⟨A, hA⟩ := exists_abs_mu_le
  obtain ⟨D, hD⟩ := exists_abs_deriv_mu_le
  have hJi : Integrable (fun τ : ℝ => (1 + |τ|) ^ (-(5 / 4 : ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  set K₀ := 8 * C * (|A| + 8) + 2 * C * |D| with hK₀
  refine ⟨K₀ * ∫ τ : ℝ, (1 + |τ|) ^ (-(5 / 4 : ℝ)), fun T hT y hy => ?_⟩
  have hTpos : 0 < T := by linarith
  have hwi : Integrable w := hw.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hsupp)
  have hwi' : Integrable (fun x : ℝ => x • w x) :=
    (continuous_id.smul hw.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (Λ := 1) fun u hu =>
        hsupp u fun h => hu (by simp [h]))
  have hFd := hasDerivAt_gammaAmp hwi hwi' T
  have hFc : Continuous (gammaAmp w T) :=
    continuous_iff_continuousAt.mpr fun τ => (hFd τ).continuousAt
  have hFi : Integrable (gammaAmp w T) :=
    (hJi.const_mul (2 * C * T ^ 2 * (|A| + 8))).mono' hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_gammaAmp_le hT (fun s => (hC s).1) hC0 hA))
  have hF'm : AEStronglyMeasurable (gammaAmpDeriv w T) := by
    have : gammaAmpDeriv w T = deriv (gammaAmp w T) := funext fun τ => (hFd τ).deriv.symm
    rw [this]
    exact (measurable_deriv _).aestronglyMeasurable
  have hF'i : Integrable (gammaAmpDeriv w T) :=
    (hJi.const_mul (K₀ * Real.sqrt T)).mono' hF'm
      (Filter.Eventually.of_forall (norm_gammaAmpDeriv_le hT hC hC0 hA hD))
  have hrw : (fun τ : ℝ => paperFT (landauTest w T y) τ * (mu τ : ℂ)) =
      fun τ : ℝ => gammaAmp w T τ * Complex.exp (I * y * τ) := by
    funext τ
    rw [paperFT_landauTest w hTpos, gammaAmp]
    push_cast
    ring_nf
  rw [hrw]
  refine (norm_integral_mul_exp_le hFd hFi hF'i hy).trans ?_
  gcongr
  calc (∫ τ, ‖gammaAmpDeriv w T τ‖)
      ≤ ∫ τ : ℝ, K₀ * Real.sqrt T * (1 + |τ|) ^ (-(5 / 4 : ℝ)) :=
        integral_mono hF'i.norm (hJi.const_mul _) (norm_gammaAmpDeriv_le hT hC hC0 hA hD)
    _ = K₀ * (∫ τ : ℝ, (1 + |τ|) ^ (-(5 / 4 : ℝ))) * Real.sqrt T := by
        rw [integral_const_mul]; ring

/-- The Landau test is `C²` with compact support. -/
lemma landauTest_contDiff_hasCompactSupport (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ContDiff ℝ 2 (landauTest w T y) ∧ HasCompactSupport (landauTest w T y) := by
  refine ⟨contDiff_const.mul (hw.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))), ?_⟩
  refine hasCompactSupport_of_support_subset_abs (Λ := |y| + 1 / T) fun u hu => ?_
  by_contra hlt
  apply hu
  apply landauTest_eq_zero hsupp
  rw [abs_mul, abs_of_pos hT]
  have h1 : 1 / T < |u - y| := by
    have := abs_sub_abs_le_abs_sub u y
    linarith [not_le.mp hlt]
  rw [div_lt_iff₀ hT] at h1
  linarith

/-- **The smoothed Landau formula.**  For a `C²` profile `w` supported in `[−1, 1]` there is `K`
such that for every integer `x ≥ 2` and every `T ≥ x + 2`, with `k` the Landau test at `log x`,
`|Σ_ρ m_ρ h_k(γ_ρ) + T w(0) Λ(x)/√x| ≤ 2 e^{1/2} ‖w‖₁ √x + K √T / log x`.
Here `h_k(γ_ρ) = x^{ρ − ½} ŵ(γ_ρ/T)`: the zero sum detects the prime power `x` at height `T`. -/
theorem exists_smoothedLandau_le (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ K : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ T : ℝ, (x : ℝ) + 2 ≤ T →
      ‖(∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          paperFT (landauTest w T (Real.log x)) (gammaOf ρ)) +
        ((ArithmeticFunction.vonMangoldt x / Real.sqrt x : ℝ) : ℂ) * ((T : ℂ) * w 0)‖ ≤
        2 * Real.exp (1 / 2) * (∫ u, ‖w u‖) * Real.sqrt x + K * Real.sqrt T / Real.log x := by
  obtain ⟨K, hK⟩ := exists_gammaTerm_landau_le hw hsupp
  refine ⟨K, fun x hx T hT => ?_⟩
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hwi : Integrable w := hw.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hsupp)
  obtain ⟨hkd, hkc⟩ := landauTest_contDiff_hasCompactSupport hw hsupp hTpos (Real.log x)
  have hEF := (Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hkd hkc).2
  rw [hEF, EF.literatureRHS, EF.gamma_term, primeSum_landauTest hsupp hx hT]
  -- pole terms
  have hpole : ∀ s : ℂ, |s.im| ≤ 1 / 2 →
      ‖paperFT (landauTest w T (Real.log x)) s‖ ≤ Real.exp (1 / 2) * (∫ u, ‖w u‖) * Real.sqrt x := by
    intro s hs
    refine (norm_pole_landauTest_le hwi hsupp hTpos hlog.le s hs).trans ?_
    have hT' : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT1
    have hsq : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]; ring_nf
    rw [hsq, mul_right_comm, ← Real.exp_add]
    gcongr
    linarith
  have hI : |(I / 2 : ℂ).im| ≤ 1 / 2 := by simp [abs_of_pos]
  have hI' : |(-I / 2 : ℂ).im| ≤ 1 / 2 := by simp [abs_of_pos]
  have hG := hK T hT1 (Real.log x) hlog
  calc ‖paperFT (landauTest w T (Real.log x)) (I / 2) + paperFT (landauTest w T (Real.log x)) (-I / 2)
        - ((ArithmeticFunction.vonMangoldt x / Real.sqrt x : ℝ) : ℂ) * ((T : ℂ) * w 0)
        + (∫ τ : ℝ, paperFT (landauTest w T (Real.log x)) τ * (mu τ : ℂ))
        + ((ArithmeticFunction.vonMangoldt x / Real.sqrt x : ℝ) : ℂ) * ((T : ℂ) * w 0)‖
      = ‖paperFT (landauTest w T (Real.log x)) (I / 2) + paperFT (landauTest w T (Real.log x)) (-I / 2)
        + ∫ τ : ℝ, paperFT (landauTest w T (Real.log x)) τ * (mu τ : ℂ)‖ := by ring_nf
    _ ≤ ‖paperFT (landauTest w T (Real.log x)) (I / 2)‖ +
        ‖paperFT (landauTest w T (Real.log x)) (-I / 2)‖ +
        ‖∫ τ : ℝ, paperFT (landauTest w T (Real.log x)) τ * (mu τ : ℂ)‖ := norm_add₃_le
    _ ≤ _ := by linarith [hpole _ hI, hpole _ hI']

end GammaTerm

end RHTower

end
