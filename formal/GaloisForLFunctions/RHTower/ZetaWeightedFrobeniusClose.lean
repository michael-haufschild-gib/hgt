import GaloisForLFunctions.RHTower.ZetaWeightedFrobeniusFar

/-!
# Close prime pairs in the weighted Frobenius norm: the continuous kernel

Poisson summation on the grid `τ_k = T + k h`, `h = 2π/L`, for a window whose transform vanishes for `|η| ≥ B` keeps only
the aliases `jL` within `B` of the frequency.  If the frequency `y` is at distance `≥ B` from every alias except `j = 0`,
exactly one term survives (`hasSum_grid_char_of_window`):

`Σ_{k∈ℤ} W(τ_k) e^{iyτ_k} = (L/2π) ∫ W(s) e^{iys} ds`.

For the product `W(s + rh) W(s)` of Jackson windows (band `4b`) this gives the close-pair kernel
`K_r(θ) = (L/2π) ∫ W(s + rh) W(s) e^{iθs} ds` (`jacksonPairKernel`, `hasSum_jacksonProduct_grid_char`).  On the finite
grid `[0, d)` the admissible sums differ from it by at most twice the outer Jackson mass `E₀`
(`norm_sum_admissible_jacksonProduct_sub_le`), and grid double sums with a difference kernel `B` satisfy
(`norm_sum_sum_jacksonDifference_sub_le`)

`‖Σ_{k,l} W_k W_l e^{iθτ_l} B(k − l) − Σ_{|r|<d} B(r) K_r(θ)‖ ≤ 2E₀ Σ_{|r|<d} ‖B(r)‖`.

For a close prime pair (`y_n − y_m` near `0`, far from the other aliases, and `y_n + y_m` far from all aliases) the
weighted Frobenius entry is `½ Re Σ_r A_n(r) Ā_m(r) K_r(y_n − y_m)` up to `2E₀ Σ_r ‖A_n(r)‖ ‖A_m(r)‖`
(`abs_weighted_close_pair_sub_le`): the close-pair part of the weighted prime–prime Frobenius norm is a smoothed
prime-pair correlation with the explicit kernel `K_r`.
-/

open Complex MeasureTheory Real Set Filter Asymptotics Finset
open scoped FourierTransform

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b s₀ s₁ : ℝ}

/-- **Poisson summation with a single surviving alias.** -/
theorem hasSum_grid_char_of_window {W : ℝ → ℝ} {B L : ℝ} (hWc : Continuous W)
    {C R : ℝ} (hC : 0 ≤ C) (hWdec : ∀ s, R ≤ |s| → |W s| ≤ C / s ^ 2)
    (hWF : ∀ η : ℝ, B ≤ |η| → ∫ s, ((W s : ℝ) : ℂ) * cexp (-(I * η * s)) = 0)
    (hL : 0 < L) (T y : ℝ) (hy : ∀ j : ℤ, j ≠ 0 → B ≤ |j * L - y|) :
    HasSum (fun k : ℤ => ((W (T + k * (2 * π / L)) : ℝ) : ℂ)
      * cexp (I * y * ((T + k * (2 * π / L) : ℝ) : ℂ)))
      (((L / (2 * π) : ℝ) : ℂ) * ∫ s, ((W s : ℝ) : ℂ) * cexp (I * y * s)) := by
  set h : ℝ := 2 * π / L with hh
  have hh0 : 0 < h := by positivity
  set g : ℝ → ℂ := fun x => ((W (T + x * h) : ℝ) : ℂ) * cexp (I * y * ((T + x * h : ℝ) : ℂ)) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hnorm : ∀ x, ‖g x‖ = |W (T + x * h)| := by
    intro x
    simp only [hg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show I * (y : ℂ) * ((T + x * h : ℝ) : ℂ) = ((y * (T + x * h)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hgO : g =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound (4 * C / h ^ 2) ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (2 * (|T| + |R| + 1) / h))] with x hx
    rw [Real.norm_eq_abs, div_le_iff₀ hh0] at hx
    have hT := abs_nonneg T
    have hRa := abs_nonneg R
    have h2 : |x * h| ≤ |T + x * h| + |T| := by
      have := abs_sub (T + x * h) T
      rwa [add_sub_cancel_left] at this
    have hxh : |x * h| = |x| * h := by rw [abs_mul, abs_of_pos hh0]
    have hs : |x| * h / 2 ≤ |T + x * h| := by linarith
    have hRs : R ≤ |T + x * h| := by linarith [le_abs_self R]
    have hpos : 0 < |x| * h / 2 := by linarith
    rw [hnorm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) (-2)),
      Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsq : (|x| * h / 2) ^ 2 ≤ (T + x * h) ^ 2 := by
      rw [← sq_abs (T + x * h)]; exact pow_le_pow_left₀ hpos.le hs 2
    calc |W (T + x * h)| ≤ C / (T + x * h) ^ 2 := hWdec (T + x * h) hRs
      _ ≤ C / (|x| * h / 2) ^ 2 := div_le_div_of_nonneg_left hC (by positivity) hsq
      _ = 4 * C / h ^ 2 * (|x| ^ 2)⁻¹ := by field_simp; ring
  set G : ℝ → ℝ → ℂ := fun w s => cexp (I * ((w * L * T : ℝ) : ℂ))
      * (((W s : ℝ) : ℂ) * cexp (-(I * ((w * L - y : ℝ) : ℂ) * s))) with hG
  have hFw : ∀ w : ℝ, 𝓕 g w = ((L / (2 * π) : ℝ) : ℂ) * ∫ s, G w s := by
    intro w
    have hpt : ∀ x : ℝ, Real.fourierChar (-(x * w)) • g x = G w (T + h * x) := by
      intro x
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hg, hG]
      rw [show T + x * h = T + h * x by ring]
      have e1 : cexp (((2 * π * -(x * w) : ℝ) : ℂ) * I) * cexp (I * (y : ℂ) * ((T + h * x : ℝ) : ℂ))
          = cexp (I * ((w * L * T : ℝ) : ℂ))
            * cexp (-(I * ((w * L - y : ℝ) : ℂ) * ((T + h * x : ℝ) : ℂ))) := by
        have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        rw [hh]
        push_cast
        field_simp
        ring
      linear_combination ((W (T + h * x) : ℝ) : ℂ) * e1
    rw [Real.fourier_real_eq]
    simp_rw [hpt]
    have h1 := Measure.integral_comp_mul_left (fun z => G w (T + z)) h
    rw [h1, integral_add_left_eq_self (G w) T, Complex.real_smul, abs_of_pos (inv_pos.mpr hh0), hh,
      inv_div]
  have hF0 : ∀ w : ℝ, B ≤ |w * L - y| → 𝓕 g w = 0 := by
    intro w hw
    rw [hFw, hG]
    simp only
    rw [integral_const_mul, hWF _ hw, mul_zero, mul_zero]
  have hFzero : 𝓕 g 0 = ((L / (2 * π) : ℝ) : ℂ) * ∫ s, ((W s : ℝ) : ℂ) * cexp (I * y * s) := by
    rw [hFw]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hG]
    push_cast
    simp only [zero_mul, mul_zero, Complex.exp_zero, one_mul, zero_sub]
    congr 2
    ring
  have hFO : 𝓕 g =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop ((|y| + B) / L))]
      with w hw
    rw [Real.norm_eq_abs, div_le_iff₀ hL] at hw
    rw [hF0 w]
    · simp
    · have h1 : |w * L| - |y| ≤ |w * L - y| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h1
      linarith
  have hsum : Summable (fun k : ℤ => g k) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) (hgO.comp_tendsto Int.tendsto_coe_cofinite)
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay hgc one_lt_two hgO hFO 0
  simp only [zero_add] at key
  have hsingle : ∑' n : ℤ, 𝓕 g n * fourier n ((0 : ℝ) : UnitAddCircle) = 𝓕 g 0 := by
    rw [tsum_eq_single 0 (fun n hn => by rw [hF0 n (hy n hn), zero_mul])]
    simp
  rw [hsingle, hFzero] at key
  have hfin := hsum.hasSum
  rw [key] at hfin
  convert hfin using 1

/-- The continuous close-pair kernel `K_r(θ) = (L/2π) ∫ W(s + rh) W(s) e^{iθs} ds`, `h = 2π/L`. -/
def jacksonPairKernel (b s₀ s₁ L : ℝ) (r : ℤ) (θ : ℝ) : ℂ :=
  ((L / (2 * π) : ℝ) : ℂ) * ∫ s, ((jacksonWindow b s₀ s₁ (s + r * (2 * π / L))
    * jacksonWindow b s₀ s₁ s : ℝ) : ℂ) * cexp (I * θ * s)

/-- **Grid character sums of the product window near the zero alias.** -/
theorem hasSum_jacksonProduct_grid_char (hb : 0 < b) (h01 : s₀ ≤ s₁) (r : ℤ) {L : ℝ}
    (hL : 0 < L) (T y : ℝ) (hy : ∀ j : ℤ, j ≠ 0 → 4 * b ≤ |j * L - y|) :
    HasSum (fun k : ℤ => ((jacksonWindow b s₀ s₁ (T + k * (2 * π / L) + r * (2 * π / L))
        * jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) : ℝ) : ℂ)
      * cexp (I * y * ((T + k * (2 * π / L) : ℝ) : ℂ))) (jacksonPairKernel b s₀ s₁ L r y) := by
  have hc : Continuous fun s => jacksonWindow b s₀ s₁ (s + r * (2 * π / L)) * jacksonWindow b s₀ s₁ s :=
    ((continuous_jacksonWindow hb).comp (continuous_add_const _)).mul (continuous_jacksonWindow hb)
  have hk := (jacksonMass_pos hb).le
  exact hasSum_grid_char_of_window (W := fun s => jacksonWindow b s₀ s₁ (s + r * (2 * π / L))
      * jacksonWindow b s₀ s₁ s) hc (C := (jacksonMass b)⁻¹ * (64 / (3 * b ^ 2))) (by positivity)
    (fun s hs => by
      rw [abs_mul]
      have h1 : |jacksonWindow b s₀ s₁ (s + r * (2 * π / L))| ≤ 1 := by
        rw [abs_of_nonneg (jacksonWindow_nonneg hb h01 _)]; exact jacksonWindow_le_one hb h01 _
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (abs_jacksonWindow_le_inv_sq hb h01 hs))
    (fun η hη => integral_jacksonProduct_mul_cexp_eq_zero hb h01 _ hη) hL T y hy

/-- **Admissible product-window sums near the zero alias.** -/
theorem norm_sum_admissible_jacksonProduct_sub_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) (r : ℤ) {y : ℝ}
    (hy : ∀ j : ℤ, j ≠ 0 → 4 * b ≤ |j * L - y|) :
    ‖∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d),
        ((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
          * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) - jacksonPairKernel b s₀ s₁ L r y‖
      ≤ 2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2))) := by
  have hc := hasSum_jacksonProduct_grid_char hb h01 r hL T y hy
  have e : ∀ l : ℤ, T + l * (2 * π / L) + r * (2 * π / L) = T + ((l + r : ℤ) : ℝ) * (2 * π / L) := by
    intro l; push_cast; ring
  simp only [e] at hc
  set u : ℤ → ℝ := fun k => jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => jacksonWindow_nonneg hb h01 _
  have hu1 : ∀ k, u k ≤ 1 := fun k => jacksonWindow_le_one hb h01 _
  have hus : Summable u := summable_jacksonWindow_grid hb h01 hL T
  have hnorm : ∀ l : ℤ, ‖((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
        * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
        * cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ))‖ = u (l + r) * u l := by
    intro l
    have h1 : ‖cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ))‖ = 1 := by
      rw [show I * (y : ℂ) * ((T + l * (2 * π / L) : ℝ) : ℂ)
          = ((y * (T + l * (2 * π / L)) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hu0 (l + r)) (hu0 l))]
  have h := norm_sum_admissible_sub_le hc hu0 hu0 hus hus r
    (fun l => by rw [hnorm]; exact mul_le_of_le_one_right (hu0 _) (hu1 l))
    (fun l => by rw [hnorm]; exact mul_le_of_le_one_left (hu0 l) (hu1 _)) (Finset.Ico (0 : ℤ) d)
  have hE := tsum_indicator_compl_jacksonWindow_le hb h01 hL hM d hs₀ hs₁
  refine h.trans ?_
  linarith

/-- **Grid double sums with a difference kernel near the zero alias.** -/
theorem norm_sum_sum_jacksonDifference_sub_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) {θ : ℝ}
    (hθ : ∀ j : ℤ, j ≠ 0 → 4 * b ≤ |j * L - θ|) (B : ℤ → ℂ) :
    ‖∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d,
        ((jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) * B (k - l)
        - ∑ r ∈ Finset.Ioo (-(d : ℤ)) d, B r * jacksonPairKernel b s₀ s₁ L r θ‖
      ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖B r‖)
          * (2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)))) := by
  rw [sum_sum_eq_sum_offset, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hterm : ∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d),
      ((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
        * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) * B (l + r - l)
        - B r * jacksonPairKernel b s₀ s₁ L r θ
      = B r * (∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d),
        ((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
          * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) - jacksonPairKernel b s₀ s₁ L r θ) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [add_sub_cancel_left]
    ring
  rw [hterm, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_sum_admissible_jacksonProduct_sub_le hb h01 hL hM d hs₀ hs₁ r hθ) (norm_nonneg _)

/-- **A close prime pair in the weighted Frobenius sum.**  With `z_n(k, l) = e^{iy_nτ_l} A_n(k − l)`, if `y_n − y_m` is
at distance `≥ 4b` from every alias `jL` with `j ≠ 0` and `y_n + y_m` from every alias, then the `(n, m)` entry of the
weighted expansion equals `½ Re Σ_r A_n(r) Ā_m(r) K_r(y_n − y_m)` up to `2E₀ Σ_{|r|<d} ‖A_n(r)‖ ‖A_m(r)‖`. -/
theorem abs_weighted_close_pair_sub_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) {y y' : ℝ}
    (hminus : ∀ j : ℤ, j ≠ 0 → 4 * b ≤ |j * L - (y - y')|) (hplus : ∀ j : ℤ, 4 * b ≤ |j * L - (y + y')|)
    (A A' : ℤ → ℂ) :
    |∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d,
        jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L))
          * (((cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * starRingEnd ℂ (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re
              + (cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re) / 2)
        - (∑ r ∈ Finset.Ioo (-(d : ℤ)) d,
            A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y')).re / 2|
      ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖A r‖ * ‖A' r‖)
          * (2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)))) := by
  set E : ℝ := 2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2))) with hE
  set S := Finset.Ico (0 : ℤ) d with hS
  set τ : ℤ → ℝ := fun l => T + l * (2 * π / L) with hτ
  set w : ℤ → ℤ → ℝ := fun k l => jacksonWindow b s₀ s₁ (T + k * (2 * π / L))
    * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) with hw
  set g₁ : ℤ → ℤ → ℂ := fun k l => cexp (I * ((y - y' : ℝ) : ℂ) * ((τ l : ℝ) : ℂ))
    * (A (k - l) * starRingEnd ℂ (A' (k - l))) with hg₁
  set g₂ : ℤ → ℤ → ℂ := fun k l => cexp (I * ((y + y' : ℝ) : ℂ) * ((τ l : ℝ) : ℂ))
    * (A (k - l) * A' (k - l)) with hg₂
  have hsplit : ∑ k ∈ S, ∑ l ∈ S,
        jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L))
          * (((cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * starRingEnd ℂ (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re
              + (cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re) / 2)
      = ((∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re) + ∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e₁ : cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
          * starRingEnd ℂ (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l)) = g₁ k l := by
      simp only [hg₁, hτ, map_mul]
      rw [← cexp_mul_conj_cexp]
      ring
    have e₂ : cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
          * (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l)) = g₂ k l := by
      simp only [hg₂, hτ]
      rw [← cexp_mul_cexp_I]
      ring
    rw [e₁, e₂]
    simp only [hw]
    ring
  rw [hsplit]
  have hre : ∀ g : ℤ → ℤ → ℂ, ∑ k ∈ S, ∑ l ∈ S, w k l * (g k l).re
      = (∑ k ∈ S, ∑ l ∈ S, (w k l : ℂ) * g k l).re := by
    intro g
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have hform : ∀ (θ : ℝ) (B : ℤ → ℂ), ∑ k ∈ S, ∑ l ∈ S, (w k l : ℂ)
        * (cexp (I * ((θ : ℝ) : ℂ) * ((τ l : ℝ) : ℂ)) * B (k - l))
      = ∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d,
        ((jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) * B (k - l) := by
    intro θ B
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hw, hτ]
    ring
  have h₁ := norm_sum_sum_jacksonDifference_sub_le hb h01 hL hM d hs₀ hs₁ hminus
    (fun r => A r * starRingEnd ℂ (A' r))
  have h₂ := norm_sum_sum_jacksonDifference_le hb h01 hL hM d hs₀ hs₁ hplus (fun r => A r * A' r)
  rw [← hform (y - y') (fun r => A r * starRingEnd ℂ (A' r))] at h₁
  rw [← hform (y + y') (fun r => A r * A' r)] at h₂
  simp only [norm_mul, Complex.norm_conj] at h₁ h₂
  have hX₁ : |(∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re)
      - (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y')).re|
      ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖A r‖ * ‖A' r‖) * E := by
    rw [hre, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans h₁
  have hX₂ : |∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re|
      ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖A r‖ * ‖A' r‖) * E := by
    rw [hre]
    exact (Complex.abs_re_le_norm _).trans h₂
  rw [show ((∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re) + ∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re) / 2
      - (∑ r ∈ Finset.Ioo (-(d : ℤ)) d,
          A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y')).re / 2
      = (((∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re)
          - (∑ r ∈ Finset.Ioo (-(d : ℤ)) d,
              A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y')).re)
          + ∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re) / 2 by ring, abs_div, abs_two]
  have := abs_add_le ((∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re)
      - (∑ r ∈ Finset.Ioo (-(d : ℤ)) d,
          A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y')).re)
    (∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re)
  linarith

end FejerWeight

end RHTower
