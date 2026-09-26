import GaloisForLFunctions.RHTower.FermiNymanBoundedWitnessRigidity
import GaloisForLFunctions.RHTower.DeningerZetaLowerBound
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import Zeta23.FromPNTPlus.ZetaBounds

/-!
# Bounded witnesses of the alternating Nyman–Beurling system are dyadically self-similar

Let `w` be continuous and bounded on `(0,1]` with `∫_0^1 φ_a w = 0` for all `a ≥ 1`, where
`φ_a(t) = {1/(at)} − 2{1/(2at)}`.  The entire transform

`U(z) = 2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)`,  `V(z) = (1 − 2^{−z}) ∫_0^1 t^{z−1} w`,

equals `∫_0^1 u^{z−1}(w(u/2) − w(u)) du` on `Re z > 0` and
`(1 − z) Φ₀(1 − z)/ζ(1 − z) − 2^z ∫_{1/2}^1 t^{z−1} w` on `Re z < 1`.  The bounds
`1/ζ(σ + it) = O(log^{10}|t|)` on `1 − c/log⁹|t| < σ ≤ 2` together with the de la Vallée Poussin
zero-free region make `U` of polynomial growth, so `U` is a polynomial; it tends to zero along the
positive reals, so `U ≡ 0`.  Fourier uniqueness then gives `w(t/2) = w(t)` on `(0,1]`.

This is the `L^∞` endpoint of the `L^p` scale of the alternating system: for `p = 2` the same
statement (every square-integrable witness is dyadically self-similar) is equivalent to the Riemann
hypothesis.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower

variable {w : ℝ → ℂ} {M : ℝ}

/-! ## Reciprocal bounds for `ζ` near the one-line -/

theorem one_lt_log_of_three_lt {t : ℝ} (ht : 3 < |t|) : 1 < Real.log |t| := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem one_sub_eq_ofReal_add (z : ℂ) :
    (1 : ℂ) - z = ((1 - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- `1/‖ζ(σ + it)‖ ≤ B log^{10}|t|` for `1 ≤ σ ≤ 2`, `|t| > 3`. -/
theorem exists_inv_norm_zeta_le_right :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, 3 < |t| → 1 ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B * Real.log |t| ^ (10 : ℕ) := by
  obtain ⟨A, hA, C₁, hC₁, h1⟩ := ZetaInvBnd
  obtain ⟨C₂, hC₂, h2⟩ := ZetaInvBound2
  have hA0 : 0 < A := hA.1
  refine ⟨C₁ + C₂ / A, by positivity, fun σ t ht hσ1 hσ2 => ?_⟩
  have hL := one_lt_log_of_three_lt ht
  have hAL : 0 ≤ A / Real.log |t| ^ 9 := div_nonneg hA0.le (pow_nonneg (by linarith) 9)
  have key1 : σ < 1 + A / Real.log |t| ^ 9 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * Real.log |t| ^ (7 : ℝ) :=
    fun h => h1 σ t ht ⟨by linarith, h⟩
  have key2 : 1 < σ → 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      C₂ * (σ - 1) ^ (-(3 : ℝ) / 4) * Real.log |t| ^ ((1 : ℝ) / 4) :=
    fun h => h2 ⟨h, hσ2⟩ t ht
  generalize Real.log |t| = L at hL hAL key1 key2 ⊢
  generalize 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ = Z at key1 key2 ⊢
  have hL0 : 0 < L := by linarith
  have e7 : L ^ (7 : ℝ) = L ^ (7 : ℕ) := by exact_mod_cast Real.rpow_natCast L 7
  by_cases hσ : σ < 1 + A / L ^ 9
  · have hb := key1 hσ
    rw [e7] at hb
    have h710 : L ^ (7 : ℕ) ≤ L ^ (10 : ℕ) := pow_le_pow_right₀ hL.le (by norm_num)
    have : 0 ≤ C₂ / A * L ^ (10 : ℕ) := by positivity
    calc Z ≤ C₁ * L ^ (7 : ℕ) := hb
      _ ≤ C₁ * L ^ (10 : ℕ) := mul_le_mul_of_nonneg_left h710 hC₁.le
      _ ≤ (C₁ + C₂ / A) * L ^ (10 : ℕ) := by nlinarith
  · rw [not_lt] at hσ
    have hL9 : 0 < L ^ 9 := by positivity
    have hpos : 0 < A / L ^ 9 := by positivity
    have hu0 : 0 < σ - 1 := by linarith
    have hb := key2 (by linarith)
    have hr : (σ - 1) ^ (-(3 : ℝ) / 4) ≤ (σ - 1)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hu0 (by linarith) (by norm_num)
    have hinv : (σ - 1)⁻¹ ≤ L ^ 9 / A := by
      rw [inv_le_comm₀ hu0 (by positivity), inv_div]
      linarith
    have hq : L ^ ((1 : ℝ) / 4) ≤ L := by
      calc L ^ ((1 : ℝ) / 4) ≤ L ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL.le (by norm_num)
        _ = L := Real.rpow_one L
    have : 0 ≤ C₁ * L ^ (10 : ℕ) := by positivity
    calc Z ≤ C₂ * (σ - 1) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := hb
      _ ≤ C₂ * (L ^ 9 / A) * L :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hr.trans hinv) hC₂.le) hq
            (Real.rpow_nonneg hL0.le _) (by positivity)
      _ = C₂ / A * L ^ (10 : ℕ) := by field_simp
      _ ≤ (C₁ + C₂ / A) * L ^ (10 : ℕ) := by nlinarith

/-! ## Polynomial growth of `U` -/

/-- **`U` has polynomial growth.** -/
theorem IsBoundedFermiWitness.exists_growth (hw : IsBoundedFermiWitness w M) :
    ∃ K : ℝ, ∀ z : ℂ, ‖dyadicDefectTransform w z‖ ≤ K * (1 + ‖z‖) ^ (11 : ℕ) := by
  obtain ⟨B, hB, hBnd⟩ := exists_inv_norm_zeta_le_right
  obtain ⟨A₁, hA₁, C₁, hC₁, hInv⟩ := ZetaInvBnd
  obtain ⟨A₂, hA₂, hZF⟩ := ZetaZeroFree
  have hcpt : IsCompact (Icc (-1 : ℝ) 1 ×ℂ Icc (-3 : ℝ) 3) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨K₀, hK₀⟩ := hcpt.exists_bound_of_continuousOn
    hw.differentiable_dyadicDefectTransform.continuous.continuousOn
  have hA0 : 0 < min A₁ A₂ := lt_min hA₁.1 hA₂.1
  have hM := hw.nonneg
  have t1 : 0 ≤ |K₀| := abs_nonneg _
  have t2 : 0 ≤ 7 * M := by positivity
  have t3 : 0 ≤ 3 * M * B + M := by positivity
  have t4 : 0 ≤ 2 * M / min A₁ A₂ := by positivity
  have t5 : 0 ≤ 6 * M * C₁ + M := by have := hC₁.le; positivity
  refine ⟨|K₀| + 7 * M + (3 * M * B + M) + 2 * M / min A₁ A₂ + (6 * M * C₁ + M), fun z => ?_⟩
  have hR1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
  have fin : ∀ c : ℝ, 0 ≤ c →
      c ≤ |K₀| + 7 * M + (3 * M * B + M) + 2 * M / min A₁ A₂ + (6 * M * C₁ + M) →
      ∀ j ≤ 11, ‖dyadicDefectTransform w z‖ ≤ c * (1 + ‖z‖) ^ j →
      ‖dyadicDefectTransform w z‖ ≤
        (|K₀| + 7 * M + (3 * M * B + M) + 2 * M / min A₁ A₂ + (6 * M * C₁ + M)) *
          (1 + ‖z‖) ^ (11 : ℕ) := by
    intro c hc hcK j hj h
    refine h.trans (mul_le_mul hcK (pow_le_pow_right₀ hR1 hj) (by positivity) (by linarith))
  have h1z : ‖1 - z‖ ≤ 1 + ‖z‖ := (norm_sub_le _ _).trans (by simp)
  have hre1 : (1 - z).re = 1 - z.re := by simp
  have hζeq : riemannZeta (1 - z) =
      riemannZeta (((1 - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I) := by
    rw [← one_sub_eq_ofReal_add]
  -- the region `Re z ≥ 1`
  by_cases hx1 : 1 ≤ z.re
  · refine fin (7 * M) t2 (by linarith) 0 (by norm_num) ?_
    rw [pow_zero, mul_one]
    calc ‖dyadicDefectTransform w z‖ ≤ 2 * M / z.re :=
          hw.norm_dyadicDefectTransform_le_of_re_pos (by linarith)
      _ ≤ 2 * M := div_le_self (by linarith) hx1
      _ ≤ 7 * M := by linarith
  rw [not_le] at hx1
  -- the region `Re z ≤ −1`
  by_cases hxm : z.re ≤ -1
  · have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hxm; linarith
    have hb := hw.norm_dyadicDefectTransform_le_left hx1 hz0 (fun h => absurd h (by linarith))
    have hζ : (1 : ℝ) / 4 ≤ ‖riemannZeta (1 - z)‖ :=
      norm_riemannZeta_ge_of_two_le_re (by rw [hre1]; linarith)
    have hinv : 1 / ‖riemannZeta (1 - z)‖ ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hΦ : 3 * M / (1 - z.re) ≤ 3 * M / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    refine fin (7 * M) t2 (by linarith) 1 (by norm_num) ?_
    calc ‖dyadicDefectTransform w z‖
        ≤ ‖1 - z‖ * (3 * M / (1 - z.re)) * (1 / ‖riemannZeta (1 - z)‖) + M := hb
      _ ≤ (1 + ‖z‖) * (3 * M / 2) * 4 + M := by
          gcongr
      _ ≤ 7 * M * (1 + ‖z‖) ^ 1 := by rw [pow_one]; nlinarith
  rw [not_le] at hxm
  -- the compact region
  by_cases hy : |z.im| ≤ 3
  · refine fin |K₀| t1 (by linarith) 0 (by norm_num) ?_
    rw [pow_zero, mul_one]
    exact (hK₀ z ⟨⟨hxm.le, hx1.le⟩, abs_le.1 hy⟩).trans (le_abs_self _)
  rw [not_le] at hy
  have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_im, abs_zero] at hy; linarith
  have hy' : 3 < |-z.im| := by rwa [abs_neg]
  have hL := one_lt_log_of_three_lt hy
  have hLR : Real.log |z.im| ≤ 1 + ‖z‖ := by
    have := Real.log_le_sub_one_of_pos (show 0 < |z.im| by linarith)
    linarith [Complex.abs_im_le_norm z]
  have hLpow : ∀ k : ℕ, Real.log |z.im| ^ k ≤ (1 + ‖z‖) ^ k :=
    fun k => pow_le_pow_left₀ (by linarith) hLR k
  -- the region `−1 < Re z ≤ 0`
  by_cases hx0 : z.re ≤ 0
  · have hb := hw.norm_dyadicDefectTransform_le_left hx1 hz0 (fun h => absurd h (by linarith))
    have hinv : 1 / ‖riemannZeta (1 - z)‖ ≤ B * Real.log |z.im| ^ (10 : ℕ) := by
      have := hBnd (1 - z.re) (-z.im) hy' (by linarith) (by linarith)
      rwa [abs_neg, ← hζeq] at this
    have hΦ : 3 * M / (1 - z.re) ≤ 3 * M :=
      div_le_self (by positivity) (by linarith)
    refine fin (3 * M * B + M) t3 (by linarith) 11 le_rfl ?_
    have hR10 := hLpow 10
    calc ‖dyadicDefectTransform w z‖
        ≤ ‖1 - z‖ * (3 * M / (1 - z.re)) * (1 / ‖riemannZeta (1 - z)‖) + M := hb
      _ ≤ (1 + ‖z‖) * (3 * M) * (B * (1 + ‖z‖) ^ (10 : ℕ)) + M * 1 := by
          rw [mul_one]
          refine add_le_add (mul_le_mul (mul_le_mul h1z hΦ
            (div_nonneg (by linarith) (by linarith)) (by linarith))
            (hinv.trans (mul_le_mul_of_nonneg_left hR10 hB)) (by positivity)
            (mul_nonneg (by linarith) (by linarith))) le_rfl
      _ ≤ (3 * M * B + M) * (1 + ‖z‖) ^ 11 := by
          have hp : 1 ≤ (1 + ‖z‖) ^ 11 := one_le_pow₀ hR1
          have e : (1 + ‖z‖) * (3 * M) * (B * (1 + ‖z‖) ^ (10 : ℕ)) =
              3 * M * B * (1 + ‖z‖) ^ 11 := by ring
          rw [e]
          have : M * 1 ≤ M * (1 + ‖z‖) ^ 11 := mul_le_mul_of_nonneg_left hp hM
          nlinarith
  rw [not_le] at hx0
  set A := min A₁ A₂ with hAdef
  have hL9 : 1 ≤ Real.log |z.im| ^ 9 := one_le_pow₀ hL.le
  have hL9pos : 0 < Real.log |z.im| ^ 9 := by linarith
  -- the region `0 < Re z`, away from the imaginary axis
  by_cases hxA : A / Real.log |z.im| ^ 9 ≤ z.re
  · refine fin (2 * M / A) t4 (by linarith) 9 (by norm_num) ?_
    have hb := hw.norm_dyadicDefectTransform_le_of_re_pos hx0
    have hApos : 0 < A / Real.log |z.im| ^ 9 := by positivity
    calc ‖dyadicDefectTransform w z‖ ≤ 2 * M / z.re := hb
      _ ≤ 2 * M / (A / Real.log |z.im| ^ 9) :=
          div_le_div_of_nonneg_left (by positivity) hApos hxA
      _ = 2 * M / A * Real.log |z.im| ^ 9 := by field_simp
      _ ≤ 2 * M / A * (1 + ‖z‖) ^ 9 := mul_le_mul_of_nonneg_left (hLpow 9) t4
  rw [not_le] at hxA
  -- the thin strip `0 < Re z < A/log⁹|t|`: the zero-free region
  have hAA₁ : A ≤ A₁ := min_le_left _ _
  have hAA₂ : A ≤ A₂ := min_le_right _ _
  have hA12 : A ≤ 1 / 2 := hAA₁.trans hA₁.2
  have hsmall : A / Real.log |z.im| ^ 9 ≤ 1 / 2 := by
    rw [div_le_iff₀ hL9pos]; nlinarith
  have hlow₂ : 1 - A₂ / Real.log |z.im| ^ 9 ≤ 1 - z.re := by
    have : A / Real.log |z.im| ^ 9 ≤ A₂ / Real.log |z.im| ^ 9 :=
      div_le_div_of_nonneg_right hAA₂ hL9pos.le
    linarith
  have hlow₁ : 1 - A₁ / Real.log |z.im| ^ 9 ≤ 1 - z.re := by
    have : A / Real.log |z.im| ^ 9 ≤ A₁ / Real.log |z.im| ^ 9 :=
      div_le_div_of_nonneg_right hAA₁ hL9pos.le
    linarith
  have hup₁ : 1 - z.re < 1 + A₁ / Real.log |z.im| ^ 9 := by
    have : 0 < A₁ / Real.log |z.im| ^ 9 := div_pos hA₁.1 hL9pos
    linarith
  have hne : riemannZeta (1 - z) ≠ 0 := by
    have := hZF (1 - z.re) (-z.im) hy' ⟨by rwa [abs_neg], by linarith⟩
    rwa [← hζeq] at this
  have hinv : 1 / ‖riemannZeta (1 - z)‖ ≤ C₁ * Real.log |z.im| ^ (7 : ℕ) := by
    have := hInv (1 - z.re) (-z.im) hy' ⟨by rwa [abs_neg], by rwa [abs_neg]⟩
    rw [abs_neg, ← hζeq] at this
    have e7 : Real.log |z.im| ^ (7 : ℝ) = Real.log |z.im| ^ (7 : ℕ) := by
      exact_mod_cast Real.rpow_natCast _ 7
    rwa [e7] at this
  have hb := hw.norm_dyadicDefectTransform_le_left hx1 hz0 (fun _ => hne)
  have hΦ : 3 * M / (1 - z.re) ≤ 6 * M := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  refine fin (6 * M * C₁ + M) t5 (by linarith) 8 (by norm_num) ?_
  calc ‖dyadicDefectTransform w z‖
      ≤ ‖1 - z‖ * (3 * M / (1 - z.re)) * (1 / ‖riemannZeta (1 - z)‖) + M := hb
    _ ≤ (1 + ‖z‖) * (6 * M) * (C₁ * (1 + ‖z‖) ^ (7 : ℕ)) + M * 1 := by
        rw [mul_one]
        refine add_le_add (mul_le_mul (mul_le_mul h1z hΦ
          (div_nonneg (by linarith) (by linarith)) (by linarith))
          (hinv.trans (mul_le_mul_of_nonneg_left (hLpow 7) hC₁.le)) (by positivity)
          (mul_nonneg (by linarith) (by linarith))) le_rfl
    _ ≤ (6 * M * C₁ + M) * (1 + ‖z‖) ^ 8 := by
        have hp : 1 ≤ (1 + ‖z‖) ^ 8 := one_le_pow₀ hR1
        have e : (1 + ‖z‖) * (6 * M) * (C₁ * (1 + ‖z‖) ^ (7 : ℕ)) =
            6 * M * C₁ * (1 + ‖z‖) ^ 8 := by ring
        rw [e]
        have : M * 1 ≤ M * (1 + ‖z‖) ^ 8 := mul_le_mul_of_nonneg_left hp hM
        nlinarith

/-! ## `U ≡ 0` -/

/-- **The transform vanishes identically.**  By Liouville `U` is a polynomial, and it tends to zero
along the positive reals. -/
theorem IsBoundedFermiWitness.dyadicDefectTransform_eq_zero (hw : IsBoundedFermiWitness w M)
    (z : ℂ) : dyadicDefectTransform w z = 0 := by
  obtain ⟨K, hK⟩ := hw.exists_growth
  obtain ⟨p, hp⟩ := GaloisForLFunctions.HTGeometry.exists_polynomial_of_polynomial_growth
    hw.differentiable_dyadicDefectTransform hK
  have hreal : ∀ x : ℝ, 0 < x → ‖p.eval (x : ℂ)‖ ≤ 2 * M / x := by
    intro x hx
    rw [← hp]
    have := hw.norm_dyadicDefectTransform_le_of_re_pos (z := (x : ℂ)) (by simpa using hx)
    simpa using this
  have hdeg : p.degree ≤ 0 := by
    by_contra hdeg
    rw [not_le] at hdeg
    have ht := p.tendsto_norm_atTop hdeg (l := atTop) (z := fun x : ℝ => (x : ℂ))
      (by simpa [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop)
    obtain ⟨x, hx1, hx2⟩ :=
      ((ht.eventually_gt_atTop (2 * M)).and (eventually_ge_atTop (1 : ℝ))).exists
    have h1 := hreal x (by linarith)
    have h2 : 2 * M / x ≤ 2 * M := div_le_self (by linarith [hw.nonneg]) hx2
    linarith
  have hpC := Polynomial.eq_C_of_degree_le_zero hdeg
  have hc : p.coeff 0 = 0 := by
    have hlim : Tendsto (fun x : ℝ => 2 * M / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hle : ∀ᶠ x : ℝ in atTop, ‖p.coeff 0‖ ≤ 2 * M / x := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have := hreal x hx
      rwa [hpC, Polynomial.eval_C] at this
    exact norm_le_zero_iff.1 (ge_of_tendsto hlim hle)
  rw [hp, hpC, Polynomial.eval_C, hc]

/-! ## Fourier uniqueness -/

/-- The dilation defect `w(u/2) − w(u)` on `(0,1]`, extended by zero. -/
def dilationDefect (w : ℝ → ℂ) : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator (fun u => w (u / 2) - w u)

theorem IsBoundedFermiWitness.mellin_dilationDefect (hw : IsBoundedFermiWitness w M) {z : ℂ}
    (hz : 0 < z.re) : mellin (dilationDefect w) z = 0 := by
  unfold dilationDefect
  rw [mellin_indicator_eq_setIntegral le_rfl, ← hw.dyadicDefectTransform_eq_of_re_pos hz,
    hw.dyadicDefectTransform_eq_zero]

theorem IsBoundedFermiWitness.measurable_dilationDefect (hw : IsBoundedFermiWitness w M) :
    Measurable (dilationDefect w) := by
  have heq : dilationDefect w =
      (Ioc (0 : ℝ) 1).indicator (fun u => unitExt w (u / 2) - unitExt w u) := by
    funext u
    unfold dilationDefect
    by_cases hu : u ∈ Ioc (0 : ℝ) 1
    · have hu2 : u / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      simp only [Set.indicator_of_mem hu, unitExt, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
  rw [heq]
  exact ((hw.measurable_unitExt.comp (measurable_id.div_const 2)).sub
    hw.measurable_unitExt).indicator measurableSet_Ioc

theorem IsBoundedFermiWitness.norm_dilationDefect_le (hw : IsBoundedFermiWitness w M) (v : ℝ) :
    ‖dilationDefect w v‖ ≤ 2 * M := by
  unfold dilationDefect
  by_cases hv : v ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hv]
    have h1 := hw.bound (v / 2) ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have h2 := hw.bound v hv
    calc ‖w (v / 2) - w v‖ ≤ ‖w (v / 2)‖ + ‖w v‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  · rw [Set.indicator_of_notMem hv, norm_zero]; linarith [hw.nonneg]

theorem IsBoundedFermiWitness.dilationDefect_eq_zero_of_mem_Ioo (hw : IsBoundedFermiWitness w M)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : w (t / 2) - w t = 0 := by
  set h : ℝ → ℂ := fun u => Real.exp (-1 * u) • dilationDefect w (Real.exp (-u)) with hh
  have hF : ∀ ξ : ℝ, 𝓕 h ξ = 0 := by
    intro ξ
    have := hw.mellin_dilationDefect (z := 1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) (by simp)
    rw [mellin_eq_fourier] at this
    have hre : (1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I).re = 1 := by simp
    have him : (1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I).im / (2 * Real.pi) = ξ := by
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
      field_simp
    rw [hre, him] at this
    exact this
  have hmeas : Measurable h :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
      (hw.measurable_dilationDefect.comp (Real.measurable_exp.comp measurable_neg))
  have hsupp : ∀ u : ℝ, u < 0 → h u = 0 := by
    intro u hu
    simp only [hh]
    rw [dilationDefect, Set.indicator_of_notMem, smul_zero]
    intro hm
    have := Real.exp_le_one_iff.1 hm.2
    linarith
  have hint : Integrable h := by
    have hb : Integrable ((Ici (0 : ℝ)).indicator (fun u => 2 * M * Real.exp (-1 * u))) := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
      exact ((integrableOn_Ici_iff_integrableOn_Ioi).2
        (exp_neg_integrableOn_Ioi 0 one_pos)).const_mul _
    refine hb.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    by_cases hu : u < 0
    · rw [hsupp u hu, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by have := hw.nonneg; positivity) u
    · rw [not_lt] at hu
      rw [Set.indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu)]
      simp only [hh, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_comm (2 * M)]
      exact mul_le_mul_of_nonneg_left (hw.norm_dilationDefect_le _) (Real.exp_pos _).le
  have hae := HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hint hF
  have hmaps : MapsTo (fun u : ℝ => Real.exp (-u)) (Ioi 0) (Ioc 0 1) := fun u hu =>
    ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (by linarith [show (0 : ℝ) < u from hu])⟩
  have hmaps2 : MapsTo (fun u : ℝ => Real.exp (-u) / 2) (Ioi 0) (Ioc 0 1) := fun u hu =>
    ⟨by have := Real.exp_pos (-u); positivity, by linarith [(hmaps hu).2]⟩
  have hc1 : ContinuousOn (fun u : ℝ => w (Real.exp (-u))) (Ioi 0) :=
    hw.cont.comp (Real.continuous_exp.comp continuous_neg).continuousOn hmaps
  have hc2 : ContinuousOn (fun u : ℝ => w (Real.exp (-u) / 2)) (Ioi 0) :=
    hw.cont.comp ((Real.continuous_exp.comp continuous_neg).div_const 2).continuousOn hmaps2
  have hcont : ContinuousOn h (Ioi 0) := by
    refine ContinuousOn.congr
      (f := fun u => Real.exp (-1 * u) • (w (Real.exp (-u) / 2) - w (Real.exp (-u)))) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.smul
        (hc2.sub hc1)
    · intro u hu
      simp only [hh, dilationDefect]
      rw [Set.indicator_of_mem (hmaps hu)]
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_Ioi hcont
    continuousOn_const
  have hu : (0 : ℝ) < -Real.log t := by have := Real.log_neg ht.1 ht.2; linarith
  have := heq hu
  simp only [hh, Pi.zero_apply, neg_neg, neg_mul, one_mul, Real.exp_log ht.1] at this
  rw [dilationDefect, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩),
    smul_eq_zero] at this
  rcases this with h0 | h0
  · exact absurd h0 ht.1.ne'
  · exact h0

/-- **Bounded witnesses are dyadically self-similar:** `w(t/2) = w(t)` on `(0,1]`. -/
theorem IsBoundedFermiWitness.selfSimilar (hw : IsBoundedFermiWitness w M) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    have hmaps : MapsTo (fun u : ℝ => u / 2) (Ioc 0 1) (Ioc 0 1) := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hg : ContinuousOn (fun u => w (u / 2) - w u) (Ioc 0 1) :=
      (hw.cont.comp (continuousOn_id.div_const 2) hmaps).sub hw.cont
    have hg' := (hg 1 ht).mono_of_mem_nhdsWithin (s := Iio 1)
      (mem_of_superset (Ioo_mem_nhdsLT (zero_lt_one' ℝ)) Ioo_subset_Ioc_self)
    have hev : (fun u => w (u / 2) - w u) =ᶠ[𝓝[<] (1 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with u hu
      exact hw.dilationDefect_eq_zero_of_mem_Ioo hu
    exact sub_eq_zero.1 (tendsto_nhds_unique (hg'.tendsto.congr' hev) tendsto_const_nhds)
  · exact sub_eq_zero.1 (hw.dilationDefect_eq_zero_of_mem_Ioo ⟨ht.1, h1⟩)

/-- **The `L^∞` endpoint for the Hermitian witness class.**  A bounded witness of the alternating
Nyman–Beurling system is dyadically self-similar. -/
theorem IsFermiNymanWitness.selfSimilar_of_bounded {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    {M : ℝ} (hM : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w (t / 2) = w t := by
  have hb : IsBoundedFermiWitness (fun u => (starRingEnd ℂ) (w u)) M :=
    { cont := Complex.continuous_conj.comp_continuousOn hw.1
      bound := fun u hu => by rw [Complex.norm_conj]; exact hM u hu
      orth := fun a ha => hw.2.2 a ha }
  have := congrArg (starRingEnd ℂ) (hb.selfSimilar ht)
  simpa using this

end RHTower
