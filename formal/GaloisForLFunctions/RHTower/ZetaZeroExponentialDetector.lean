import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorRectangle
import GaloisForLFunctions.RHTower.ExponentialMellinPerron
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgeMeanSquare
import GaloisForLFunctions.RHTower.Sieve.InghamGabrielPoleClearedBound

/-!
# The exponentially smoothed zero detector

Let `ρ` be a zero of `ζ` with `0 < Re ρ < 1`, `X ≥ 1`, `Y ≥ 1`, and let `D = 1 - μ_{≤X} ⋆ 1` be the
Möbius truncation defect, so that `Σ D(n) n^{-s} = 1 - M_X(s) ζ(s)` and `D(n) = 0` for `n ≤ X`.
For every `-1/2 ≤ c < 0`,

`Σ_n D(n) n^{-ρ} e^{-n/Y} = 1 - Y^{1-ρ} Γ(1-ρ) M_X(1) + (1/2π) ∫_ℝ F(c + iy) dy`,

with `F(w) = Y^w Γ(w) (1 - M_X(ρ+w) ζ(ρ+w))`.  The left side is the Cahen–Mellin integral of `F` on
`Re w = 2` (`mellinInv_gamma_mul_LSeries_eq_tsum_exp`); the rectangle residue identity
`rectIntegral_expDetIntegrand` moves the line to `Re w = c`.  The horizontal edges vanish and both
lines are integrable because `|Γ(w)| ≪ |y|^N e^{-π|y|/2}` while `ζ` and `M_X` grow at most
polynomially (`exists_bound_norm_expDetIntegrand`).

This is the zero-detection identity behind Montgomery's form of the zero-density method: either the
Dirichlet polynomial on the left is large, or the integral over the line `Re(ρ + w) = Re ρ + c` is.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

/-- `|y|^N e^{-π|y|/2} ≤ 4^N N! e^{-|y|}`. -/
theorem abs_pow_mul_exp_neg_pi_le (N : ℕ) (y : ℝ) :
    |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) ≤
      4 ^ N * (N.factorial : ℝ) * Real.exp (-|y|) := by
  have hy : 0 ≤ |y| / 4 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (|y| / 4) hy N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h2 : |y| ^ N ≤ 4 ^ N * (N.factorial : ℝ) * Real.exp (|y| / 4) := by
    rw [div_le_iff₀ hf, div_pow, div_le_iff₀ (by positivity)] at h1
    calc |y| ^ N ≤ Real.exp (|y| / 4) * (N.factorial : ℝ) * 4 ^ N := h1
      _ = 4 ^ N * (N.factorial : ℝ) * Real.exp (|y| / 4) := by ring
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h3 : Real.exp (|y| / 4) * Real.exp (-(Real.pi * |y| / 2)) ≤ Real.exp (-|y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg y]
  calc |y| ^ N * Real.exp (-(Real.pi * |y| / 2))
      ≤ (4 ^ N * (N.factorial : ℝ) * Real.exp (|y| / 4)) * Real.exp (-(Real.pi * |y| / 2)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 4 ^ N * (N.factorial : ℝ) *
          (Real.exp (|y| / 4) * Real.exp (-(Real.pi * |y| / 2))) := by ring
    _ ≤ 4 ^ N * (N.factorial : ℝ) * Real.exp (-|y|) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **Decay of the detector integrand.**  For `1/2 ≤ Re ρ ≤ 1`, on `-1/2 ≤ Re w ≤ 2` and
`|Im w| ≥ |Im ρ| + 1`,
`|F(w)| ≤ K |Im w|^N e^{-π|Im w|/2}`. -/
theorem exists_bound_norm_expDetIntegrand (X : ℕ) (ρ : ℂ) (hβ0 : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧ ∀ x y : ℝ, -1 / 2 ≤ x → x ≤ 2 → |ρ.im| + 1 ≤ |y| →
      ‖expDetIntegrand X ρ Y ((x : ℂ) + (y : ℂ) * I)‖ ≤
        K * |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (show (0 : ℝ) < 1 / 2 by norm_num) 3
  obtain ⟨Cζ, Nζ, hCζ, hζ⟩ := exists_bound_norm_riemannZeta_strip 3
  refine ⟨Y ^ (2 : ℝ) * CΓ * (1 + X * Cζ * 2 ^ Nζ), NΓ + Nζ, by positivity, ?_⟩
  intro x y hx1 hx2 hy
  have hY0 : 0 < Y := by linarith
  have hy1 : 1 ≤ |y| := by linarith [abs_nonneg ρ.im]
  set w : ℂ := (x : ℂ) + (y : ℂ) * I with hw
  have hwre : w.re = x := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  -- the power of `Y`
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0, hwre]
    exact Real.rpow_le_rpow_of_exponent_le hY hx2
  -- the Gamma factor through `Γ(w) = Γ(w+1)/w`
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [hwim] at this
    simp at this
    rw [this, abs_zero] at hy1
    linarith
  have hnormw : |y| ≤ ‖w‖ := by
    rw [← hwim]
    exact Complex.abs_im_le_norm w
  have hΓw : ‖Complex.Gamma w‖ ≤ CΓ * |y| ^ NΓ * Real.exp (-(Real.pi * |y| / 2)) := by
    have hrel : Complex.Gamma w = Complex.Gamma (w + 1) / w := by
      rw [Complex.Gamma_add_one w hw0]
      field_simp
    have hw1 : w + 1 = ((x + 1 : ℝ) : ℂ) + (y : ℂ) * I := by
      rw [hw]
      push_cast
      ring
    have hb := hΓ (x + 1) y (by linarith) (by linarith) hy1
    rw [← hw1] at hb
    rw [hrel, norm_div]
    have hnw : 1 ≤ ‖w‖ := le_trans hy1 hnormw
    calc ‖Complex.Gamma (w + 1)‖ / ‖w‖ ≤ ‖Complex.Gamma (w + 1)‖ :=
          div_le_self (norm_nonneg _) hnw
      _ ≤ CΓ * |y| ^ NΓ * Real.exp (-(Real.pi * |y| / 2)) := hb
  -- the zeta factor
  have hs : ρ + w = ((ρ.re + x : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hw]
  have hγy1 : 1 ≤ |ρ.im + y| := by
    have := abs_sub_abs_le_abs_sub y (-ρ.im)
    rw [abs_neg, sub_neg_eq_add, add_comm y] at this
    linarith
  have hγy2 : |ρ.im + y| ≤ 2 * |y| := by
    have := abs_add_le ρ.im y
    linarith
  have hζw : ‖riemannZeta (ρ + w)‖ ≤ Cζ * (2 ^ Nζ * |y| ^ Nζ) := by
    rw [hs]
    have hσ : |ρ.re + x| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith
    refine le_trans (hζ (ρ.re + x) (ρ.im + y) hσ hγy1) ?_
    apply mul_le_mul_of_nonneg_left _ hCζ
    calc |ρ.im + y| ^ Nζ ≤ (2 * |y|) ^ Nζ := pow_le_pow_left₀ (abs_nonneg _) hγy2 _
      _ = 2 ^ Nζ * |y| ^ Nζ := by rw [mul_pow]
  have hM : ‖Sieve.inghamMollifier X (ρ + w)‖ ≤ X :=
    Sieve.norm_inghamMollifier_le_nat X (by rw [add_re, hwre]; linarith)
  have hyN : 1 ≤ |y| ^ Nζ := one_le_pow₀ hy1
  have hfac : ‖1 - Sieve.inghamMollifier X (ρ + w) * riemannZeta (ρ + w)‖ ≤
      (1 + X * Cζ * 2 ^ Nζ) * |y| ^ Nζ := by
    calc ‖1 - Sieve.inghamMollifier X (ρ + w) * riemannZeta (ρ + w)‖
        ≤ 1 + ‖Sieve.inghamMollifier X (ρ + w)‖ * ‖riemannZeta (ρ + w)‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          rw [norm_one, norm_mul]
      _ ≤ 1 + X * (Cζ * (2 ^ Nζ * |y| ^ Nζ)) := by
          gcongr
      _ ≤ |y| ^ Nζ + X * Cζ * 2 ^ Nζ * |y| ^ Nζ := by nlinarith
      _ = (1 + X * Cζ * 2 ^ Nζ) * |y| ^ Nζ := by ring
  unfold expDetIntegrand
  rw [norm_mul, norm_mul]
  have hE : 0 ≤ Real.exp (-(Real.pi * |y| / 2)) := (Real.exp_pos _).le
  calc ‖(Y : ℂ) ^ w‖ * ‖Complex.Gamma w‖ *
        ‖1 - Sieve.inghamMollifier X (ρ + w) * riemannZeta (ρ + w)‖
      ≤ Y ^ (2 : ℝ) * (CΓ * |y| ^ NΓ * Real.exp (-(Real.pi * |y| / 2))) *
          ((1 + X * Cζ * 2 ^ Nζ) * |y| ^ Nζ) := by
        gcongr
    _ = Y ^ (2 : ℝ) * CΓ * (1 + X * Cζ * 2 ^ Nζ) * |y| ^ (NΓ + Nζ) *
          Real.exp (-(Real.pi * |y| / 2)) := by
        rw [pow_add]
        ring

/-- The detector integrand is continuous along every vertical line `Re w = x` with `x` not a
nonpositive integer and `Re ρ + x ≠ 1`. -/
theorem continuous_expDetIntegrand_line (X : ℕ) (ρ : ℂ) {Y : ℝ} (hY : 0 < Y) {x : ℝ}
    (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) (hxρ : ρ.re + x ≠ 1) :
    Continuous fun y : ℝ => expDetIntegrand X ρ Y ((x : ℂ) + (y : ℂ) * I) := by
  have hline : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I := by fun_prop
  refine continuous_iff_continuousAt.mpr fun y => ?_
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (x : ℂ) + (y : ℂ) * I := ⟨_, rfl⟩
  have hwre : w.re = x := by simp [hw]
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ w) w :=
    (differentiableAt_id).const_cpow (Or.inl hY0)
  have hΓ : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    rw [hwre] at this
    simp at this
    exact hx m this
  have hM : DifferentiableAt ℂ (fun w : ℂ => Sieve.inghamMollifier X (ρ + w)) w :=
    ((Sieve.analyticAt_inghamMollifier X (ρ + w)).differentiableAt).comp w
      ((differentiableAt_id).const_add ρ)
  have hζ : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (ρ + w)) w := by
    have hne : ρ + w ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [add_re, hwre, one_re] at this
      exact hxρ this
    exact (differentiableAt_riemannZeta hne).comp w ((differentiableAt_id).const_add ρ)
  have hF : DifferentiableAt ℂ (expDetIntegrand X ρ Y) w := by
    unfold expDetIntegrand
    exact (hpow.mul hΓ).mul ((differentiableAt_const _).sub (hM.mul hζ))
  rw [hw] at hF
  exact ContinuousAt.comp (g := expDetIntegrand X ρ Y) hF.continuousAt hline.continuousAt

/-- **Integrability along a vertical line** `Re w = x`, `-1/2 ≤ x ≤ 2`. -/
theorem integrable_expDetIntegrand_line (X : ℕ) (ρ : ℂ) (hβ0 : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) {x : ℝ} (hx1 : -1 / 2 ≤ x) (hx2 : x ≤ 2)
    (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) (hxρ : ρ.re + x ≠ 1) :
    Integrable fun y : ℝ => expDetIntegrand X ρ Y ((x : ℂ) + (y : ℂ) * I) := by
  obtain ⟨K, N, hK, hb⟩ := exists_bound_norm_expDetIntegrand X ρ hβ0 hβ1 hY
  have hcont := continuous_expDetIntegrand_line X ρ (by linarith : (0 : ℝ) < Y) hx hxρ
  set R : ℝ := |ρ.im| + 1 with hR
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  set B : ℝ := |M₁| * Real.exp R + K * (4 ^ N * (N.factorial : ℝ)) with hB
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul B)
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hE : 0 < Real.exp (-(1 * |y|)) := Real.exp_pos _
  have hfac : (0 : ℝ) ≤ 4 ^ N * (N.factorial : ℝ) := by positivity
  rw [one_mul]
  by_cases hy : |y| ≤ R
  · have hyI : y ∈ Icc (-R) R := abs_le.mp hy
    have h1 := hM₁ y hyI
    have h2 : 1 ≤ Real.exp R * Real.exp (-|y|) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖expDetIntegrand X ρ Y ((x : ℂ) + (y : ℂ) * I)‖ ≤ |M₁| := le_trans h1 (le_abs_self _)
      _ ≤ |M₁| * (Real.exp R * Real.exp (-|y|)) := le_mul_of_one_le_right (abs_nonneg _) h2
      _ ≤ B * Real.exp (-|y|) := by
          rw [hB]
          nlinarith [Real.exp_pos (-|y|), mul_nonneg hK hfac]
  · push Not at hy
    have h1 := hb x y hx1 hx2 hy.le
    have h2 := abs_pow_mul_exp_neg_pi_le N y
    calc ‖expDetIntegrand X ρ Y ((x : ℂ) + (y : ℂ) * I)‖
        ≤ K * (|y| ^ N * Real.exp (-(Real.pi * |y| / 2))) := by rw [← mul_assoc]; exact h1
      _ ≤ K * (4 ^ N * (N.factorial : ℝ) * Real.exp (-|y|)) := mul_le_mul_of_nonneg_left h2 hK
      _ ≤ B * Real.exp (-|y|) := by
          rw [hB]
          have : 0 ≤ |M₁| * Real.exp R * Real.exp (-|y|) := by positivity
          nlinarith

/-- The horizontal edges are `O(|y|^N e^{-π|y|/2})`. -/
theorem exists_bound_norm_integral_expDetIntegrand_horizontal (X : ℕ) (ρ : ℂ)
    (hβ0 : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧ ∀ c : ℝ, -1 / 2 ≤ c → c ≤ 2 → ∀ y : ℝ, |ρ.im| + 1 ≤ |y| →
      ‖∫ x in c..2, expDetIntegrand X ρ Y ((x : ℂ) + (y : ℂ) * I)‖ ≤
        K * |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) * |2 - c| := by
  obtain ⟨K, N, hK, hb⟩ := exists_bound_norm_expDetIntegrand X ρ hβ0 hβ1 hY
  refine ⟨K, N, hK, fun c hc1 hc2 y hy => ?_⟩
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hc2] at hx
  exact hb x y (by linarith [hx.1]) hx.2 hy

/-- `K H^N e^{-πH/2} → 0`. -/
theorem tendsto_const_mul_pow_mul_exp_neg_pi (K : ℝ) (N : ℕ) :
    Tendsto (fun H : ℝ => K * H ^ N * Real.exp (-(Real.pi * H / 2))) atTop (𝓝 0) := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp
    (tendsto_id.const_mul_atTop hpi)).const_mul (K * (2 / Real.pi) ^ N)
  rw [mul_zero] at h
  refine h.congr fun H => ?_
  simp only [Function.comp_apply, id]
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [mul_pow]
  have e : Real.pi / 2 * H = Real.pi * H / 2 := by ring
  rw [e]
  have e2 : (2 / Real.pi) ^ N * (Real.pi / 2) ^ N = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  calc K * (2 / Real.pi) ^ N * ((Real.pi / 2) ^ N * H ^ N * Real.exp (-(Real.pi * H / 2)))
      = K * ((2 / Real.pi) ^ N * (Real.pi / 2) ^ N) * H ^ N * Real.exp (-(Real.pi * H / 2)) := by
        ring
    _ = K * H ^ N * Real.exp (-(Real.pi * H / 2)) := by rw [e2, mul_one]

/-- **The contour shift.**  For `1/2 ≤ Re ρ < 1` a zero of `ζ`, `Y ≥ 1` and `-1/2 ≤ c < 0`,
`∫ F(2 + iy) dy - ∫ F(c + iy) dy = 2π (1 - Y^{1-ρ}Γ(1-ρ)M_X(1))`. -/
theorem integral_expDetIntegrand_two_sub_line (X : ℕ) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ0 : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re < 1) {Y : ℝ} (hY : 1 ≤ Y) {c : ℝ} (hc1 : -1 / 2 ≤ c)
    (hc0 : c < 0) :
    (∫ y : ℝ, expDetIntegrand X ρ Y (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        ∫ y : ℝ, expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I) =
      2 * Real.pi * (1 + expDetZetaResidue X ρ Y) := by
  have hY0 : 0 < Y := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, one_re] at hβ1
    exact lt_irrefl _ hβ1
  have hint2 := integrable_expDetIntegrand_line X ρ hβ0 hβ1.le hY (x := 2) (by norm_num)
    le_rfl (fun m hm => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith) (by linarith)
  have hintc := integrable_expDetIntegrand_line X ρ hβ0 hβ1.le hY (x := c) hc1 (by linarith)
    (fun m hm => by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, Nat.cast_zero, neg_zero] at hm
        linarith
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
        linarith) (by linarith)
  obtain ⟨K, N, hK, hhor⟩ :=
    exists_bound_norm_integral_expDetIntegrand_horizontal X ρ hβ0 hβ1.le hY
  set F := expDetIntegrand X ρ Y with hF
  set A : ℝ → ℂ := fun H =>
    ((∫ x in c..2, F ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) - ∫ x in c..2, F ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y in (-H)..H, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      I • ∫ y in (-H)..H, F ((c : ℂ) + (y : ℂ) * I) with hA
  -- the rectangle identity for every large height
  have hrect : ∀ᶠ H : ℝ in atTop, A H = 2 * Real.pi * I * (1 + expDetZetaResidue X ρ Y) := by
    filter_upwards [eventually_gt_atTop (|ρ.im| + 1)] with H hH
    have hH0 : 0 < H := by linarith [abs_nonneg ρ.im]
    have hγ : |ρ.im| < H := by linarith
    have h := rectIntegral_expDetIntegrand X hρ hρ1 (by linarith) hY0
      (z₁ := ⟨c, -H⟩) (z₂ := ⟨2, H⟩) (by simp only; linarith) (by simp only; linarith)
      (by simp only; norm_num) (by simp only; linarith) (by simp only; linarith)
      (by simp only [sub_re, one_re]; linarith) (by simp only [sub_re, one_re]; linarith)
      (by simp only [sub_im, one_im, zero_sub]; linarith [le_abs_self ρ.im])
      (by simp only [sub_im, one_im, zero_sub]; linarith [neg_le_abs ρ.im])
    rw [← h]
    simp only [hA, rectIntegral, hF]
  -- the limit of the rectangle expression
  have hbot : Tendsto (fun H : ℝ => ∫ x in c..2, F ((x : ℂ) + ((-H : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_mul_pow_mul_exp_neg_pi K N).mul_const |2 - c|
      |>.trans (by rw [zero_mul]))
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with H hH
    have hH0 : 0 ≤ H := by linarith [abs_nonneg ρ.im]
    have h := hhor c hc1 (by linarith) (-H) (by rw [abs_neg, abs_of_nonneg hH0]; exact hH)
    rwa [abs_neg, abs_of_nonneg hH0] at h
  have htop : Tendsto (fun H : ℝ => ∫ x in c..2, F ((x : ℂ) + (H : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_mul_pow_mul_exp_neg_pi K N).mul_const |2 - c|
      |>.trans (by rw [zero_mul]))
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with H hH
    have hH0 : 0 ≤ H := by linarith [abs_nonneg ρ.im]
    have h := hhor c hc1 (by linarith) H (by rw [abs_of_nonneg hH0]; exact hH)
    rwa [abs_of_nonneg hH0] at h
  have hright := intervalIntegral_tendsto_integral hint2 tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral hintc tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto A atTop (𝓝 ((0 - 0) +
      I • (∫ y : ℝ, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      I • ∫ y : ℝ, F ((c : ℂ) + (y : ℂ) * I))) :=
    ((hbot.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hconst : Tendsto A atTop (𝓝 (2 * Real.pi * I * (1 + expDetZetaResidue X ρ Y))) :=
    tendsto_const_nhds.congr' (hrect.mono fun H h => h.symm)
  have heq := tendsto_nhds_unique hlim hconst
  simp only [sub_zero, zero_add, smul_eq_mul] at heq
  have hI : I ≠ 0 := I_ne_zero
  have h2 : I * ((∫ y : ℝ, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      ∫ y : ℝ, F ((c : ℂ) + (y : ℂ) * I)) =
      I * (2 * Real.pi * (1 + expDetZetaResidue X ρ Y)) := by
    rw [mul_sub, heq]
    ring
  exact mul_left_cancel₀ hI h2

/-- Twisting the coefficients by `n^{-ρ}` shifts the Dirichlet series by `ρ`. -/
theorem LSeries_mul_natCast_cpow_neg (f : ℕ → ℂ) (ρ w : ℂ) :
    LSeries (fun n => f n * (n : ℂ) ^ (-ρ)) w = LSeries f (ρ + w) := by
  unfold LSeries
  congr 1
  funext n
  simp only [LSeries.term_def]
  split_ifs with hn
  · rfl
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_add _ _ hn0, Complex.cpow_neg]
    have h1 : (n : ℂ) ^ ρ ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      tauto
    have h2 : (n : ℂ) ^ w ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      tauto
    field_simp

/-- The twisted defect coefficients are absolutely summable against `n^{-2}`. -/
theorem summable_norm_moebiusZetaDefect_twist {X : ℕ} (hX : 1 ≤ X) {ρ : ℂ} (hβ0 : 0 < ρ.re) :
    Summable (fun n : ℕ =>
      ‖Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n * (n : ℂ) ^ (-ρ)‖ *
        (n : ℝ) ^ (-(2 : ℝ))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - ρ.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (-1 - ρ.re) := Real.rpow_nonneg (by simp) _
    simpa using h0
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hD := Sieve.norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
    have hdiv : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, neg_re]
    calc ‖Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n‖ * (n : ℝ) ^ (-ρ.re) *
          (n : ℝ) ^ (-(2 : ℝ))
        ≤ (n : ℝ) * (n : ℝ) ^ (-ρ.re) * (n : ℝ) ^ (-(2 : ℝ)) := by
          gcongr
          exact le_trans hD hdiv
      _ = (n : ℝ) ^ (-1 - ρ.re) := by
          rw [show (-1 - ρ.re) = (1 : ℝ) + (-ρ.re) + (-(2 : ℝ)) by ring,
            Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]

/-- **Cahen–Mellin on the line `Re w = 2`.** -/
theorem tsum_moebiusZetaDefect_exp_eq_integral_two {X : ℕ} (hX : 1 ≤ X) {ρ : ℂ}
    (hβ0 : 0 < ρ.re) {Y : ℝ} (hY : 0 < Y) :
    ∑' n : ℕ, Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n * (n : ℂ) ^ (-ρ) *
        Complex.exp (-(((n : ℝ) * Y⁻¹ : ℝ) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, expDetIntegrand X ρ Y (((2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  set b : ℕ → ℂ := fun n => Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n * (n : ℂ) ^ (-ρ)
    with hb
  have hb0 : b 0 = 0 := by simp [hb]
  have h := mellinInv_gamma_mul_LSeries_eq_tsum_exp (a := b) (c := 2) two_pos hb0
    (summable_norm_moebiusZetaDefect_twist hX hβ0) (x := Y⁻¹) (inv_pos.mpr hY)
  rw [← h]
  unfold mellinInv
  rw [Complex.real_smul]
  congr 1
  congr 1
  funext y
  set w : ℂ := ((2 : ℝ) : ℂ) + (y : ℂ) * I with hw
  have hwre : (ρ + w).re = ρ.re + 2 := by simp [hw]
  have hpow : ((Y⁻¹ : ℝ) : ℂ) ^ (-w) = (Y : ℂ) ^ w := by
    have harg : ((Y : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hY.le]
      exact (Real.pi_pos).ne
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
  have hL : LSeries b w = 1 - Sieve.inghamMollifier X (ρ + w) * riemannZeta (ρ + w) := by
    rw [hb, LSeries_mul_natCast_cpow_neg]
    exact Sieve.LSeries_complexCoeff_moebiusZetaDefect_eq X (by rw [hwre]; linarith)
  rw [smul_eq_mul, hpow]
  show (Y : ℂ) ^ w * (Complex.Gamma w * LSeries b w) = expDetIntegrand X ρ Y w
  rw [hL]
  unfold expDetIntegrand
  ring

/-- **The exponentially smoothed zero detector.**  For a zero `ρ` of `ζ` with `1/2 ≤ Re ρ < 1`,
`X ≥ 1`, `Y ≥ 1` and `-1/2 ≤ c < 0`,
`Σ_n D(n) n^{-ρ} e^{-n/Y} = 1 - Y^{1-ρ}Γ(1-ρ)M_X(1) + (1/2π) ∫ F(c + iy) dy`. -/
theorem tsum_moebiusZetaDefect_exp_eq (X : ℕ) (hX : 1 ≤ X) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ0 : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re < 1) {Y : ℝ} (hY : 1 ≤ Y) {c : ℝ} (hc1 : -1 / 2 ≤ c)
    (hc0 : c < 0) :
    ∑' n : ℕ, Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n * (n : ℂ) ^ (-ρ) *
        Complex.exp (-(((n : ℝ) * Y⁻¹ : ℝ) : ℂ)) =
      1 + expDetZetaResidue X ρ Y +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I) := by
  rw [tsum_moebiusZetaDefect_exp_eq_integral_two hX (by linarith) (by linarith : (0 : ℝ) < Y)]
  have hshift := integral_expDetIntegrand_two_sub_line X hρ hβ0 hβ1 hY hc1 hc0
  rw [sub_eq_iff_eq_add] at hshift
  rw [hshift]
  generalize (∫ y : ℝ, expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I)) = J
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

end RHTower
