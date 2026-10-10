import GaloisForLFunctions.RHTower.ExponentialMellinPerron
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovInvZeta
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepCoefficientIdentification
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# The Abel-smoothed Möbius sum below the Vinogradov–Korobov height `log(1/x)`

For `0 < x < 1` write `S(x) = Σ μ(n) e^{-nx}`. By exponentially smoothed Perron inversion,

`2π S(x) = ∫ x^{-s} Γ(s) ζ(s)^{-1} dt`,   `s = 2 + it`.

Because `Γ` decays like `e^{-|t|/2}` on `1/2 ≤ Re s ≤ 2` (`exists_norm_Gamma_le_exp_half`), the
contour only has to be shifted up to the height `K = 12 log(1/x)`. The part above `K` costs `O(x)`.
Below `K` the rectangle `[c, 2] × [-K, K]`, with `c = 1 - min(δ, w(K+1))/4` and
`w = vkHadamardWidth`, lies in the Vinogradov–Korobov zero-free region, where
`‖1/ζ‖ ≤ C log(K+1)⁷ (1 + 2/w(K+1))⁷` (`Sieve.exists_bound_invZeta_vk_uniform`).

**Theorem** (`exists_norm_tsum_moebius_exp_le`). There are `C, δ > 0` and `x₀ > 0` such that for
`0 < x ≤ x₀`, with `K = 12 log(1/x)`,

`‖Σ μ(n) e^{-nx}‖ ≤ C (1 + K) log(K+1)⁷ (1 + 2/w(K+1))⁷ · x^{-1 + min(δ, w(K+1))/4}`.

The zero-free region at height `K ≍ log(1/x)` therefore gives a saving `x^{w(log(1/x))/4}`, up to
factors polylogarithmic in `log(1/x)`. This is far stronger than the saving
`exp(-c (log N)^{3/5}…)` of the sharp sum `Σ_{n ≤ N} μ(n)`, whose contour must reach height
`N^{o(1)}`.
-/

open Complex MeasureTheory Filter Topology

namespace RHTower.MoebiusAbel

noncomputable section

/-! ## The Gamma envelope on a strip -/

/-- `Γ` is bounded by `A e^{-|t|/2}` on `1/2 ≤ Re s ≤ 2`. -/
theorem exists_norm_Gamma_le_exp_half :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2)) := by
  obtain ⟨C, N, hC, hdec⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := 1 / 2) (by norm_num) 2
  set Kc : Set ℂ := {z | 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1} with hKc
  have hKcc : IsCompact Kc := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hc : IsClosed ({z : ℂ | 1 / 2 ≤ z.re} ∩ {z | z.re ≤ 2} ∩ {z | |z.im| ≤ 1}) :=
        ((isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
      convert hc using 1
      ext z
      simp only [hKc, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 3 := by
            have : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.1⟩
            linarith [hz.2.2]
  have hcont : ContinuousOn Complex.Gamma Kc := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z fun m hm => ?_).continuousAt.continuousWithinAt
    have hre := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hz.1]
  obtain ⟨G₀, hG₀⟩ := hKcc.exists_bound_of_continuousOn hcont
  refine ⟨max (C * N.factorial) (max G₀ 0 * Real.exp (1 / 2)), le_max_of_le_right
    (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le), fun σ t hσ1 hσ2 => ?_⟩
  rcases le_or_gt 1 |t| with ht | ht
  · have h := hdec σ t hσ1 hσ2 ht
    have hpow : |t| ^ N ≤ N.factorial * Real.exp |t| := by
      have := Real.pow_div_factorial_le_exp |t| (abs_nonneg t) N
      rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos)] at this
      linarith
    have hexp : Real.exp |t| * Real.exp (-(Real.pi * |t| / 2)) ≤ Real.exp (-(|t| / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, abs_nonneg t])
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := h
      _ ≤ C * (N.factorial * Real.exp |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
          gcongr
      _ = C * N.factorial * (Real.exp |t| * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ C * N.factorial * Real.exp (-(|t| / 2)) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hz : ((σ : ℂ) + (t : ℂ) * I) ∈ Kc := by
      refine ⟨by simpa using hσ1, by simpa using hσ2, ?_⟩
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      exact ht.le
    have h := hG₀ _ hz
    have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-(|t| / 2)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max G₀ 0 := h.trans (le_max_left _ _)
      _ ≤ max G₀ 0 * (Real.exp (1 / 2) * Real.exp (-(|t| / 2))) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = max G₀ 0 * Real.exp (1 / 2) * Real.exp (-(|t| / 2)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-! ## The integrand and the inversion formula -/

/-- `x^{-s} Γ(s) ζ(s)^{-1}`, with the pole of `ζ` removed. -/
def abelMoebiusIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (-s) * (Complex.Gamma s * Sieve.invZeta s)

theorem norm_abelMoebiusIntegrand {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖abelMoebiusIntegrand x s‖ = x ^ (-s.re) * (‖Complex.Gamma s‖ * ‖Sieve.invZeta s‖) := by
  rw [abelMoebiusIntegrand, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]

/-- **Exponentially smoothed Perron inversion for `μ`.** -/
theorem tsum_moebius_exp_eq_integral {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ))
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hsum : Summable (fun n : ℕ =>
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-(2 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (fun n => ?_)
      (Real.summable_nat_rpow.mpr (by norm_num : (-(2 : ℝ)) < -1))
    have h1 : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith
  have h := mellinInv_gamma_mul_LSeries_eq_tsum_exp (a := fun n : ℕ =>
    ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (c := 2) (by norm_num) (by simp) hsum hx
  rw [← h, mellinInv]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)
      = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
          abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I) from (Complex.real_smul).symm]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hre : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by simp
  have hne : ((2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    simp at this
  simp only [abelMoebiusIntegrand, smul_eq_mul]
  rw [RHTower.LSeries_moebius_eq_inv_riemannZeta hre, Sieve.invZeta_eq_inv hne]

/-! ## Bounds on the integrand -/

theorem abelMoebiusIntegrand_line_le {x : ℝ} (hx : 0 < x) {A Bz : ℝ}
    (hΓ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2)))
    (hz : ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → ‖(riemannZeta s)⁻¹‖ ≤ Bz) (t : ℝ) :
    ‖abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(|t| / 2)) := by
  have hre : (((2 : ℝ) : ℂ) + (t : ℂ) * I).re = 2 := by simp
  have hne : ((2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    simp at this
  rw [norm_abelMoebiusIntegrand hx, hre, Sieve.invZeta_eq_inv hne]
  have h1 := hΓ 2 t (by norm_num) le_rfl
  have h2 := hz _ (by rw [hre]; norm_num)
  have hxp : 0 ≤ x ^ (-(2 : ℝ)) := Real.rpow_nonneg hx.le _
  calc x ^ (-(2 : ℝ)) * (‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖(riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I))⁻¹‖)
      ≤ x ^ (-(2 : ℝ)) * ((A * Real.exp (-(|t| / 2))) * Bz) := by
        gcongr
        exact (norm_nonneg _).trans h1
    _ = x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(|t| / 2)) := by ring

theorem continuous_abelMoebiusIntegrand_line {x : ℝ} (hx : 0 < x) :
    Continuous fun t : ℝ => abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hl : Continuous fun t : ℝ => ((2 : ℝ) : ℂ) + (t : ℂ) * I := by fun_prop
  have hc : Continuous fun t : ℝ => (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) :=
    continuous_iff_continuousAt.2 fun t =>
      ((differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).continuousAt).comp
        hl.continuousAt
  have hg : Continuous fun t : ℝ => Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.2 fun t => ((Complex.differentiableAt_Gamma _ fun m hm => ?_
      ).continuousAt).comp hl.continuousAt
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      add_zero, neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact hc.mul (hg.mul (Sieve.continuous_invZeta_line (by norm_num)))

/-! ## Truncation at height `K` and the rectangle -/

/-- The part of a line integral above height `K` costs `B e^{-K/4} ∫ e^{-|t|/4}`. -/
theorem norm_integral_sub_intervalIntegral_le {g : ℝ → ℂ} (hg : Integrable g) {B K : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hbd : ∀ t, ‖g t‖ ≤ B * Real.exp (-(|t| / 2))) :
    ‖(∫ t, g t) - ∫ t in (-K)..K, g t‖
      ≤ B * Real.exp (-(K / 4)) * ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|)) := by
  have hS : MeasurableSet (Set.Ioc (-K) K) := measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_add_compl hS hg,
    add_sub_cancel_left]
  have hint : Integrable (fun t : ℝ => B * Real.exp (-(K / 4)) * Real.exp (-((1 / 4 : ℝ) * |t|))) :=
    (RHTower.integrable_exp_neg_mul_abs' (by norm_num)).const_mul _
  have hpt : ∀ t ∈ (Set.Ioc (-K) K)ᶜ,
      ‖g t‖ ≤ B * Real.exp (-(K / 4)) * Real.exp (-((1 / 4 : ℝ) * |t|)) := by
    intro t ht
    have hKt : K ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h.le
    calc ‖g t‖ ≤ B * Real.exp (-(|t| / 2)) := hbd t
      _ = B * (Real.exp (-(|t| / 4)) * Real.exp (-((1 / 4 : ℝ) * |t|))) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ B * (Real.exp (-(K / 4)) * Real.exp (-((1 / 4 : ℝ) * |t|))) := by
          gcongr
      _ = _ := by ring
  calc ‖∫ t in (Set.Ioc (-K) K)ᶜ, g t‖
      ≤ ∫ t in (Set.Ioc (-K) K)ᶜ,
          B * Real.exp (-(K / 4)) * Real.exp (-((1 / 4 : ℝ) * |t|)) :=
        norm_integral_le_of_norm_le hint.integrableOn
          ((ae_restrict_iff' hS.compl).mpr (Eventually.of_forall hpt))
    _ ≤ ∫ t : ℝ, B * Real.exp (-(K / 4)) * Real.exp (-((1 / 4 : ℝ) * |t|)) :=
        setIntegral_le_integral hint (Eventually.of_forall fun t => by positivity)
    _ = _ := integral_const_mul _ _

/-- The rectangle `[c, 2] × [-K, K]` moves the line integral to `Re s = c` at the cost of the two
horizontal edges. -/
theorem norm_intervalIntegral_two_le_rect {F : ℂ → ℂ} {c K : ℝ}
    (hF : DifferentiableOn ℂ F (Set.uIcc c 2 ×ℂ Set.uIcc (-K) K)) :
    ‖∫ y in (-K)..K, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ ‖∫ y in (-K)..K, F ((c : ℂ) + (y : ℂ) * I)‖
        + ‖∫ σ in c..2, F ((σ : ℂ) + ((-K : ℝ) : ℂ) * I)‖
        + ‖∫ σ in c..2, F ((σ : ℂ) + (K : ℂ) * I)‖ := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F ⟨c, -K⟩ ⟨2, K⟩ hF
  simp only at h
  set R := ∫ y in (-K)..K, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)
  set L := ∫ y in (-K)..K, F ((c : ℂ) + (y : ℂ) * I)
  set Bt := ∫ σ in c..2, F ((σ : ℂ) + ((-K : ℝ) : ℂ) * I)
  set Tp := ∫ σ in c..2, F ((σ : ℂ) + (K : ℂ) * I)
  have hR : I • R = I • L - Bt + Tp := by
    have : Bt - Tp + I • R - I • L = 0 := h
    linear_combination this
  have hnR : ‖R‖ = ‖I • R‖ := by rw [norm_smul, norm_I, one_mul]
  rw [hnR, hR]
  calc ‖I • L - Bt + Tp‖ ≤ ‖I • L - Bt‖ + ‖Tp‖ := norm_add_le _ _
    _ ≤ ‖I • L‖ + ‖Bt‖ + ‖Tp‖ := by gcongr; exact norm_sub_le _ _
    _ = ‖L‖ + ‖Bt‖ + ‖Tp‖ := by rw [norm_smul, norm_I, one_mul]

/-! ## Assembly -/

/-- The contour height `12 log(1/x)`. -/
def abelHeight (x : ℝ) : ℝ := 12 * Real.log (1 / x)

/-- The polylogarithmic factor `log(K+1)⁷ (1 + 2/w(K+1))⁷` at `K = abelHeight x`. -/
def abelLogFactor (x : ℝ) : ℝ :=
  Real.log (abelHeight x + 1) ^ 7 * (1 + 2 / vkHadamardWidth (abelHeight x + 1)) ^ 7

theorem exp_neg_abelHeight_div {x : ℝ} (hx : 0 < x) (a : ℝ) :
    Real.exp (-(abelHeight x / a)) = x ^ (12 / a) := by
  rw [abelHeight, Real.rpow_def_of_pos hx, one_div, Real.log_inv]
  congr 1
  ring

/-- Differentiability of the integrand on a Vinogradov–Korobov rectangle. -/
theorem differentiableOn_abelMoebiusIntegrand_rect {x c K : ℝ} (hx : 0 < x) (hc : 1 / 2 ≤ c)
    (hc2 : c ≤ 2)
    (hzf : ∀ s ∈ Set.uIcc c 2 ×ℂ Set.uIcc (-K) K, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ (abelMoebiusIntegrand x) (Set.uIcc c 2 ×ℂ Set.uIcc (-K) K) := by
  have hinv := Sieve.differentiableOn_invZeta_rect hzf
  intro s hs
  have hsre : c ≤ s.re := by
    have := (Complex.mem_reProdIm.mp hs).1
    rw [Set.uIcc_of_le hc2] at this
    exact this.1
  have hG : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m hm => ?_
    have hre := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hP : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  exact (hP.differentiableWithinAt.mul (hG.differentiableWithinAt.mul (hinv s hs)))

/-- The left edge `Re s = c`, `|Im s| ≤ K`. -/
theorem norm_left_edge_le {x c K A V : ℝ} (hx : 0 < x) (hc12 : 1 / 2 ≤ c) (hc2 : c ≤ 2)
    (hK0 : 0 ≤ K) (hA : 0 ≤ A)
    (hΓ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2)))
    (hinvR : ∀ s : ℂ, |s.im| ≤ K → c ≤ s.re → s.re ≤ 2 → ‖Sieve.invZeta s‖ ≤ V) :
    ‖∫ y in (-K)..K, abelMoebiusIntegrand x ((c : ℂ) + (y : ℂ) * I)‖
      ≤ x ^ (-c) * A * V * (2 * K) := by
  have hpt : ∀ y ∈ Set.uIoc (-K) K,
      ‖abelMoebiusIntegrand x ((c : ℂ) + (y : ℂ) * I)‖ ≤ x ^ (-c) * A * V := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith)] at hy
    have hyK : |y| ≤ K := abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    have him : ((c : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [norm_abelMoebiusIntegrand hx, hre]
    have hiv := hinvR _ (by rw [him]; exact hyK) (by rw [hre]) (by rw [hre]; exact hc2)
    have he : Real.exp (-(|y| / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := abs_nonneg y; linarith)
    have hgA : ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ ≤ A :=
      (hΓ c y hc12 hc2).trans (mul_le_of_le_one_right hA he)
    have hxp : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
    calc x ^ (-c) * (‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ *
          ‖Sieve.invZeta ((c : ℂ) + (y : ℂ) * I)‖)
        ≤ x ^ (-c) * (A * V) := by gcongr
      _ = x ^ (-c) * A * V := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans (le_of_eq ?_)
  rw [show K - -K = 2 * K by ring, abs_of_nonneg (by linarith)]

/-- A horizontal edge `Im s = y`, `|y| = K`, `c ≤ Re s ≤ 2`. -/
theorem norm_horizontal_edge_le {x c K A V y : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hc12 : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hA : 0 ≤ A) (hV : 0 ≤ V) (hy : |y| = K)
    (hΓ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2)))
    (hinvR : ∀ s : ℂ, |s.im| ≤ K → c ≤ s.re → s.re ≤ 2 → ‖Sieve.invZeta s‖ ≤ V) :
    ‖∫ σ in c..2, abelMoebiusIntegrand x ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V * 2 := by
  have hpt : ∀ σ ∈ Set.uIoc c 2, ‖abelMoebiusIntegrand x ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V := by
    intro σ hσ
    rw [Set.uIoc_of_le hc2] at hσ
    have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [norm_abelMoebiusIntegrand hx, hre]
    have hg := hΓ σ y (by linarith [hσ.1]) hσ.2
    rw [hy] at hg
    have hiv := hinvR _ (by rw [him, hy]) (by rw [hre]; exact hσ.1.le) (by rw [hre]; exact hσ.2)
    have hxs : x ^ (-σ) ≤ x ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith [hσ.2])
    have hxp : 0 ≤ x ^ (-σ) := Real.rpow_nonneg hx.le _
    calc x ^ (-σ) * (‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I)‖ *
          ‖Sieve.invZeta ((σ : ℂ) + (y : ℂ) * I)‖)
        ≤ x ^ (-(2 : ℝ)) * ((A * Real.exp (-(K / 2))) * V) := by
          gcongr
      _ = x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
  have hpos : 0 ≤ x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V := by positivity
  rw [abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_left (by linarith) hpos

/-- **The contour bound at a fixed `x`.** -/
theorem norm_integral_abelMoebiusIntegrand_le {x K c A Bz V : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hK0 : 0 ≤ K) (hc12 : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hA : 0 ≤ A) (hBz : 0 ≤ Bz) (hV : 0 ≤ V)
    (hΓ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2)))
    (hz : ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → ‖(riemannZeta s)⁻¹‖ ≤ Bz)
    (hinvR : ∀ s : ℂ, |s.im| ≤ K → c ≤ s.re → s.re ≤ 2 → ‖Sieve.invZeta s‖ ≤ V)
    (hzfR : ∀ s ∈ Set.uIcc c 2 ×ℂ Set.uIcc (-K) K, s ≠ 1 → riemannZeta s ≠ 0) :
    ‖∫ t : ℝ, abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ x ^ (-c) * A * V * (2 * K) + 2 * (x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V * 2)
        + x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(K / 4)) *
            ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|)) := by
  set g : ℝ → ℂ := fun t => abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I) with hgdef
  have hgbd : ∀ t, ‖g t‖ ≤ x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(|t| / 2)) :=
    fun t => abelMoebiusIntegrand_line_le hx hΓ hz t
  have hgint : Integrable g := by
    refine Integrable.mono' (((RHTower.integrable_exp_neg_mul_abs' (c := 1 / 2)
      (by norm_num)).const_mul (x ^ (-(2 : ℝ)) * A * Bz)))
      (continuous_abelMoebiusIntegrand_line hx).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    refine (hgbd t).trans (le_of_eq ?_)
    congr 2
    ring
  have htail := norm_integral_sub_intervalIntegral_le hgint hK0
    (by positivity : 0 ≤ x ^ (-(2 : ℝ)) * A * Bz) hgbd
  have hrect := norm_intervalIntegral_two_le_rect
    (differentiableOn_abelMoebiusIntegrand_rect hx hc12 hc2 hzfR)
  have hleft := norm_left_edge_le hx hc12 hc2 hK0 hA hΓ hinvR
  have hbot := norm_horizontal_edge_le (y := -K) hx hx1 hc12 hc2 hA hV
    (by rw [abs_neg, abs_of_nonneg hK0]) hΓ hinvR
  have htop := norm_horizontal_edge_le (y := K) hx hx1 hc12 hc2 hA hV (abs_of_nonneg hK0) hΓ hinvR
  have h1 : ‖∫ t, g t‖ ≤ ‖∫ t in (-K)..K, g t‖ + ‖(∫ t, g t) - ∫ t in (-K)..K, g t‖ := by
    have := norm_add_le (∫ t in (-K)..K, g t) ((∫ t, g t) - ∫ t in (-K)..K, g t)
    rwa [add_sub_cancel] at this
  have hK' : ((-K : ℝ) : ℂ) = ((-K : ℝ) : ℂ) := rfl
  linarith [hrect, hleft, hbot, htop, htail, h1]

/-- The arithmetic of the final bound. -/
theorem final_bound_arith {x c K A Bz Cv LF I₄ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hK0 : 0 ≤ K)
    (hc0 : 0 ≤ c) (hA : 0 ≤ A) (hBz : 0 ≤ Bz) (hCv : 0 ≤ Cv) (hI₄ : 0 ≤ I₄) (hLF1 : 1 ≤ LF) :
    x ^ (-c) * A * (Cv * LF) * (2 * K) + 2 * (x ^ (-(2 : ℝ)) * A * x ^ (6 : ℝ) * (Cv * LF) * 2)
      + x ^ (-(2 : ℝ)) * A * Bz * x ^ (3 : ℝ) * I₄
      ≤ (2 * A * Cv + 4 * A * Cv + A * Bz * I₄) * (1 + K) * LF * x ^ (-c) := by
  have hx2 : x ^ (-(2 : ℝ)) * x ^ (6 : ℝ) = x ^ (4 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have hx2' : x ^ (-(2 : ℝ)) * x ^ (3 : ℝ) = x := by
    rw [← Real.rpow_add hx]; norm_num
  have hx4c : x ^ (4 : ℝ) ≤ x ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith)
  have hx1c : x ≤ x ^ (-c) := by
    have := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (show -c ≤ (1 : ℝ) by linarith)
    rwa [Real.rpow_one] at this
  have hxc0 : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
  have hLF0 : 0 ≤ LF := by linarith
  have e1 : x ^ (-c) * A * (Cv * LF) * (2 * K) ≤ (2 * A * Cv) * (1 + K) * LF * x ^ (-c) := by
    have h : x ^ (-c) * A * (Cv * LF) * (2 * K) = (2 * A * Cv) * K * LF * x ^ (-c) := by ring
    rw [h]
    have : 0 ≤ 2 * A * Cv := by positivity
    gcongr
    linarith
  have e2 : 2 * (x ^ (-(2 : ℝ)) * A * x ^ (6 : ℝ) * (Cv * LF) * 2)
      ≤ (4 * A * Cv) * (1 + K) * LF * x ^ (-c) := by
    have h : 2 * (x ^ (-(2 : ℝ)) * A * x ^ (6 : ℝ) * (Cv * LF) * 2)
        = (4 * A * Cv) * 1 * LF * (x ^ (-(2 : ℝ)) * x ^ (6 : ℝ)) := by ring
    rw [h, hx2]
    have : 0 ≤ 4 * A * Cv := by positivity
    gcongr
    linarith
  have e3 : x ^ (-(2 : ℝ)) * A * Bz * x ^ (3 : ℝ) * I₄
      ≤ (A * Bz * I₄) * (1 + K) * LF * x ^ (-c) := by
    have h : x ^ (-(2 : ℝ)) * A * Bz * x ^ (3 : ℝ) * I₄
        = (A * Bz * I₄) * 1 * 1 * (x ^ (-(2 : ℝ)) * x ^ (3 : ℝ)) := by ring
    rw [h, hx2']
    have : 0 ≤ A * Bz * I₄ := by positivity
    gcongr
    linarith
  nlinarith [e1, e2, e3]

/-- **The Abel-smoothed Möbius sum below the Vinogradov–Korobov height.** -/
theorem exists_norm_tsum_moebius_exp_le :
    ∃ C δ x₀ : ℝ, 0 < C ∧ 0 < δ ∧ 0 < x₀ ∧ x₀ < 1 ∧ ∀ x : ℝ, 0 < x → x ≤ x₀ →
      ‖∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ))‖
        ≤ C * (1 + abelHeight x) * abelLogFactor x *
            x ^ (-1 + min δ (vkHadamardWidth (abelHeight x + 1)) / 4) := by
  obtain ⟨A, hA, hΓ⟩ := exists_norm_Gamma_le_exp_half
  obtain ⟨Bz, hBz, hz⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  obtain ⟨Cv, δ, K₀, hCv, hδ, hK₀3, hK₀e, hzf, hinv⟩ := Sieve.exists_bound_invZeta_vk_uniform
  have hI₄ : 0 ≤ ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hx₀1 : Real.exp (-(K₀ / 12)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨(2 * A * Cv + 4 * A * Cv + A * Bz * ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|))) /
      (2 * Real.pi) + 1, δ, Real.exp (-(K₀ / 12)), by positivity, hδ, Real.exp_pos _, hx₀1,
    fun x hx hxx₀ => ?_⟩
  have hx1 : x < 1 := lt_of_le_of_lt hxx₀ hx₀1
  have hlog : K₀ / 12 ≤ Real.log (1 / x) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hx hxx₀
    rw [Real.log_exp] at this
    linarith
  have hK : K₀ ≤ abelHeight x := by rw [abelHeight]; linarith
  have hK0 : 0 ≤ abelHeight x := by linarith
  have hee : Real.exp (Real.exp 1) ≤ abelHeight x + 1 := by
    have : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 30) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
    linarith
  have hw : 0 < vkHadamardWidth (abelHeight x + 1) := vkHadamardWidth_pos hee
  have hw8 : vkHadamardWidth (abelHeight x + 1) ≤ 1 / 10 ^ 8 := Sieve.vkHadamardWidth_le_inv hee
  have hm0 : 0 < min δ (vkHadamardWidth (abelHeight x + 1)) := lt_min hδ hw
  have hm1 : min δ (vkHadamardWidth (abelHeight x + 1)) ≤ 1 / 10 ^ 8 := (min_le_right _ _).trans hw8
  have hlogK : 1 ≤ Real.log (abelHeight x + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLF1 : 1 ≤ abelLogFactor x := by
    have h1 : 1 ≤ Real.log (abelHeight x + 1) ^ 7 := one_le_pow₀ hlogK
    have h2 : 1 ≤ (1 + 2 / vkHadamardWidth (abelHeight x + 1)) ^ 7 :=
      one_le_pow₀ (by have := div_pos two_pos hw; linarith)
    rw [abelLogFactor]
    nlinarith
  have hcore := norm_integral_abelMoebiusIntegrand_le (x := x) (K := abelHeight x)
    (c := 1 - min δ (vkHadamardWidth (abelHeight x + 1)) / 4)
    (V := Cv * abelLogFactor x) hx hx1 hK0 (by linarith) (by linarith) hA hBz
    (by have := hLF1; positivity) hΓ hz
    (fun s him hre hre2 => by
      have h := hinv s (abelHeight x) hK him hre hre2
      rw [abelLogFactor]
      linarith)
    (fun s hs hs1 => by
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
      rw [Set.uIcc_of_le (by linarith)] at hre
      rw [Set.uIcc_of_le (by linarith)] at him
      exact hzf s (abelHeight x) hK (abs_le.mpr ⟨him.1, him.2⟩) hre.1 hs1)
  have hx6 : Real.exp (-(abelHeight x / 2)) = x ^ (6 : ℝ) := by
    rw [exp_neg_abelHeight_div hx]; norm_num
  have hx3 : Real.exp (-(abelHeight x / 4)) = x ^ (3 : ℝ) := by
    rw [exp_neg_abelHeight_div hx]; norm_num
  rw [hx6, hx3] at hcore
  have harith := final_bound_arith (c := 1 - min δ (vkHadamardWidth (abelHeight x + 1)) / 4)
    (K := abelHeight x) (Cv := Cv) (LF := abelLogFactor x)
    (I₄ := ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|))) hx hx1 hK0 (by linarith) hA hBz hCv.le
    hI₄ hLF1
  have hcomb := hcore.trans (le_of_le_of_eq harith rfl)
  have hexp : -(1 - min δ (vkHadamardWidth (abelHeight x + 1)) / 4)
      = -1 + min δ (vkHadamardWidth (abelHeight x + 1)) / 4 := by ring
  rw [hexp] at harith
  rw [tsum_moebius_exp_eq_integral hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  set E := x ^ (-1 + min δ (vkHadamardWidth (abelHeight x + 1)) / 4)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpos : 0 ≤ (1 + abelHeight x) * abelLogFactor x * E := by
    have : 0 ≤ E := Real.rpow_nonneg hx.le _
    have : 0 ≤ abelLogFactor x := by linarith
    positivity
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * ((2 * A * Cv + 4 * A * Cv + A * Bz *
          ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|))) * (1 + abelHeight x) * abelLogFactor x * E) := by
        gcongr
        rw [hexp] at hcomb
        exact hcomb
    _ = (2 * A * Cv + 4 * A * Cv + A * Bz * ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|))) /
          (2 * Real.pi) * (1 + abelHeight x) * abelLogFactor x * E := by ring
    _ ≤ _ := by nlinarith

end

end RHTower.MoebiusAbel
