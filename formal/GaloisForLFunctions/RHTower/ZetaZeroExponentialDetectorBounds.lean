import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetector
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Uniform bounds for the exponentially smoothed zero detector

The three error terms of the detector identity `tsum_moebiusZetaDefect_exp_eq` are controlled
here.

* `|Γ(x + it)| ≤ C e^{-|t|}` uniformly for `1/2 ≤ x ≤ 1` (`|Γ(s)| ≤ Γ(Re s)` near the real axis and
  `|t|^N e^{-π|t|/2}` beyond), hence `|Γ(c + iy)| ≤ 12C e^{-|y|}` for `-1/2 ≤ c ≤ -1/12`.
* `|ζ(1/2 + it)| ≤ C (1 + |t|)^N`.
* The residue `Y^{1-ρ} Γ(1-ρ) M_X(1)` is at most `X Y C |γ|^N e^{-π|γ|/2}`.
* The tail `Σ_{n > Z} |D(n)| n^{-β} e^{-n/Y}` is at most `6 Y² e^{-Z/(2Y)}`, from
  `n e^{-n/Y} ≤ 2Y e^{-n/(2Y)}` and a geometric series.
* On the line `Re w = c = 1/2 - β` the integrand is at most
  `Y^c 12C e^{-|y|}(1 + X|ζ(1/2 + i(γ+y))|)`, so its integral is at most
  `Y^c 12C (2 + X(∫_{-L}^{L}|ζ(1/2 + i(γ+y))| dy + C' (1+|γ|)^N e^{-L/2}))`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

/-- `|Γ(x + it)| ≤ C e^{-|t|}` uniformly on `1/2 ≤ x ≤ 1`. -/
theorem exists_norm_Gamma_le_exp_neg_abs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t : ℝ, 1 / 2 ≤ x → x ≤ 1 →
      ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.exp (-|t|) := by
  obtain ⟨Cγ, hCγ0, hCγ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_Real_Gamma_Icc (a := 1 / 2) (b := 1)
      (by norm_num)
  obtain ⟨C₁, N, hC₁, hdec⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (show (0 : ℝ) < 1 / 2 by norm_num) 1
  refine ⟨Cγ * Real.exp 1 + C₁ * (4 ^ N * (N.factorial : ℝ)), by positivity, ?_⟩
  intro x t hx1 hx2
  have hE : 0 < Real.exp (-|t|) := Real.exp_pos _
  have hfac : (0 : ℝ) ≤ 4 ^ N * (N.factorial : ℝ) := by positivity
  by_cases ht : |t| ≤ 1
  · have hre : 0 < ((x : ℂ) + (t : ℂ) * I).re := by simp; linarith
    have h1 := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re hre
    have hre' : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
    rw [hre'] at h1
    have h2 := hCγ x hx1 hx2
    have h3 : 1 ≤ Real.exp 1 * Real.exp (-|t|) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≤ Cγ := le_trans h1 h2
      _ ≤ Cγ * (Real.exp 1 * Real.exp (-|t|)) := le_mul_of_one_le_right hCγ0 h3
      _ ≤ (Cγ * Real.exp 1 + C₁ * (4 ^ N * (N.factorial : ℝ))) * Real.exp (-|t|) := by
          nlinarith [mul_nonneg hC₁ hfac]
  · push Not at ht
    have h1 := hdec x t (by linarith) hx2 ht.le
    have h2 := abs_pow_mul_exp_neg_pi_le N t
    calc ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * I)‖
        ≤ C₁ * (|t| ^ N * Real.exp (-(Real.pi * |t| / 2))) := by rw [← mul_assoc]; exact h1
      _ ≤ C₁ * (4 ^ N * (N.factorial : ℝ) * Real.exp (-|t|)) := mul_le_mul_of_nonneg_left h2 hC₁
      _ ≤ (Cγ * Real.exp 1 + C₁ * (4 ^ N * (N.factorial : ℝ))) * Real.exp (-|t|) := by
          have : 0 ≤ Cγ * Real.exp 1 * Real.exp (-|t|) := by positivity
          nlinarith

/-- `|Γ(c + iy)| ≤ 12 C e^{-|y|}` for `-1/2 ≤ c ≤ -1/12`, through `Γ(w) = Γ(w+1)/w`. -/
theorem norm_Gamma_neg_line_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x t : ℝ, 1 / 2 ≤ x → x ≤ 1 →
      ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.exp (-|t|))
    {c : ℝ} (hc1 : -1 / 2 ≤ c) (hc2 : c ≤ -1 / 12) (y : ℝ) :
    ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ ≤ 12 * C * Real.exp (-|y|) := by
  set w : ℂ := (c : ℂ) + (y : ℂ) * I with hw
  have hwre : w.re = c := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hwre] at this
    simp at this
    linarith
  have hnorm : 1 / 12 ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [hwre, abs_of_neg (by linarith)] at h
    linarith
  have hrel : Complex.Gamma w = Complex.Gamma (w + 1) / w := by
    rw [Complex.Gamma_add_one w hw0]
    field_simp
  have hw1 : w + 1 = ((c + 1 : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [hw]; push_cast; ring
  have hb := hC (c + 1) y (by linarith) (by linarith)
  rw [← hw1] at hb
  rw [hrel, norm_div, div_le_iff₀ (by linarith)]
  calc ‖Complex.Gamma (w + 1)‖ ≤ C * Real.exp (-|y|) := hb
    _ = 12 * C * Real.exp (-|y|) * (1 / 12) := by ring
    _ ≤ 12 * C * Real.exp (-|y|) * ‖w‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)

/-- `|ζ(1/2 + it)| ≤ C (1 + |t|)^N` for all real `t`. -/
theorem exists_norm_riemannZeta_half_le :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_bound_norm_riemannZeta_strip 1
  have hcont : Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hline : Continuous fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by fun_prop
    exact ContinuousAt.comp (g := riemannZeta)
      (differentiableAt_riemannZeta hne).continuousAt hline.continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨|M| + Cζ, N, by positivity, fun t => ?_⟩
  have hpow : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  by_cases ht : |t| ≤ 1
  · have h1 := hM t (abs_le.mp ht)
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ |M| := le_trans h1 (le_abs_self _)
      _ ≤ (|M| + Cζ) * 1 := by linarith
      _ ≤ (|M| + Cζ) * (1 + |t|) ^ N := mul_le_mul_of_nonneg_left hpow (by positivity)
  · push Not at ht
    have h1 := hζ (1 / 2) t (by norm_num [abs_of_pos]) ht.le
    have h2 : |t| ^ N ≤ (1 + |t|) ^ N := pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ N := h1
      _ ≤ Cζ * (1 + |t|) ^ N := mul_le_mul_of_nonneg_left h2 hCζ
      _ ≤ (|M| + Cζ) * (1 + |t|) ^ N := by
          have := abs_nonneg M
          nlinarith

/-- **The residue term is exponentially small in the height.** -/
theorem exists_norm_expDetZetaResidue_le :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (X : ℕ) (ρ : ℂ) (Y : ℝ), 1 / 2 ≤ ρ.re → ρ.re < 1 →
      1 ≤ |ρ.im| → 1 ≤ Y →
      ‖expDetZetaResidue X ρ Y‖ ≤
        X * Y * (C * |ρ.im| ^ N * Real.exp (-(Real.pi * |ρ.im| / 2))) := by
  obtain ⟨C₁, N, hC₁, hdec⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (show (0 : ℝ) < 1 / 2 by norm_num) 3
  refine ⟨C₁, N, hC₁, fun X ρ Y hβ0 hβ1 hγ hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hq0 : (1 : ℂ) - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hqnorm : 1 ≤ ‖(1 : ℂ) - ρ‖ := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) - ρ)
    simp only [sub_im, one_im, zero_sub, abs_neg] at h
    linarith
  have hrel : Complex.Gamma (1 - ρ) = Complex.Gamma (1 - ρ + 1) / (1 - ρ) := by
    rw [Complex.Gamma_add_one _ hq0]
    field_simp
  have hq1 : (1 : ℂ) - ρ + 1 = ((2 - ρ.re : ℝ) : ℂ) + ((-ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp; ring
  have hb := hdec (2 - ρ.re) (-ρ.im) (by linarith) (by linarith) (by rw [abs_neg]; exact hγ)
  rw [← hq1, abs_neg] at hb
  have hΓ : ‖Complex.Gamma (1 - ρ)‖ ≤ C₁ * |ρ.im| ^ N * Real.exp (-(Real.pi * |ρ.im| / 2)) := by
    rw [hrel, norm_div]
    exact le_trans (div_le_self (norm_nonneg _) hqnorm) hb
  have hYq : ‖(Y : ℂ) ^ (1 - ρ)‖ ≤ Y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0]
    simp only [sub_re, one_re]
    calc Y ^ (1 - ρ.re) ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      _ = Y := Real.rpow_one Y
  have hM : ‖Sieve.inghamMollifier X 1‖ ≤ X := Sieve.norm_inghamMollifier_le_nat X (by simp)
  unfold expDetZetaResidue
  rw [norm_neg, norm_mul, norm_mul]
  calc ‖(Y : ℂ) ^ (1 - ρ)‖ * ‖Complex.Gamma (1 - ρ)‖ * ‖Sieve.inghamMollifier X 1‖
      ≤ Y * (C₁ * |ρ.im| ^ N * Real.exp (-(Real.pi * |ρ.im| / 2))) * X := by
        gcongr
    _ = X * Y * (C₁ * |ρ.im| ^ N * Real.exp (-(Real.pi * |ρ.im| / 2))) := by ring

/-- `x e^{-x/Y} ≤ 2Y e^{-x/(2Y)}`. -/
theorem mul_exp_neg_div_le {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    x * Real.exp (-(x / Y)) ≤ 2 * Y * Real.exp (-(x / (2 * Y))) := by
  have h1 : x ≤ 2 * Y * Real.exp (x / (2 * Y)) := by
    have := Real.add_one_le_exp (x / (2 * Y))
    have h2 : x / (2 * Y) ≤ Real.exp (x / (2 * Y)) := by linarith [Real.exp_pos (x / (2 * Y))]
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have h3 : Real.exp (x / (2 * Y)) * Real.exp (-(x / Y)) = Real.exp (-(x / (2 * Y))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc x * Real.exp (-(x / Y)) ≤ (2 * Y * Real.exp (x / (2 * Y))) * Real.exp (-(x / Y)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 * Y * (Real.exp (x / (2 * Y)) * Real.exp (-(x / Y))) := by ring
    _ = 2 * Y * Real.exp (-(x / (2 * Y))) := by rw [h3]

/-- The terms of the detector series. -/
def expDetTerm (X : ℕ) (ρ : ℂ) (Y : ℝ) (n : ℕ) : ℂ :=
  Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n * (n : ℂ) ^ (-ρ) *
    Complex.exp (-(((n : ℝ) * Y⁻¹ : ℝ) : ℂ))

theorem norm_expDetTerm_le {X : ℕ} (hX : 1 ≤ X) {ρ : ℂ} (hβ0 : 0 ≤ ρ.re) {Y : ℝ} (n : ℕ) :
    ‖expDetTerm X ρ Y n‖ ≤ n * Real.exp (-(n / Y)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expDetTerm]
  · have hD := Sieve.norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
    have hdiv : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : ‖(n : ℂ) ^ (-ρ)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hn, neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    have hexp : ‖Complex.exp (-(((n : ℝ) * Y⁻¹ : ℝ) : ℂ))‖ = Real.exp (-(n / Y)) := by
      rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.ofReal_re, div_eq_mul_inv]
    unfold expDetTerm
    rw [norm_mul, norm_mul, hexp]
    calc ‖Sieve.complexCoeff (Sieve.moebiusZetaDefect X) n‖ * ‖(n : ℂ) ^ (-ρ)‖ *
          Real.exp (-(n / Y))
        ≤ n * 1 * Real.exp (-(n / Y)) := by
          gcongr
          exact le_trans hD hdiv
      _ = n * Real.exp (-(n / Y)) := by ring

/-- **The tail of the detector series.**  The series converges absolutely, and the terms beyond
`Z` contribute at most `4 Y² e^{-Z/(2Y)}`. -/
theorem summable_expDetTerm_and_tail_le {X : ℕ} (hX : 1 ≤ X) {ρ : ℂ} (hβ0 : 0 ≤ ρ.re) {Y : ℝ}
    (hY : 0 < Y) (Z : ℕ) :
    Summable (expDetTerm X ρ Y) ∧
      ‖(∑' n, expDetTerm X ρ Y n) - ∑ n ∈ Finset.range (Z + 1), expDetTerm X ρ Y n‖ ≤
        4 * Y ^ 2 * Real.exp (-(Z / (2 * Y))) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.exp (-(1 / (2 * Y))) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; exact (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  have hgeom : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hexp_n : ∀ n : ℕ, Real.exp (-((n : ℝ) / (2 * Y))) = r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hbound : ∀ n : ℕ, ‖expDetTerm X ρ Y n‖ ≤ 2 * Y * r ^ n := by
    intro n
    refine le_trans (norm_expDetTerm_le hX hβ0 n) ?_
    rw [← hexp_n]
    exact mul_exp_neg_div_le hY (n : ℝ)
  have hsum : Summable (expDetTerm X ρ Y) :=
    Summable.of_norm_bounded (hgeom.mul_left (2 * Y)) hbound
  refine ⟨hsum, ?_⟩
  have hsplit := hsum.sum_add_tsum_nat_add (Z + 1)
  rw [← hsplit, add_sub_cancel_left]
  have hsumtail : Summable (fun i : ℕ => expDetTerm X ρ Y (i + (Z + 1))) :=
    (summable_nat_add_iff (Z + 1)).mpr hsum
  have hnormtail : Summable (fun i : ℕ => ‖expDetTerm X ρ Y (i + (Z + 1))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hbound (i + (Z + 1)))
      ((summable_nat_add_iff (f := fun n : ℕ => 2 * Y * r ^ n) (Z + 1)).mpr
        (hgeom.mul_left (2 * Y)))
  refine le_trans (norm_tsum_le_tsum_norm hnormtail) ?_
  have hgeomtail : Summable (fun i : ℕ => 2 * Y * r ^ (i + (Z + 1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => 2 * Y * r ^ n) (Z + 1)).mpr
      (hgeom.mul_left (2 * Y))
  refine le_trans (Summable.tsum_mono hnormtail hgeomtail (fun i => hbound (i + (Z + 1)))) ?_
  have heq : (fun i : ℕ => 2 * Y * r ^ (i + (Z + 1))) =
      fun i : ℕ => (2 * Y * r ^ (Z + 1)) * r ^ i := by
    funext i
    rw [pow_add]
    ring
  rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  -- `r^{Z+1}/(1 - r) ≤ 2Y e^{-Z/(2Y)}`
  have ha : (0 : ℝ) < 1 / (2 * Y) := by positivity
  have hrZ : r ^ Z = Real.exp (-(Z / (2 * Y))) := by rw [← hexp_n]
  have hkey : r / (1 - r) ≤ 2 * Y := by
    have h1 : 1 - r ≥ r * (1 / (2 * Y)) := by
      have he : Real.exp (1 / (2 * Y)) * r = 1 := by
        rw [hr, ← Real.exp_add]; simp
      have hadd := Real.add_one_le_exp (1 / (2 * Y))
      nlinarith
    rw [div_le_iff₀ (by linarith)]
    have : r * (1 / (2 * Y)) * (2 * Y) = r := by field_simp
    nlinarith
  have hpos : 0 < 1 - r := by linarith
  calc 2 * Y * r ^ (Z + 1) * (1 - r)⁻¹ = 2 * Y * r ^ Z * (r / (1 - r)) := by
        rw [pow_succ]; field_simp
    _ ≤ 2 * Y * r ^ Z * (2 * Y) := by
        apply mul_le_mul_of_nonneg_left hkey
        have := pow_nonneg hr0 Z
        positivity
    _ = 4 * Y ^ 2 * Real.exp (-(Z / (2 * Y))) := by rw [hrZ]; ring

/-- `e^{-|y|/2}(1 + |y|)^N` is integrable. -/
theorem integrable_exp_neg_half_abs_mul_one_add_abs_pow (N : ℕ) :
    Integrable (fun y : ℝ => Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by
  have hint := (integrable_exp_neg_mul_abs' (c := 1 / 4) (by norm_num)).const_mul
    (4 ^ N * (N.factorial : ℝ) * Real.exp (1 / 4))
  refine Integrable.mono' hint (by fun_prop) (Eventually.of_forall fun y => ?_)
  have hy : 0 ≤ (1 + |y|) / 4 := by positivity
  have h1 := Real.pow_div_factorial_le_exp ((1 + |y|) / 4) hy N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h2 : (1 + |y|) ^ N ≤ 4 ^ N * (N.factorial : ℝ) * Real.exp ((1 + |y|) / 4) := by
    rw [div_le_iff₀ hf, div_pow, div_le_iff₀ (by positivity)] at h1
    calc (1 + |y|) ^ N ≤ Real.exp ((1 + |y|) / 4) * (N.factorial : ℝ) * 4 ^ N := h1
      _ = 4 ^ N * (N.factorial : ℝ) * Real.exp ((1 + |y|) / 4) := by ring
  have h3 : Real.exp (-(|y| / 2)) * Real.exp ((1 + |y|) / 4) =
      Real.exp (1 / 4) * Real.exp (-(1 / 4 * |y|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.exp (-(|y| / 2)) * (1 + |y|) ^ N
      ≤ Real.exp (-(|y| / 2)) * (4 ^ N * (N.factorial : ℝ) * Real.exp ((1 + |y|) / 4)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = 4 ^ N * (N.factorial : ℝ) * (Real.exp (-(|y| / 2)) * Real.exp ((1 + |y|) / 4)) := by
        ring
    _ = 4 ^ N * (N.factorial : ℝ) * Real.exp (1 / 4) * Real.exp (-(1 / 4 * |y|)) := by
        rw [h3]; ring

theorem continuous_norm_riemannZeta_half_shift (γ : ℝ) :
    Continuous fun y : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I)‖ := by
  refine continuous_norm.comp (continuous_iff_continuousAt.mpr fun y => ?_)
  have hne : ((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hline : Continuous fun y : ℝ => ((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I := by fun_prop
  exact ContinuousAt.comp (g := riemannZeta)
    (differentiableAt_riemannZeta hne).continuousAt hline.continuousAt

/-- **The line integral of the detector.**  On `Re w = c = 1/2 - β`, `7/12 ≤ β ≤ 1`,
`|∫ F(c+iy) dy| ≤ Y^c (A + X A ∫_{-L}^{L} |ζ(1/2 + i(γ+y))| dy + X B (1 + |γ|)^N e^{-L/2})`. -/
theorem exists_norm_integral_expDetIntegrand_le :
    ∃ (A B : ℝ) (N : ℕ), 0 ≤ A ∧ 0 ≤ B ∧ ∀ (X : ℕ) (ρ : ℂ) (Y L : ℝ), 7 / 12 ≤ ρ.re →
      ρ.re ≤ 1 → 1 ≤ Y → 0 ≤ L →
      ‖∫ y : ℝ, expDetIntegrand X ρ Y (((1 / 2 - ρ.re : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        Y ^ (1 / 2 - ρ.re) * (A + X * A *
          (∫ y in (-L)..L, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖) +
          X * B * (1 + |ρ.im|) ^ N * Real.exp (-(L / 2))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Gamma_le_exp_neg_abs
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_norm_riemannZeta_half_le
  set E₁ : ℝ := ∫ y : ℝ, Real.exp (-(1 * |y|)) with hE₁
  set I₁ : ℝ := ∫ y : ℝ, Real.exp (-(|y| / 2)) * (1 + |y|) ^ N with hI₁
  have hE₁0 : 0 ≤ E₁ := integral_nonneg fun y => (Real.exp_pos _).le
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun y => by positivity
  refine ⟨12 * C * (E₁ + 1), 12 * C * (Cζ * I₁), N, by positivity, by positivity, ?_⟩
  intro X ρ Y L hβ1 hβ2 hY hL
  set c : ℝ := 1 / 2 - ρ.re with hc
  set γ : ℝ := ρ.im with hγ
  have hY0 : 0 < Y := by linarith
  set g : ℝ → ℝ := fun y => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I)‖ with hg
  have hgcont : Continuous g := continuous_norm_riemannZeta_half_shift γ
  -- the pointwise bound
  have hpt : ∀ y : ℝ, ‖expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I)‖ ≤
      Y ^ c * (12 * C * (Real.exp (-(1 * |y|)) + X * (Real.exp (-(1 * |y|)) * g y))) := by
    intro y
    have hs : ρ + ((c : ℂ) + (y : ℂ) * I) = ((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hc, hγ]
    have hYw : ‖(Y : ℂ) ^ ((c : ℂ) + (y : ℂ) * I)‖ = Y ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0]
      simp
    have hΓ := norm_Gamma_neg_line_le hC0 hC (c := c) (by rw [hc]; linarith)
      (by rw [hc]; linarith) y
    have hM : ‖Sieve.inghamMollifier X (ρ + ((c : ℂ) + (y : ℂ) * I))‖ ≤ X :=
      Sieve.norm_inghamMollifier_le_nat X (by rw [hs]; norm_num)
    have hfac : ‖1 - Sieve.inghamMollifier X (ρ + ((c : ℂ) + (y : ℂ) * I)) *
        riemannZeta (ρ + ((c : ℂ) + (y : ℂ) * I))‖ ≤ 1 + X * g y := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one, norm_mul]
      have hgy : ‖riemannZeta (ρ + ((c : ℂ) + (y : ℂ) * I))‖ = g y := by rw [hs]
      rw [hgy]
      gcongr
    unfold expDetIntegrand
    rw [norm_mul, norm_mul, hYw, one_mul]
    have hg0 : 0 ≤ g y := norm_nonneg _
    calc Y ^ c * ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ *
          ‖1 - Sieve.inghamMollifier X (ρ + ((c : ℂ) + (y : ℂ) * I)) *
            riemannZeta (ρ + ((c : ℂ) + (y : ℂ) * I))‖
        ≤ Y ^ c * (12 * C * Real.exp (-|y|)) * (1 + X * g y) := by
          gcongr
      _ = Y ^ c * (12 * C * (Real.exp (-|y|) + X * (Real.exp (-|y|) * g y))) := by ring
  -- integrability
  have hexp1 : Integrable (fun y : ℝ => Real.exp (-(1 * |y|))) :=
    integrable_exp_neg_mul_abs' one_pos
  have hgbound : ∀ y : ℝ, g y ≤ Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N := by
    intro y
    have h1 := hζ (γ + y)
    have h2 : (1 + |γ + y|) ^ N ≤ ((1 + |γ|) * (1 + |y|)) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_add_le γ y, abs_nonneg γ, abs_nonneg y]
    calc g y ≤ Cζ * (1 + |γ + y|) ^ N := h1
      _ ≤ Cζ * ((1 + |γ|) * (1 + |y|)) ^ N := mul_le_mul_of_nonneg_left h2 hCζ
      _ = Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N := by rw [mul_pow]; ring
  have hIhalf := integrable_exp_neg_half_abs_mul_one_add_abs_pow N
  have hexpg : Integrable (fun y : ℝ => Real.exp (-(1 * |y|)) * g y) := by
    refine Integrable.mono' (hIhalf.const_mul (Cζ * (1 + |γ|) ^ N))
      ((by fun_prop : Continuous fun y : ℝ => Real.exp (-(1 * |y|))).mul
        hgcont).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have hg0 : 0 ≤ g y := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-(1 * |y|)) ≤ Real.exp (-(|y| / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg y])
    calc Real.exp (-(1 * |y|)) * g y
        ≤ Real.exp (-(|y| / 2)) * (Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N) :=
          mul_le_mul h1 (hgbound y) hg0 (Real.exp_pos _).le
      _ = Cζ * (1 + |γ|) ^ N * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by ring
  -- the integral of the majorant
  have hmaj_int : Integrable (fun y : ℝ =>
      Y ^ c * (12 * C * (Real.exp (-(1 * |y|)) + X * (Real.exp (-(1 * |y|)) * g y)))) :=
    ((hexp1.add (hexpg.const_mul (X : ℝ))).const_mul (12 * C)).const_mul (Y ^ c)
  have hint : Integrable (fun y : ℝ => expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I)) :=
    integrable_expDetIntegrand_line X ρ (by linarith) hβ2 hY (x := c) (by rw [hc]; linarith)
      (by rw [hc]; linarith)
      (fun m hm => by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, Nat.cast_zero, neg_zero] at hm
          rw [hc] at hm
          linarith
        · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
          rw [hc] at hm
          linarith) (by rw [hc]; linarith)
  have hstep1 := norm_integral_le_integral_norm (μ := volume)
    (fun y : ℝ => expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I))
  have hstep2 := integral_mono hint.norm hmaj_int hpt
  rw [integral_const_mul, integral_const_mul, integral_add hexp1 (hexpg.const_mul _),
    integral_const_mul] at hstep2
  -- the split of `∫ e^{-|y|} g`
  have hsplit := integral_add_compl (measurableSet_Icc (a := -L) (b := L)) hexpg
  have hIcc : ∫ y in Icc (-L) L, Real.exp (-(1 * |y|)) * g y ≤ ∫ y in (-L)..L, g y := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_mono_on hexpg.integrableOn
      (hgcont.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc ?_
    intro y _
    have hg0 : 0 ≤ g y := norm_nonneg _
    have h1 : Real.exp (-(1 * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg y])
    nlinarith
  have hcompl : ∫ y in (Icc (-L) L)ᶜ, Real.exp (-(1 * |y|)) * g y ≤
      Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁ := by
    have hmaj2 : Integrable (fun y : ℝ =>
        Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N)) :=
      hIhalf.const_mul _
    calc ∫ y in (Icc (-L) L)ᶜ, Real.exp (-(1 * |y|)) * g y
        ≤ ∫ y in (Icc (-L) L)ᶜ,
            Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by
          refine setIntegral_mono_on hexpg.integrableOn hmaj2.integrableOn
            measurableSet_Icc.compl ?_
          intro y hy
          have hyL : L < |y| := by
            simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hy
            rcases hy with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; exact h
          have hg0 : 0 ≤ g y := norm_nonneg _
          have h1 : Real.exp (-(1 * |y|)) ≤ Real.exp (-(L / 2)) * Real.exp (-(|y| / 2)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith)
          calc Real.exp (-(1 * |y|)) * g y
              ≤ (Real.exp (-(L / 2)) * Real.exp (-(|y| / 2))) *
                  (Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N) :=
                mul_le_mul h1 (hgbound y) hg0 (by positivity)
            _ = Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) *
                  (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by ring
      _ ≤ ∫ y : ℝ,
            Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) :=
          setIntegral_le_integral hmaj2 (Eventually.of_forall fun y => by positivity)
      _ = Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁ := by rw [integral_const_mul]
  have hEg : ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y ≤
      (∫ y in (-L)..L, g y) + Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁ := by
    rw [← hsplit]
    exact add_le_add hIcc hcompl
  have hYc : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le _
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hint_g : 0 ≤ ∫ y in (-L)..L, g y :=
    intervalIntegral.integral_nonneg (by linarith) fun y _ => norm_nonneg _
  refine le_trans hstep1 (le_trans hstep2 ?_)
  apply mul_le_mul_of_nonneg_left _ hYc
  have hfinal : 12 * C * (E₁ + X * ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y) ≤
      12 * C * (E₁ + 1) + X * (12 * C * (E₁ + 1)) * (∫ y in (-L)..L, g y) +
        X * (12 * C * (Cζ * I₁)) * (1 + |γ|) ^ N * Real.exp (-(L / 2)) := by
    have h12 : 0 ≤ 12 * C := by positivity
    have hXE : X * ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y ≤
        X * ((∫ y in (-L)..L, g y) + Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁) :=
      mul_le_mul_of_nonneg_left hEg hX0
    have hA : 12 * C * (E₁ + X * ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y) ≤
        12 * C * (E₁ + X * ((∫ y in (-L)..L, g y) +
          Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁)) :=
      mul_le_mul_of_nonneg_left (by linarith) h12
    refine le_trans hA ?_
    have hgE : 0 ≤ X * (12 * C) * (∫ y in (-L)..L, g y) := by positivity
    have : 12 * C * (E₁ + X * ((∫ y in (-L)..L, g y) +
          Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁)) =
        12 * C * E₁ + X * (12 * C * E₁) * 0 + X * (12 * C) * (∫ y in (-L)..L, g y) +
          X * (12 * C * (Cζ * I₁)) * (1 + |γ|) ^ N * Real.exp (-(L / 2)) := by ring
    rw [this]
    have hXEg : 0 ≤ X * (12 * C * E₁) * (∫ y in (-L)..L, g y) := by positivity
    nlinarith
  exact hfinal

end RHTower
