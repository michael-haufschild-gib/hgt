import GaloisForLFunctions.ThetaCuspSections.AllApertureFiniteRankCriterion
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay

/-!
# An explicit tail for the current

**Theorem** (`abs_current_le_explicit`). For `|a| ≤ ½`,

`|current a b| ≤ 6.05·10⁹ · |a| · e^{−(7/5)|b|}`.

The theta source on the line `Im z = 7/10` is at most `2770 e^{−2|Re z|}`. The Gaussian factor has
`cos(7/5) ≥ 0.169`, and `X^m e^{−βX} ≤ (m/β)^m e^{−m}` pays every power of `X = n² e^{2x}`, with
`Σ n⁻⁴` left over. The contour shift then gives `|Ξ(t + ia)| ≤ 4432 e^{−(7/10)|t|}` on `|a| ≤ ¾`;
Cauchy's estimate on circles of radius `1/8` gives the first two derivatives on `|a| ≤ ½`, and the
current vanishes at `a = 0`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar

/-! ## The source on the line `Im z = 7/10` -/

/-- `X^m e^{−βX} ≤ (m/β)^m e^{−m}`. -/
theorem pow_mul_exp_neg_le {β X : ℝ} (hβ : 0 < β) (hX : 0 ≤ X) {m : ℕ} (hm : 0 < m) :
    X ^ m * Real.exp (-(β * X)) ≤ ((m : ℝ) / β) ^ m * Real.exp (-(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨u, hu⟩ : ∃ u, u = β * X / m := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have h1 : u ≤ Real.exp (u - 1) := by
    have := Real.add_one_le_exp (u - 1)
    linarith only [this]
  have h2 : u ^ m ≤ Real.exp (β * X - m) := by
    have h3 := pow_le_pow_left₀ hu0 h1 m
    rw [← Real.exp_nat_mul] at h3
    refine h3.trans (le_of_eq ?_)
    congr 1
    rw [hu]
    field_simp
  have hX' : X = (m : ℝ) / β * u := by
    rw [hu]
    field_simp
  rw [hX', mul_pow]
  have hexp : Real.exp (β * X - m) = Real.exp (β * X) * Real.exp (-(m : ℝ)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp] at h2
  have h4 : u ^ m * Real.exp (-(β * ((m : ℝ) / β * u))) ≤ Real.exp (-(m : ℝ)) := by
    rw [← hX', Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith only [h2]
  calc ((m : ℝ) / β) ^ m * u ^ m * Real.exp (-(β * ((m : ℝ) / β * u)))
      = ((m : ℝ) / β) ^ m * (u ^ m * Real.exp (-(β * ((m : ℝ) / β * u)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- `cos(7/5) ≥ 0.169`: the sine of a small positive angle. -/
theorem cos_seven_fifths_ge : (0.169 : ℝ) ≤ Real.cos (7 / 5) := by
  have hπ := Real.pi_gt_d4
  have hid : Real.cos (7 / 5) = Real.sin (Real.pi / 2 - 7 / 5) := (Real.sin_pi_div_two_sub _).symm
  rw [hid]
  have hpos : (0.1707 : ℝ) ≤ Real.pi / 2 - 7 / 5 := by norm_num at hπ ⊢; linarith only [hπ]
  have hle : Real.pi / 2 - 7 / 5 ≤ 1 := by linarith only [Real.pi_lt_d2]
  have hmono : Real.sin 0.1707 ≤ Real.sin (Real.pi / 2 - 7 / 5) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by norm_num; linarith only [Real.pi_gt_three])
      (by linarith only [Real.pi_gt_three]) hpos
  have hs := Real.sin_gt_sub_cube (x := 0.1707) (by norm_num) (by norm_num)
  norm_num at hs
  linarith only [hmono, hs]

private theorem exp_neg_four_le : Real.exp (-(4 : ℝ)) ≤ 0.0184 := by
  have he := Real.exp_one_gt_d9
  have h : Real.exp (-(4 : ℝ)) = (Real.exp 1 ^ 4)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  rw [h]
  have hp : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he.le 4
  calc (Real.exp 1 ^ 4)⁻¹ ≤ ((2.7182818283 : ℝ) ^ 4)⁻¹ := inv_anti₀ (by norm_num) hp
    _ ≤ _ := by norm_num

private theorem exp_neg_three_le : Real.exp (-(3 : ℝ)) ≤ 0.05 := by
  have he := Real.exp_one_gt_d9
  have h : Real.exp (-(3 : ℝ)) = (Real.exp 1 ^ 3)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  rw [h]
  have hp : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
  calc (Real.exp 1 ^ 3)⁻¹ ≤ ((2.7182818283 : ℝ) ^ 3)⁻¹ := inv_anti₀ (by norm_num) hp
    _ ≤ _ := by norm_num

private theorem quartic_le {X : ℝ} (hX : 0 ≤ X) : X ^ 4 * Real.exp (-(0.53 * X)) ≤ 60 := by
  have h := pow_mul_exp_neg_le (β := 0.53) (by norm_num) hX (m := 4) (by norm_num)
  have h4 := exp_neg_four_le
  norm_num at h h4 ⊢
  have hc : (4 / (53 / 100) : ℝ) ^ 4 = 1600000000 / 493039 := by norm_num
  nlinarith only [h, h4, Real.exp_pos (-(4 : ℝ))]

private theorem cubic_le {X : ℝ} (hX : 0 ≤ X) : X ^ 3 * Real.exp (-(0.53 * X)) ≤ 10 := by
  have h := pow_mul_exp_neg_le (β := 0.53) (by norm_num) hX (m := 3) (by norm_num)
  have h3 := exp_neg_three_le
  norm_num at h h3 ⊢
  nlinarith only [h, h3, Real.exp_pos (-(3 : ℝ))]

/-- One term of the source on the line, paid by `n⁻⁴`. -/
theorem norm_term_le {z : ℂ} (him : |z.im| ≤ 7 / 10) (hre : 0 ≤ z.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖thetaCuspComplexTerm z n‖ * Real.exp (2 * z.re) ≤ 2558 * (1 / (n : ℝ) ^ 4) := by
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨x, hx⟩ : ∃ x, x = z.re := ⟨_, rfl⟩
  rw [← hx] at hre ⊢
  obtain ⟨X, hXdef⟩ : ∃ X, X = (n : ℝ) ^ 2 * Real.exp (2 * x) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hXdef]; positivity
  -- The Gaussian factor.
  have hcos : (0.169 : ℝ) ≤ Real.cos (2 * z.im) := by
    refine cos_seven_fifths_ge.trans ?_
    have h1 := cos_le_cos_of_abs_le (δ := 7 / 10) (y := z.im)
      (by linarith only [Real.pi_gt_d2]) him
    norm_num at h1 ⊢
    exact h1
  have hgauss : ‖Complex.exp (-(Real.pi : ℂ) * ((n : ℂ) * Complex.exp z) ^ 2)‖ ≤
      Real.exp (-(0.53 * X)) := by
    rw [norm_exp_neg_pi_sq, ← hx]
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0.53 ≤ Real.pi * Real.cos (2 * z.im) := by
      have h2 := mul_le_mul Real.pi_gt_d2.le hcos (by norm_num) hπ.le
      norm_num at h2 ⊢
      linarith only [h2]
    have h3 := mul_le_mul_of_nonneg_right h1 hX0.le
    rw [hXdef] at h3 ⊢
    nlinarith only [h3]
  -- The polynomial factor.
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (n : ℂ) * Complex.exp z := ⟨_, rfl⟩
  have hnw : ‖w‖ ^ 2 = X := by
    rw [hw, norm_mul, Complex.norm_natCast, Complex.norm_exp, ← hx, mul_pow, ← Real.exp_nat_mul,
      hXdef]
    norm_num
  have hpoly : ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ ≤
      2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) := by
    have h1 : ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖ ≤ 2 * Real.pi * X ^ 2 + 3 * X := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
      have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have e3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [e2, e3, ← hnw]
      apply le_of_eq
      ring
    rw [norm_mul]
    have h2 : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hπ]
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  -- Assemble.
  have hterm : ‖thetaCuspComplexTerm z n‖ ≤ Real.exp (x / 2) *
      (2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) * Real.exp (-(0.53 * X))) := by
    unfold thetaCuspComplexTerm thetaCuspComplexSeed
    rw [norm_mul, norm_mul, ← hw]
    have he : ‖Complex.exp (z / 2)‖ = Real.exp (x / 2) := by
      rw [Complex.norm_exp, hx]
      simp
    rw [he]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hg := hgauss
    rw [← hw] at hg
    exact mul_le_mul hpoly hg (norm_nonneg _) (by positivity)
  have hfront : Real.exp (x / 2) * Real.exp (2 * x) ≤ X ^ 2 / (n : ℝ) ^ 4 := by
    rw [← Real.exp_add, hXdef, mul_pow, ← Real.exp_nat_mul,
      mul_div_right_comm, show ((n : ℝ) ^ 2) ^ 2 / (n : ℝ) ^ 4 = 1 by field_simp, one_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith only [hre]
  have hq := quartic_le hX0.le
  have hc := cubic_le hX0.le
  have hE0 := Real.exp_pos (2 * x)
  obtain ⟨g, hg⟩ : ∃ g, g = Real.exp (-(0.53 * X)) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Real.exp_pos _
  rw [← hg] at hterm hq hc
  have hbrack : 0 ≤ 2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) * g := by positivity
  calc ‖thetaCuspComplexTerm z n‖ * Real.exp (2 * x)
      ≤ (Real.exp (x / 2) * (2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) * g)) *
          Real.exp (2 * x) := mul_le_mul_of_nonneg_right hterm hE0.le
    _ = (Real.exp (x / 2) * Real.exp (2 * x)) * (2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) * g) := by
        ring
    _ ≤ (X ^ 2 / (n : ℝ) ^ 4) * (2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) * g) :=
        mul_le_mul_of_nonneg_right hfront hbrack
    _ = (2 * Real.pi * (2 * Real.pi * (X ^ 4 * g) + 3 * (X ^ 3 * g))) * (1 / (n : ℝ) ^ 4) := by
        field_simp
        ring
    _ ≤ (2 * Real.pi * (2 * Real.pi * 60 + 3 * 10)) * (1 / (n : ℝ) ^ 4) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * Real.pi)
        linarith only [h1, hc]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h2 := Real.pi_lt_d4
        nlinarith only [h2, hπ, mul_pos hπ hπ]

/-- The source on the right half of the line. -/
theorem norm_source_le_of_nonneg {z : ℂ} (him : |z.im| ≤ 7 / 10) (hre : 0 ≤ z.re) :
    ‖thetaCuspStripSource z‖ ≤ 2770 * Real.exp (-(2 * z.re)) := by
  have hE0 := Real.exp_pos (2 * z.re)
  have hzeta : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 4) (Real.pi ^ 4 / 90) := hasSum_zeta_four
  have hb : ∀ n : ℕ, ‖thetaCuspComplexTerm z n‖ ≤
      2558 * (1 / (n : ℝ) ^ 4) * Real.exp (-(2 * z.re)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [thetaCuspComplexTerm, thetaCuspComplexSeed]
    · have h := norm_term_le him hre hn
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE0]
      exact h
  have hsum : Summable fun n : ℕ => 2558 * (1 / (n : ℝ) ^ 4) * Real.exp (-(2 * z.re)) :=
    (hzeta.summable.mul_left _).mul_right _
  have hnorm : Summable fun n : ℕ => ‖thetaCuspComplexTerm z n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have hval : ∑' n : ℕ, 2558 * (1 / (n : ℝ) ^ 4) * Real.exp (-(2 * z.re)) =
      2558 * (Real.pi ^ 4 / 90) * Real.exp (-(2 * z.re)) := by
    rw [tsum_mul_right, tsum_mul_left, hzeta.tsum_eq]
  have hπ4 : Real.pi ^ 4 / 90 ≤ 1.0824 := by
    have h1 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 4
    norm_num at h1 ⊢
    linarith only [h1]
  calc ‖thetaCuspStripSource z‖ ≤ ∑' n : ℕ, ‖thetaCuspComplexTerm z n‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, 2558 * (1 / (n : ℝ) ^ 4) * Real.exp (-(2 * z.re)) :=
        hnorm.tsum_le_tsum hb hsum
    _ = 2558 * (Real.pi ^ 4 / 90) * Real.exp (-(2 * z.re)) := hval
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        norm_num at hπ4 ⊢
        linarith only [hπ4]

/-- **The source on the line.** `‖Φ(z)‖ ≤ 2770 e^{−2|Re z|}` for `|Im z| ≤ 7/10`. -/
theorem norm_source_le {z : ℂ} (him : |z.im| ≤ 7 / 10) :
    ‖thetaCuspStripSource z‖ ≤ 2770 * Real.exp (-(2 * |z.re|)) := by
  rcases le_or_gt 0 z.re with hre | hre
  · rw [abs_of_nonneg hre]
    exact norm_source_le_of_nonneg him hre
  · have hzmem : z ∈ thetaCuspStrip := by
      rw [thetaCuspStrip, Set.mem_setOf_eq]
      linarith only [him, Real.pi_gt_d2]
    rw [← thetaCuspStripSource_neg hzmem, abs_of_neg hre]
    exact norm_source_le_of_nonneg (by rwa [Complex.neg_im, abs_neg])
      (by rw [Complex.neg_re]; linarith only [hre])

/-! ## `Ξ` on horizontal lines -/

private theorem integral_exp_neg_mul_abs {r : ℝ} (hr : 0 < r) :
    ∫ x : ℝ, Real.exp (-(r * |x|)) = 2 / r := by
  have h := integral_comp_abs (f := fun u : ℝ => Real.exp (-(r * u)))
  rw [h]
  have e : ∀ u : ℝ, Real.exp (-(r * u)) = Real.exp (-r * u) := fun u => by ring_nf
  simp_rw [e]
  rw [integral_exp_mul_Ioi (by linarith only [hr]) 0]
  simp
  field_simp

/-- `|Ξ(t + ia)| ≤ 4432 e^{−(7/10)|t|}` for `|a| ≤ ¾`. -/
theorem norm_XiC_le (t a : ℝ) (ha : |a| ≤ 3 / 4) :
    ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ 4432 * Real.exp (-(7 / 10 * |t|)) := by
  have hcore : ∀ t a : ℝ, t ≤ 0 → |a| ≤ 3 / 4 →
      ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ 4432 * Real.exp (-(7 / 10 * |t|)) := by
    intro t a ht ha
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (t : ℂ) + (a : ℂ) * I := ⟨_, rfl⟩
    have hwre : w.re = t := by rw [hw]; simp
    have hwim : w.im = a := by rw [hw]; simp
    rw [← hw]
    have hgen : ∀ (M : ℝ) (z : ℂ), t * z.im ≤ M → |z.im| ≤ 7 / 10 →
        ‖thetaStripKernel w z‖ ≤ (2770 * Real.exp M) * Real.exp (-(5 / 4 * |z.re|)) := by
      intro M z hM hz
      rw [norm_thetaStripKernel, hwre, hwim]
      have hK := norm_source_le hz
      have hexp : Real.exp (t * z.im + a * z.re) ≤ Real.exp M * Real.exp (3 / 4 * |z.re|) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h2 : a * z.re ≤ 3 / 4 * |z.re| := by
          calc a * z.re ≤ |a * z.re| := le_abs_self _
            _ = |a| * |z.re| := abs_mul _ _
            _ ≤ _ := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        linarith only [hM, h2]
      calc Real.exp (t * z.im + a * z.re) * ‖thetaCuspStripSource z‖
          ≤ (Real.exp M * Real.exp (3 / 4 * |z.re|)) * (2770 * Real.exp (-(2 * |z.re|))) :=
            mul_le_mul hexp hK (norm_nonneg _) (by positivity)
        _ = (2770 * Real.exp M) * (Real.exp (3 / 4 * |z.re|) * Real.exp (-(2 * |z.re|))) := by ring
        _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
    have hbound : ∀ z : ℂ, |z.im| ≤ 7 / 10 →
        ‖thetaStripKernel w z‖ ≤ (2770 * Real.exp (|t| * (7 / 10))) *
          Real.exp (-(5 / 4 * |z.re|)) := by
      intro z hz
      refine hgen _ z ?_ hz
      calc t * z.im ≤ |t * z.im| := le_abs_self _
        _ = |t| * |z.im| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
    have hdiff : ∀ z : ℂ, |z.im| ≤ 7 / 10 → DifferentiableAt ℂ (thetaStripKernel w) z := by
      intro z hz
      refine differentiableAt_thetaStripKernel w ?_
      rw [thetaCuspStrip, Set.mem_setOf_eq]
      linarith only [hz, Real.pi_gt_d2]
    have hshift := integral_horizontal_shift_of_decay (F := thetaStripKernel w) (c := 7 / 10)
      (C := 2770 * Real.exp (|t| * (7 / 10))) (r := 5 / 4) (by norm_num) (by norm_num) hdiff hbound
    have hFL : (∫ x : ℝ, thetaStripKernel w ((x : ℝ) : ℂ)) = XiC w := by
      rw [integral_thetaStripKernel_real]
      refine thetaCuspFourierLaplace_eq_XiC_on_strip ?_
      rw [thetaCuspFourierLaplaceStrip, Set.mem_setOf_eq, hwim]
      have := abs_le.mp ha
      constructor <;> linarith only [this.1, this.2]
    rw [← hFL, ← hshift]
    have hmaj : Integrable (fun x : ℝ =>
        (2770 * Real.exp (t * (7 / 10))) * Real.exp (-(5 / 4 * |x|))) :=
      (integrable_exp_neg_mul_abs' (by norm_num)).const_mul _
    have hbd : ∀ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖ ≤
        (2770 * Real.exp (t * (7 / 10))) * Real.exp (-(5 / 4 * |x|)) := by
      intro x
      have hval : ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I).im = 7 / 10 := by simp
      have hre : ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I).re = x := by simp
      have h := hgen (t * (7 / 10)) _ (by rw [hval]) (by rw [hval]; norm_num [abs_of_pos])
      rwa [hre] at h
    have hcont : Continuous fun x : ℝ => thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      have hmem : |((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I).im| ≤ 7 / 10 := by
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add,
          add_zero]
        norm_num [abs_of_pos]
      have hcomp := ((hdiff _ hmem).continuousAt).comp (x := x)
        (f := fun y : ℝ => ((y : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)) (by fun_prop)
      simpa [Function.comp_def] using hcomp
    have hint : ∫ x : ℝ, (2770 * Real.exp (t * (7 / 10))) * Real.exp (-(5 / 4 * |x|)) =
        4432 * Real.exp (-(7 / 10 * |t|)) := by
      rw [integral_const_mul, integral_exp_neg_mul_abs (by norm_num), abs_of_nonpos ht]
      have : t * (7 / 10) = -(7 / 10 * -t) := by ring
      rw [this]
      norm_num
      ring
    calc ‖∫ x : ℝ, thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖
        ≤ ∫ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, (2770 * Real.exp (t * (7 / 10))) * Real.exp (-(5 / 4 * |x|)) := by
          refine integral_mono ?_ hmaj hbd
          refine Integrable.mono' hmaj hcont.norm.aestronglyMeasurable
            (Filter.Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hbd x
      _ = _ := hint
  rcases le_or_gt t 0 with ht | ht
  · exact hcore t a ht ha
  · have heven : XiC ((t : ℂ) + (a : ℂ) * I) = XiC (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * I) := by
      rw [show (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * I) = -((t : ℂ) + (a : ℂ) * I) by push_cast; ring,
        XiC_even]
    rw [heven]
    have h := hcore (-t) (-a) (by linarith only [ht]) (by rwa [abs_neg])
    rwa [abs_neg] at h

/-! ## Derivatives by Cauchy -/

/-- Cauchy's estimate transports a strip bound with exponential decay to the derivative. -/
theorem norm_deriv_le_of_strip {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C δ A ρ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hb : ∀ t a : ℝ, |a| ≤ A → ‖f ((t : ℂ) + (a : ℂ) * I)‖ ≤ C * Real.exp (-(δ * |t|)))
    (t a : ℝ) (ha : |a| ≤ A - ρ) :
    ‖deriv f ((t : ℂ) + (a : ℂ) * I)‖ ≤ C * Real.exp (δ * ρ) / ρ * Real.exp (-(δ * |t|)) := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (t : ℂ) + (a : ℂ) * I := ⟨_, rfl⟩
  rw [← hw]
  have hsphere (u : ℂ) (hu : u ∈ Metric.sphere w ρ) :
      ‖f u‖ ≤ C * Real.exp (δ * ρ) * Real.exp (-(δ * |t|)) := by
    have hu' : ‖u - w‖ = ρ := by simpa only [Metric.mem_sphere, dist_eq_norm] using hu
    have hi : |u.im - a| ≤ ρ := by
      have h := Complex.abs_im_le_norm (u - w)
      rw [hu', Complex.sub_im, hw] at h
      simpa using h
    have hr : |u.re - t| ≤ ρ := by
      have h := Complex.abs_re_le_norm (u - w)
      rw [hu', Complex.sub_re, hw] at h
      simpa using h
    have him : |u.im| ≤ A := by
      have h1 := abs_sub_abs_le_abs_sub u.im a
      linarith only [h1, hi, ha]
    have hu2 := hb u.re u.im him
    rw [Complex.re_add_im] at hu2
    refine hu2.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    have h1 := abs_sub_abs_le_abs_sub t u.re
    rw [abs_sub_comm t u.re] at h1
    have h2 : δ * (|t| - ρ) ≤ δ * |u.re| := mul_le_mul_of_nonneg_left (by linarith only [h1, hr]) hδ
    linarith only [h2]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hf.diffContOnCl hsphere
  refine h.trans (le_of_eq ?_)
  field_simp

/-- The mean value theorem on a vertical segment through the real axis. -/
theorem norm_sub_vertical_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {B : ℝ} {b a : ℝ}
    (hd : ∀ a' : ℝ, |a'| ≤ |a| → ‖deriv f ((b : ℂ) + (a' : ℂ) * I)‖ ≤ B) :
    ‖f ((b : ℂ) - (a : ℂ) * I) - f (b : ℂ)‖ ≤ B * |a| := by
  let S : Set ℂ := {w : ℂ | w.re = b ∧ |w.im| ≤ |a|}
  have hS : Convex ℝ S := by
    intro x hx y hy p q hp hq hpq
    constructor
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [hx.1, hy.1]
      calc p * b + q * b = (p + q) * b := by ring
        _ = b := by rw [hpq, one_mul]
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      calc |p * x.im + q * y.im| ≤ |p * x.im| + |q * y.im| := abs_add_le _ _
        _ = p * |x.im| + q * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
        _ ≤ p * |a| + q * |a| := add_le_add (mul_le_mul_of_nonneg_left hx.2 hp)
            (mul_le_mul_of_nonneg_left hy.2 hq)
        _ = |a| := by rw [← add_mul, hpq, one_mul]
  have hz : (b : ℂ) ∈ S := by simp [S]
  have hy : (b : ℂ) - (a : ℂ) * I ∈ S := by simp [S]
  have hbound : ∀ w ∈ S, ‖deriv f w‖ ≤ B := by
    intro w hw
    have h := hd w.im hw.2
    have e : (b : ℂ) + (w.im : ℂ) * I = w := by
      apply Complex.ext
      · simp [hw.1]
      · simp
    rwa [e] at h
  have h := hS.norm_image_sub_le_of_norm_deriv_le (fun w _ => hf w) hbound hz hy
  have hn : ‖(b : ℂ) - (a : ℂ) * I - (b : ℂ)‖ = |a| := by
    rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  rwa [hn] at h

/-! ## The tail -/

private theorem exp_small_le : Real.exp (7 / 10 * (1 / 8)) ≤ 1.096 := by
  have h := Real.add_one_le_exp (-(7 / 10 * (1 / 8)))
  rw [Real.exp_neg] at h
  have hp := Real.exp_pos (7 / 10 * (1 / 8) : ℝ)
  have h2 : (0.9125 : ℝ) ≤ (Real.exp (7 / 10 * (1 / 8)))⁻¹ := by
    norm_num at h ⊢
    linarith only [h]
  have h3 := mul_le_mul_of_nonneg_right h2 hp.le
  rw [inv_mul_cancel₀ hp.ne'] at h3
  linarith only [h3]

/-- `Ξ'` on `|a| ≤ 5/8`. -/
theorem norm_deriv_XiC_le (t a : ℝ) (ha : |a| ≤ 5 / 8) :
    ‖deriv XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ 38860 * Real.exp (-(7 / 10 * |t|)) := by
  have h := norm_deriv_le_of_strip XiC_differentiable (C := 4432) (δ := 7 / 10) (A := 3 / 4)
    (ρ := 1 / 8) (by norm_num) (by norm_num) (by norm_num) norm_XiC_le t a
    (by norm_num at ha ⊢; linarith only [ha])
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hs := exp_small_le
  have hp := Real.exp_pos (7 / 10 * (1 / 8) : ℝ)
  rw [div_le_iff₀ (by norm_num)]
  nlinarith only [hs, hp]

/-- `Ξ''` on `|a| ≤ ½`. -/
theorem norm_deriv_deriv_XiC_le (t a : ℝ) (ha : |a| ≤ 1 / 2) :
    ‖deriv (deriv XiC) ((t : ℂ) + (a : ℂ) * I)‖ ≤ 340726 * Real.exp (-(7 / 10 * |t|)) := by
  have hd : Differentiable ℂ (deriv XiC) :=
    fun z => ((XiC_differentiable.analyticAt z).deriv).differentiableAt
  have h := norm_deriv_le_of_strip hd (C := 38860) (δ := 7 / 10) (A := 5 / 8) (ρ := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num) norm_deriv_XiC_le t a
    (by norm_num at ha ⊢; linarith only [ha])
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hs := exp_small_le
  have hp := Real.exp_pos (7 / 10 * (1 / 8) : ℝ)
  rw [div_le_iff₀ (by norm_num)]
  nlinarith only [hs, hp]

/-- **The explicit tail of the current.** -/
theorem abs_current_le_explicit {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    |current a b| ≤ 6050000000 * |a| * Real.exp (-(7 / 5 * |b|)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Real.exp (-(7 / 10 * |b|)) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Real.exp_pos _
  have hgg : Real.exp (-(7 / 5 * |b|)) = g * g := by
    rw [hg, ← Real.exp_add]
    congr 1
    ring
  have hd : Differentiable ℂ (deriv XiC) :=
    fun z => ((XiC_differentiable.analyticAt z).deriv).differentiableAt
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (b : ℂ) - (a : ℂ) * I := ⟨_, rfl⟩
  have hzform : z = (b : ℂ) + ((-a : ℝ) : ℂ) * I := by
    rw [hz]
    push_cast
    ring
  have hU : ‖XiC z - XiC (b : ℂ)‖ ≤ 38860 * g * |a| := by
    rw [hz]
    refine norm_sub_vertical_le XiC_differentiable fun a' ha' => ?_
    rw [← hg]
    exact norm_deriv_XiC_le b a' (ha'.trans (ha.trans (by norm_num)))
  have hV : ‖deriv XiC z - deriv XiC (b : ℂ)‖ ≤ 340726 * g * |a| := by
    rw [hz]
    refine norm_sub_vertical_le hd fun a' ha' => ?_
    rw [← hg]
    exact norm_deriv_deriv_XiC_le b a' (ha'.trans ha)
  have hv : ‖deriv XiC z‖ ≤ 38860 * g := by
    rw [hzform, hg]
    exact norm_deriv_XiC_le b (-a) (by rw [abs_neg]; exact ha.trans (by norm_num))
  have hu₀ : ‖XiC (b : ℂ)‖ ≤ 4432 * g := by
    have h := norm_XiC_le b 0 (by norm_num)
    simpa [hg] using h
  have hdiff := current_difference_le (XiC (b : ℂ)) (XiC z) (deriv XiC (b : ℂ)) (deriv XiC z)
  have hrew : current a b = 2 * ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z)).re := by
    rw [hz]
    rfl
  have hrew₀ : 2 * ((starRingEnd ℂ) (XiC (b : ℂ)) * (-I * deriv XiC (b : ℂ))).re = 0 := by
    have h := current_zero b
    have hz0 : ((b : ℂ) - ((0 : ℝ) : ℂ) * I) = (b : ℂ) := by simp
    rw [current, hz0] at h
    exact h
  rw [hrew₀, sub_zero, ← hrew] at hdiff
  have habs := abs_nonneg a
  have h1 := mul_le_mul hU hv (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul hu₀ hV (norm_nonneg _) (by positivity)
  rw [hgg]
  have hpos : 0 ≤ |a| * (g * g) := by positivity
  nlinarith only [hdiff, h1, h2, hpos]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
