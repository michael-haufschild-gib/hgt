import GaloisForLFunctions.RHTower.ZetaLeftLineGaussianTerms

/-!
# Real parts of Gaussian zero sums

For `H` holomorphic on `Im s > 0`, with `F = H ζ'/ζ` conjugation-symmetric and integrable on the line
`Re s = −½`, the real part of `Σ_{ρ ∈ [−½, 11/10] × [t₀, Y]} m_ρ H(ρ)` equals
`−(1/4π) Re ∫_ℝ F(−½ + iy) dy` up to the bottom, top and right edges and the two pieces
`∫_0^{t₀}`, `∫_{y > Y}` of the left line (`abs_re_zeroSum_add_le`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

theorem leftEdge_point (t₀ y : ℝ) :
    (((((-1 / 2 : ℂ) + t₀ * I).re : ℝ) : ℂ) + (y : ℂ) * I) = leftPt y := by
  simp only [leftPt]
  congr 1
  simp

theorem rightEdge_point (Y y : ℝ) :
    (((((11 / 10 : ℂ) + Y * I).re : ℝ) : ℂ) + (y : ℂ) * I) = ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I := by
  congr 2
  simp

/-- **Edge decomposition of the real part of a zero sum.** -/
theorem abs_re_zeroSum_add_le {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H {s : ℂ | 0 < s.im}) {t₀ Y : ℝ}
    (ht₀ : 0 < t₀) (hY : t₀ < Y)
    (hbot : ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + t₀ * I) ≠ 0)
    (htop : ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + Y * I) ≠ 0)
    (hint : Integrable fun y : ℝ => H (leftPt y) * (deriv riemannZeta (leftPt y) /
      riemannZeta (leftPt y)))
    (hconj : ∀ y : ℝ, H (leftPt (-y)) * (deriv riemannZeta (leftPt (-y)) / riemannZeta (leftPt (-y))) =
      (starRingEnd ℂ) (H (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)))) :
    |(∑ w ∈ rectZeros t₀ Y, (mult w : ℂ) * H w).re +
        (1 / (4 * Real.pi)) * (∫ y : ℝ, H (leftPt y) * (deriv riemannZeta (leftPt y) /
          riemannZeta (leftPt y))).re| ≤
      (1 / (2 * Real.pi)) *
        (‖∫ x in (-1 / 2 : ℝ)..(11 / 10), H ((x : ℂ) + t₀ * I) *
            (deriv riemannZeta ((x : ℂ) + t₀ * I) / riemannZeta ((x : ℂ) + t₀ * I))‖ +
          ‖∫ x in (-1 / 2 : ℝ)..(11 / 10), H ((x : ℂ) + Y * I) *
            (deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I))‖ +
          ‖∫ y in t₀..Y, H (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) *
            (deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
              riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I))‖ +
          ‖∫ y in (0 : ℝ)..t₀, H (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ +
          ‖∫ y in Ioi Y, H (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖) := by
  set F : ℂ → ℂ := fun s => H s * (deriv riemannZeta s / riemannZeta s) with hF
  have hsub : (uIcc (-1 / 2 : ℝ) (11 / 10) ×ℂ uIcc t₀ Y) ⊆ {s : ℂ | 0 < s.im} := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le hY.le] at hs
    show 0 < s.im
    linarith [hs.2.1]
  have hcont := zeroSum_eq_rectIntegral (isOpen_lt continuous_const Complex.continuous_im) hH ht₀ hY
    hsub hbot htop
  unfold rectIntegral at hcont
  set z₁ : ℂ := (-1 / 2 : ℂ) + t₀ * I with hz₁
  set z₂ : ℂ := (11 / 10 : ℂ) + Y * I with hz₂
  have h1re : z₁.re = -1 / 2 := by simp [hz₁]
  have h1im : z₁.im = t₀ := by simp [hz₁]
  have h2re : z₂.re = 11 / 10 := by simp [hz₂]
  have h2im : z₂.im = Y := by simp [hz₂]
  rw [h1re, h2re, h1im, h2im] at hcont
  set Bt := ∫ x in (-1 / 2 : ℝ)..(11 / 10), F ((x : ℂ) + t₀ * I) with hBt
  set Tp := ∫ x in (-1 / 2 : ℝ)..(11 / 10), F ((x : ℂ) + Y * I) with hTp
  set R := ∫ y in t₀..Y, F (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) with hR
  set Lf := ∫ y in t₀..Y, F (leftPt y) with hLf
  have hLf' : ∫ y in t₀..Y, F ((((-1 / 2 : ℝ)) : ℂ) + (y : ℂ) * I) = Lf := by
    rw [hLf]; congr 1; funext y; congr 1; simp [leftPt]
  rw [hLf'] at hcont
  -- the zero sum
  set S := ∑ w ∈ rectZeros t₀ Y, (mult w : ℂ) * H w with hS
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_pos.ne'
  have hSeq : S = (Bt - Tp) / (2 * Real.pi * I) + (R - Lf) / (2 * Real.pi) := by
    have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    field_simp
    rw [smul_eq_mul, smul_eq_mul] at hcont
    linear_combination hcont
  -- the left line through the full line
  have hsym := re_integral_eq_of_conj (f := fun y => F (leftPt y)) hint
    (fun y => by simp only [hF]; exact hconj y) ht₀.le hY.le
  have hreL : Lf.re = (1 / 2) * (∫ y : ℝ, F (leftPt y)).re -
      (∫ y in (0 : ℝ)..t₀, F (leftPt y)).re - (∫ y in Ioi Y, F (leftPt y)).re := by
    rw [hLf]; linarith
  have hre : S.re + (1 / (4 * Real.pi)) * (∫ y : ℝ, F (leftPt y)).re =
      ((Bt - Tp) / (2 * Real.pi * I)).re + (1 / (2 * Real.pi)) * (R.re +
        (∫ y in (0 : ℝ)..t₀, F (leftPt y)).re + (∫ y in Ioi Y, F (leftPt y)).re) := by
    rw [hSeq, Complex.add_re]
    have : ((R - Lf) / (2 * Real.pi : ℂ)).re = (R.re - Lf.re) / (2 * Real.pi) := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re,
        Complex.sub_re]
    rw [this, hreL]
    field_simp
    ring
  simp only [hF] at hre ⊢
  rw [hre]
  have h2π : 0 < 2 * Real.pi := by positivity
  have hb1 : |((Bt - Tp) / (2 * Real.pi * I)).re| ≤ (1 / (2 * Real.pi)) * (‖Bt‖ + ‖Tp‖) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, show ‖(2 : ℂ)‖ = 2 by norm_num, div_eq_inv_mul, one_div,
      mul_inv]
    apply mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
  have hb2 : |(1 / (2 * Real.pi)) * (R.re + (∫ y in (0 : ℝ)..t₀, F (leftPt y)).re +
      (∫ y in Ioi Y, F (leftPt y)).re)| ≤ (1 / (2 * Real.pi)) * (‖R‖ +
        ‖∫ y in (0 : ℝ)..t₀, F (leftPt y)‖ + ‖∫ y in Ioi Y, F (leftPt y)‖) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      exact Complex.abs_re_le_norm _
  calc _ ≤ |((Bt - Tp) / (2 * Real.pi * I)).re| + |(1 / (2 * Real.pi)) * (R.re +
        (∫ y in (0 : ℝ)..t₀, F (leftPt y)).re + (∫ y in Ioi Y, F (leftPt y)).re)| := abs_add_le _ _
    _ ≤ (1 / (2 * Real.pi)) * (‖Bt‖ + ‖Tp‖) + (1 / (2 * Real.pi)) * (‖R‖ +
        ‖∫ y in (0 : ℝ)..t₀, F (leftPt y)‖ + ‖∫ y in Ioi Y, F (leftPt y)‖) := add_le_add hb1 hb2
    _ = _ := by simp only [hBt, hTp, hR, hF]; ring

/-! ## Edge bounds for `H = h · g_T` -/

theorem norm_gaussWeight (T : ℝ) (s : ℂ) :
    ‖gaussWeight T s‖ = Real.exp (((s.re - 1 / 2) ^ 2 - s.im ^ 2) / T ^ 2) := by
  unfold gaussWeight
  rw [Complex.norm_exp]
  congr 1
  have e : (s - 1 / 2) ^ 2 / (T : ℂ) ^ 2 =
      (((s.re - 1 / 2) ^ 2 - s.im ^ 2 : ℝ) : ℂ) / ((T ^ 2 : ℝ) : ℂ) +
        (((2 * (s.re - 1 / 2) * s.im) : ℝ) : ℂ) * I / ((T ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im s]
    push_cast
    rw [← add_div]
    congr 1
    linear_combination (s.im : ℂ) ^ 2 * Complex.I_sq
  rw [e, Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.ofReal_re]
  simp

theorem norm_gaussWeight_le_of_re {T : ℝ} (hT : 1 ≤ T) {s : ℂ} (hre : |s.re - 1 / 2| ≤ 1) :
    ‖gaussWeight T s‖ ≤ Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2)) := by
  rw [norm_gaussWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have h1 : (s.re - 1 / 2) ^ 2 ≤ 1 := by
    have := sq_abs (s.re - 1 / 2); nlinarith [abs_nonneg (s.re - 1 / 2)]
  have h2 : (s.re - 1 / 2) ^ 2 / T ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have : ((s.re - 1 / 2) ^ 2 - s.im ^ 2) / T ^ 2 = (s.re - 1 / 2) ^ 2 / T ^ 2 - s.im ^ 2 / T ^ 2 := by
    ring
  linarith

/-- **Bottom edge**: bounded uniformly in `T ≥ 1`. -/
theorem exists_bottom_edge_le {h : ℂ → ℂ} {t₀ : ℝ}
    (hcont : ContinuousOn (fun x : ℝ => h ((x : ℂ) + t₀ * I) *
      (deriv riemannZeta ((x : ℂ) + t₀ * I) / riemannZeta ((x : ℂ) + t₀ * I))) (Icc (-1 / 2) (11 / 10))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 1 ≤ T →
      ‖∫ x in (-1 / 2 : ℝ)..(11 / 10), (h ((x : ℂ) + t₀ * I) * gaussWeight T ((x : ℂ) + t₀ * I)) *
        (deriv riemannZeta ((x : ℂ) + t₀ * I) / riemannZeta ((x : ℂ) + t₀ * I))‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M₀ 0 * Real.exp 1 * (8 / 5), by positivity, fun T hT => ?_⟩
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := max M₀ 0 * Real.exp 1)
    fun x hx => ?_).trans (le_of_eq ?_)
  · rw [Set.uIoc_of_le (by norm_num)] at hx
    have hxI : x ∈ Icc (-1 / 2 : ℝ) (11 / 10) := ⟨hx.1.le, hx.2⟩
    have h1 := hM₀ x hxI
    have hg : ‖gaussWeight T ((x : ℂ) + t₀ * I)‖ ≤ Real.exp 1 := by
      refine (norm_gaussWeight_le_of_re hT (by
        simp; rw [abs_le]; constructor <;> linarith [hxI.1, hxI.2])).trans ?_
      have hq : 0 ≤ ((x : ℂ) + t₀ * I).im ^ 2 / T ^ 2 := by positivity
      have he : Real.exp (-(((x : ℂ) + t₀ * I).im ^ 2 / T ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      calc Real.exp 1 * Real.exp (-(((x : ℂ) + t₀ * I).im ^ 2 / T ^ 2)) ≤ Real.exp 1 * 1 := by
            gcongr
        _ = _ := mul_one _
    calc ‖h ((x : ℂ) + t₀ * I) * gaussWeight T ((x : ℂ) + t₀ * I) *
          (deriv riemannZeta ((x : ℂ) + t₀ * I) / riemannZeta ((x : ℂ) + t₀ * I))‖
        = ‖h ((x : ℂ) + t₀ * I) * (deriv riemannZeta ((x : ℂ) + t₀ * I) /
            riemannZeta ((x : ℂ) + t₀ * I))‖ * ‖gaussWeight T ((x : ℂ) + t₀ * I)‖ := by
          rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ max M₀ 0 * Real.exp 1 := mul_le_mul (h1.trans (le_max_left _ _)) hg (norm_nonneg _)
          (le_max_right _ _)
  · rw [abs_of_pos (by norm_num)]; ring

/-- `(1 + Y)^m e^{−Y} ≤ m! e`. -/
theorem one_add_pow_mul_exp_neg_le (m : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    (1 + Y) ^ m * Real.exp (-Y) ≤ m.factorial * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (1 + Y) (by linarith) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h
  have he : Real.exp (1 + Y) * Real.exp (-Y) = Real.exp 1 := by rw [← Real.exp_add]; ring_nf
  calc (1 + Y) ^ m * Real.exp (-Y) ≤ (Real.exp (1 + Y) * m.factorial) * Real.exp (-Y) := by gcongr
    _ = m.factorial * (Real.exp (1 + Y) * Real.exp (-Y)) := by ring
    _ = _ := by rw [he]

/-- **Top edge**: with `Y ≥ T² ≥ 1`, `|h| ≤ C_h (1 + Y)^k` and `|ζ'/ζ| ≤ C Y²` on the edge, the top
edge is bounded. -/
theorem top_edge_le {h : ℂ → ℂ} {T Y Ch Ctop : ℝ} {k : ℕ} (hT : 1 ≤ T) (hY : T ^ 2 ≤ Y)
    (hCh : 0 ≤ Ch) (hCtop : 0 ≤ Ctop)
    (hh : ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), ‖h ((x : ℂ) + Y * I)‖ ≤ Ch * (1 + Y) ^ k)
    (hz : ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10),
      ‖deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I)‖ ≤ Ctop * Y ^ 2) :
    ‖∫ x in (-1 / 2 : ℝ)..(11 / 10), (h ((x : ℂ) + Y * I) * gaussWeight T ((x : ℂ) + Y * I)) *
        (deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I))‖ ≤
      Ch * Ctop * ((k + 2).factorial * Real.exp 1) * Real.exp 1 * (8 / 5) := by
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hY1 : 1 ≤ Y := le_trans hT2 hY
  have hY0 : 0 ≤ Y := by linarith
  have hYY : Y ≤ Y ^ 2 / T ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Ch * Ctop * ((k + 2).factorial * Real.exp 1) * Real.exp 1) fun x hx => ?_).trans
    (le_of_eq ?_)
  · rw [Set.uIoc_of_le (by norm_num)] at hx
    have hxI : x ∈ Icc (-1 / 2 : ℝ) (11 / 10) := ⟨hx.1.le, hx.2⟩
    have hg : ‖gaussWeight T ((x : ℂ) + Y * I)‖ ≤ Real.exp 1 * Real.exp (-Y) := by
      refine (norm_gaussWeight_le_of_re hT (by simp; rw [abs_le]; constructor <;>
        linarith [hxI.1, hxI.2])).trans ?_
      gcongr
      simp
      linarith
    have hpow : (1 + Y) ^ k * Y ^ 2 ≤ (1 + Y) ^ (k + 2) := by
      rw [pow_add]; gcongr; linarith
    have hfin := one_add_pow_mul_exp_neg_le (k + 2) hY0
    calc ‖h ((x : ℂ) + Y * I) * gaussWeight T ((x : ℂ) + Y * I) *
          (deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I))‖
        = ‖h ((x : ℂ) + Y * I)‖ * ‖deriv riemannZeta ((x : ℂ) + Y * I) /
            riemannZeta ((x : ℂ) + Y * I)‖ * ‖gaussWeight T ((x : ℂ) + Y * I)‖ := by
          rw [norm_mul, norm_mul]; ring
      _ ≤ (Ch * (1 + Y) ^ k) * (Ctop * Y ^ 2) * (Real.exp 1 * Real.exp (-Y)) := by
          gcongr
          · exact hh x hxI
          · exact hz x hxI
      _ = Ch * Ctop * ((1 + Y) ^ k * Y ^ 2 * Real.exp (-Y)) * Real.exp 1 := by ring
      _ ≤ Ch * Ctop * ((1 + Y) ^ (k + 2) * Real.exp (-Y)) * Real.exp 1 := by gcongr
      _ ≤ Ch * Ctop * ((k + 2).factorial * Real.exp 1) * Real.exp 1 := by gcongr
  · rw [abs_of_pos (by norm_num)]; ring

theorem integral_exp_neg_sq_div {T : ℝ} (hT : 0 < T) :
    ∫ y : ℝ, Real.exp (-(y ^ 2 / T ^ 2)) = Real.sqrt Real.pi * T := by
  have h := integral_gaussian (1 / T ^ 2)
  have e : (fun x : ℝ => Real.exp (-(1 / T ^ 2) * x ^ 2)) = fun y => Real.exp (-(y ^ 2 / T ^ 2)) := by
    funext y; congr 1; ring
  rw [e] at h
  rw [h, show Real.pi / (1 / T ^ 2) = Real.pi * T ^ 2 by field_simp, Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_sq hT.le]

theorem integrable_exp_neg_sq_div {T : ℝ} (hT : 0 < T) :
    Integrable fun y : ℝ => Real.exp (-(y ^ 2 / T ^ 2)) := by
  have h := integrable_exp_neg_mul_sq (b := 1 / T ^ 2) (by positivity)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only; congr 1; ring

/-- **Right edge** on `Re s = 11/10`: `O(T)`. -/
theorem right_edge_le {h : ℂ → ℂ} {T t₀ Y CR K : ℝ} (hT : 1 ≤ T) (hY : t₀ ≤ Y) (hCR : 0 ≤ CR)
    (hK : 0 ≤ K)
    (hh : ∀ y : ℝ, ‖h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ CR)
    (hz : ∀ y : ℝ, ‖deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
      riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ K)
    (hcont : Continuous fun y : ℝ => (h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) *
      gaussWeight T (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)) *
      (deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
        riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I))) :
    ‖∫ y in t₀..Y, (h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) *
        gaussWeight T (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)) *
        (deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
          riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I))‖ ≤
      CR * K * Real.exp 1 * (Real.sqrt Real.pi * T) := by
  have hT0 : 0 < T := by linarith
  set F : ℝ → ℂ := fun y => (h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) *
    gaussWeight T (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)) *
    (deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
      riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)) with hF
  have hpt : ∀ y : ℝ, ‖F y‖ ≤ CR * K * Real.exp 1 * Real.exp (-(y ^ 2 / T ^ 2)) := by
    intro y
    have hg := norm_gaussWeight_le_of_re hT (s := ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)
      (by simp; norm_num)
    have him : (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [him] at hg
    simp only [hF]
    rw [norm_mul, norm_mul]
    calc ‖h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ * ‖gaussWeight T (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ *
          ‖deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
            riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ CR * (Real.exp 1 * Real.exp (-(y ^ 2 / T ^ 2))) * K := by
          gcongr
          · exact hh y
          · exact hz y
      _ = _ := by ring
  have hmaj : Integrable fun y : ℝ => CR * K * Real.exp 1 * Real.exp (-(y ^ 2 / T ^ 2)) :=
    (integrable_exp_neg_sq_div hT0).const_mul _
  calc ‖∫ y in t₀..Y, F y‖ ≤ ∫ y in t₀..Y, ‖F y‖ := intervalIntegral.norm_integral_le_integral_norm hY
    _ ≤ ∫ y in t₀..Y, CR * K * Real.exp 1 * Real.exp (-(y ^ 2 / T ^ 2)) :=
        intervalIntegral.integral_mono_on hY (hcont.norm.intervalIntegrable _ _)
          (hmaj.intervalIntegrable) fun y _ => hpt y
    _ ≤ ∫ y : ℝ, CR * K * Real.exp 1 * Real.exp (-(y ^ 2 / T ^ 2)) := by
        rw [intervalIntegral.integral_of_le hY]
        exact setIntegral_le_integral hmaj (Eventually.of_forall fun y => by positivity)
    _ = CR * K * Real.exp 1 * (Real.sqrt Real.pi * T) := by
        rw [integral_const_mul, integral_exp_neg_sq_div hT0]

/-- **The left line on `[0, t₀]`**: bounded uniformly in `T ≥ 1`. -/
theorem exists_left_piece_le {h : ℂ → ℂ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hcont : ContinuousOn (fun y : ℝ => h (leftPt y) *
      (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))) (Icc 0 t₀)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 1 ≤ T →
      ‖∫ y in (0 : ℝ)..t₀, (h (leftPt y) * gaussWeight T (leftPt y)) *
        (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M₀ 0 * Real.exp 1 * t₀, by positivity, fun T hT => ?_⟩
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := max M₀ 0 * Real.exp 1)
    fun y hy => ?_).trans (le_of_eq ?_)
  · rw [Set.uIoc_of_le ht₀] at hy
    have hyI : y ∈ Icc 0 t₀ := ⟨hy.1.le, hy.2⟩
    have h1 := hM₀ y hyI
    have hg : ‖gaussWeight T (leftPt y)‖ ≤ Real.exp 1 := by
      refine (norm_gaussWeight_le_of_re hT (by rw [leftPt_re]; norm_num)).trans ?_
      calc Real.exp 1 * Real.exp (-((leftPt y).im ^ 2 / T ^ 2)) ≤ Real.exp 1 * 1 := by
            gcongr
            exact Real.exp_le_one_iff.mpr (by
              have : 0 ≤ (leftPt y).im ^ 2 / T ^ 2 := by positivity
              linarith)
        _ = _ := mul_one _
    calc ‖h (leftPt y) * gaussWeight T (leftPt y) *
          (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖
        = ‖h (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ *
            ‖gaussWeight T (leftPt y)‖ := by rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ max M₀ 0 * Real.exp 1 := mul_le_mul (h1.trans (le_max_left _ _)) hg (norm_nonneg _)
          (le_max_right _ _)
  · rw [abs_of_nonneg (by linarith)]; ring

/-- **The left line beyond `Y ≥ T²`**: bounded uniformly. -/
theorem left_tail_le {h : ℂ → ℂ} {T Y CL : ℝ} {N : ℕ} (hT : 1 ≤ T) (hY : T ^ 2 ≤ Y)
    (hCL : 0 ≤ CL)
    (hh : ∀ y : ℝ, ‖h (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤
      CL * (1 + |y|) ^ N) :
    ‖∫ y in Ioi Y, (h (leftPt y) * gaussWeight T (leftPt y)) *
        (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤
      CL * Real.exp 1 * (N.factorial * 2 ^ N * Real.exp (1 / 2)) * 2 := by
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hY1 : 1 ≤ Y := le_trans hT2 hY
  set c : ℝ := CL * Real.exp 1 * (N.factorial * 2 ^ N * Real.exp (1 / 2)) with hc
  have hpt : ∀ y ∈ Ioi Y, ‖(h (leftPt y) * gaussWeight T (leftPt y)) *
      (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤ c * Real.exp (-(1 / 2) * y) := by
    intro y hy
    have hyY : Y < y := hy
    have hy0 : 0 < y := by linarith
    have hg : ‖gaussWeight T (leftPt y)‖ ≤ Real.exp 1 * Real.exp (-y) := by
      refine (norm_gaussWeight_le_of_re hT (by rw [leftPt_re]; norm_num)).trans ?_
      gcongr
      rw [leftPt_im]
      have : y ≤ y ^ 2 / T ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith
    have hpow : (1 + y) ^ N * Real.exp (-y) ≤ N.factorial * 2 ^ N * Real.exp (1 / 2) *
        Real.exp (-(1 / 2) * y) := by
      have h1 := Real.pow_div_factorial_le_exp ((1 + y) / 2) (by positivity) N
      have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
      rw [div_le_iff₀ hf, div_pow] at h1
      have h2 : (1 + y) ^ N ≤ N.factorial * 2 ^ N * Real.exp ((1 + y) / 2) := by
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        rw [div_le_iff₀ h2N] at h1
        linarith
      have he : Real.exp ((1 + y) / 2) * Real.exp (-y) = Real.exp (1 / 2) * Real.exp (-(1 / 2) * y) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      calc (1 + y) ^ N * Real.exp (-y) ≤ (N.factorial * 2 ^ N * Real.exp ((1 + y) / 2)) *
            Real.exp (-y) := by gcongr
        _ = N.factorial * 2 ^ N * (Real.exp ((1 + y) / 2) * Real.exp (-y)) := by ring
        _ = _ := by rw [he]; ring
    have habs : |y| = y := abs_of_pos hy0
    calc ‖(h (leftPt y) * gaussWeight T (leftPt y)) *
          (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖
        = ‖h (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ *
            ‖gaussWeight T (leftPt y)‖ := by rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ (CL * (1 + |y|) ^ N) * (Real.exp 1 * Real.exp (-y)) := by gcongr; exact hh y
      _ = CL * Real.exp 1 * ((1 + y) ^ N * Real.exp (-y)) := by rw [habs]; ring
      _ ≤ CL * Real.exp 1 * (N.factorial * 2 ^ N * Real.exp (1 / 2) * Real.exp (-(1 / 2) * y)) := by
          gcongr
      _ = c * Real.exp (-(1 / 2) * y) := by rw [hc]; ring
  have hmaj : IntegrableOn (fun y : ℝ => c * Real.exp (-(1 / 2) * y)) (Ioi Y) :=
    (integrableOn_exp_mul_Ioi (by norm_num) Y).const_mul c
  calc ‖∫ y in Ioi Y, (h (leftPt y) * gaussWeight T (leftPt y)) *
        (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖
      ≤ ∫ y in Ioi Y, c * Real.exp (-(1 / 2) * y) :=
        norm_integral_le_of_norm_le hmaj (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    _ = c * (2 * Real.exp (-(1 / 2) * Y)) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
        ring
    _ ≤ c * 2 := by
        have : Real.exp (-(1 / 2) * Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hc0 : 0 ≤ c := by positivity
        nlinarith

/-! ## The fixed bottom edge and admissible top edges -/

/-- A fixed zero-free bottom height in `[1, 2]`. -/
def bottomHeight : ℝ := Classical.choose exists_bottom_height

theorem bottomHeight_mem : bottomHeight ∈ Icc (1 : ℝ) 2 :=
  (Classical.choose_spec exists_bottom_height).1

theorem riemannZeta_bottom_ne_zero :
    ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + bottomHeight * I) ≠ 0 :=
  (Classical.choose_spec exists_bottom_height).2

theorem one_le_bottomHeight : 1 ≤ bottomHeight := bottomHeight_mem.1

/-- The constant of the admissible top edges. -/
def topConst : ℝ := Classical.choose exists_top_height

theorem topConst_nonneg : 0 ≤ topConst := (Classical.choose_spec exists_top_height).1

/-- `Y ∈ [T², T² + 3]` is an admissible top height: `ζ ≠ 0` and `|ζ'/ζ| ≤ C Y²` on `[−½, 2] + iY`. -/
def GoodTop (T Y : ℝ) : Prop :=
  Y ∈ Icc (T ^ 2) (T ^ 2 + 3) ∧ ∀ x ∈ Icc (-1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + Y * I) ≠ 0 ∧
    ‖deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I)‖ ≤ topConst * Y ^ 2

theorem exists_goodTop {T : ℝ} (hT : 4 ≤ T) : ∃ Y, GoodTop T Y :=
  (Classical.choose_spec exists_top_height).2 T hT

theorem GoodTop.top_ne_zero {T Y : ℝ} (h : GoodTop T Y) :
    ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + Y * I) ≠ 0 :=
  fun x hx => (h.2 x ⟨hx.1, by linarith [hx.2]⟩).1

theorem GoodTop.logDeriv_le {T Y : ℝ} (h : GoodTop T Y) :
    ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10),
      ‖deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I)‖ ≤ topConst * Y ^ 2 :=
  fun x hx => (h.2 x ⟨hx.1, by linarith [hx.2]⟩).2

theorem GoodTop.bottom_lt {T Y : ℝ} (hT : 2 ≤ T) (h : GoodTop T Y) : bottomHeight < Y := by
  have := h.1.1
  have := bottomHeight_mem.2
  nlinarith

/-! ## Conjugation symmetry on the left line -/

theorem leftPt_neg (y : ℝ) : leftPt (-y) = (starRingEnd ℂ) (leftPt y) := by
  apply Complex.ext
  · rw [Complex.conj_re, leftPt_re, leftPt_re]
  · rw [Complex.conj_im, leftPt_im, leftPt_im]

theorem gaussWeight_conj (T : ℝ) (s : ℂ) :
    gaussWeight T ((starRingEnd ℂ) s) = (starRingEnd ℂ) (gaussWeight T s) := by
  unfold gaussWeight
  rw [← Complex.exp_conj]
  congr 1
  rw [map_div₀, map_pow, map_sub, map_pow, Complex.conj_ofReal]
  congr 3
  simp [map_ofNat]

theorem ofReal_cpow_conj {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (r : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((r : ℂ) ^ s) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal]

theorem deriv_riemannZeta_conj_eq (s : ℂ) :
    deriv riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv riemannZeta s) := by
  have hfun : ((starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ)) = riemannZeta := by
    funext z; simp [riemannZeta_conj]
  have h := congrFun (deriv_conj_conj (f := riemannZeta)) ((starRingEnd ℂ) s)
  rw [hfun] at h
  simpa using h

theorem logDeriv_quot_conj (s : ℂ) :
    deriv riemannZeta ((starRingEnd ℂ) s) / riemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv riemannZeta s / riemannZeta s) := by
  rw [deriv_riemannZeta_conj_eq, riemannZeta_conj, map_div₀]

/-! ## Common bounds -/

theorem differentiable_gaussWeight (T : ℝ) : Differentiable ℂ (gaussWeight T) := by
  unfold gaussWeight; fun_prop

theorem differentiable_gW {T r : ℝ} (hr : 0 < r) : Differentiable ℂ (gW T r) := by
  unfold gW
  exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hr.ne'))).mul
    (differentiable_gaussWeight T)

theorem norm_ofReal_cpow_le {r : ℝ} (hr : 0 < r) {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 11 / 10) :
    ‖(r : ℂ) ^ s‖ ≤ r ^ (-1 / 2 : ℝ) + r ^ (11 / 10 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  rcases le_total 1 r with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    have : 0 ≤ r ^ (-1 / 2 : ℝ) := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hr h h1
    have : 0 ≤ r ^ (11 / 10 : ℝ) := by positivity
    linarith

/-- `|ζ'/ζ(11/10 + iy)| ≤ K`. -/
theorem exists_norm_logDeriv_rightEdge_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, ‖deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
      riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ K := by
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((11 / 10 : ℝ) : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun y => ?_⟩
  have hre : (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).re = 11 / 10 := by simp
  have h1 : 1 < (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).re := by rw [hre]; norm_num
  rw [show deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
      riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1]; ring, norm_neg]
  exact norm_LSeries_le_of_re hre (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))

/-- `|ζ'/ζ(−½ + iy)| ≤ C (1 + |y|)`. -/
theorem exists_norm_logDeriv_leftPt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)‖ ≤
      C * (1 + |y|) ^ 1 := by
  obtain ⟨CD, hCD0, hCD⟩ := exists_norm_logDeriv_zetaChi_leftPt_le
  obtain ⟨KΛ, hKΛ0, hKΛ⟩ := exists_norm_LSeries_one_sub_leftPt_le
    (f := fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  refine ⟨CD + KΛ, by positivity, fun y => ?_⟩
  rw [← logDeriv_apply, logDeriv_riemannZeta_eq_leftStrip (leftPt_mem_leftStrip y)]
  have hlog : Real.log (1 + |y|) ≤ |y| := by
    have := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg y] : (0 : ℝ) < 1 + |y|); linarith
  have h1 := hCD y
  have h2 := hKΛ y
  calc ‖logDeriv zetaChi (leftPt y) +
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt y)‖
      ≤ CD * (1 + Real.log (1 + |y|)) + KΛ := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ CD * (1 + |y|) + KΛ * (1 + |y|) := by
        gcongr
        exact le_mul_of_one_le_right hKΛ0 (by linarith [abs_nonneg y])
    _ = _ := by ring

theorem continuousAt_logDeriv_quot {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    ContinuousAt (fun z => deriv riemannZeta z / riemannZeta z) s :=
  (continuousAt_deriv_riemannZeta hs).div (differentiableAt_riemannZeta hs).continuousAt hz

theorem leftPt_ne_zero_zeta (y : ℝ) : riemannZeta (leftPt y) ≠ 0 :=
  riemannZeta_ne_zero_of_mem_leftStrip (leftPt_mem_leftStrip y)

theorem continuous_logDeriv_quot_leftPt :
    Continuous fun y => deriv riemannZeta (leftPt y) / riemannZeta (leftPt y) :=
  continuous_iff_continuousAt.mpr fun y =>
    (continuousAt_logDeriv_quot (leftPt_ne_one y) (leftPt_ne_zero_zeta y)).comp
      continuous_leftPt.continuousAt

theorem rightPt_ne_one (y : ℝ) : ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this; norm_num at this

theorem rightPt_ne_zero_zeta (y : ℝ) : riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)

theorem continuous_logDeriv_quot_rightPt :
    Continuous fun y : ℝ => deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
      riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) :=
  continuous_iff_continuousAt.mpr fun y =>
    ContinuousAt.comp (g := fun z => deriv riemannZeta z / riemannZeta z)
      (f := fun y : ℝ => ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)
      (continuousAt_logDeriv_quot (rightPt_ne_one y) (rightPt_ne_zero_zeta y))
      (by fun_prop : Continuous fun y : ℝ => ((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I).continuousAt

theorem bottomPt_ne_one (x : ℝ) : (x : ℂ) + bottomHeight * I ≠ 1 :=
  ne_one_of_im_pos (by simp; linarith [one_le_bottomHeight])

theorem continuousOn_bottom {h : ℂ → ℂ} (hh : ∀ x : ℝ, ContinuousAt h ((x : ℂ) + bottomHeight * I)) :
    ContinuousOn (fun x : ℝ => h ((x : ℂ) + bottomHeight * I) *
      (deriv riemannZeta ((x : ℂ) + bottomHeight * I) /
        riemannZeta ((x : ℂ) + bottomHeight * I))) (Icc (-1 / 2) (11 / 10)) := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hc : Continuous fun x : ℝ => (x : ℂ) + bottomHeight * I := by fun_prop
  refine (ContinuousAt.comp (g := h) (f := fun x : ℝ => (x : ℂ) + bottomHeight * I)
    (hh x) hc.continuousAt).mul
    (ContinuousAt.comp (g := fun z => deriv riemannZeta z / riemannZeta z)
      (f := fun x : ℝ => (x : ℂ) + bottomHeight * I)
      (continuousAt_logDeriv_quot (bottomPt_ne_one x) (riemannZeta_bottom_ne_zero x hx))
      hc.continuousAt)

theorem continuousOn_leftPiece {h : ℂ → ℂ} (hh : ∀ y, ContinuousAt h (leftPt y)) (t₀ : ℝ) :
    ContinuousOn (fun y : ℝ => h (leftPt y) *
      (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))) (Icc 0 t₀) := fun y _ =>
  ((hh y).comp continuous_leftPt.continuousAt).continuousWithinAt.mul
    continuous_logDeriv_quot_leftPt.continuousWithinAt

/-! ## The packaged edge estimate -/

/-- The `T`-independent part of the edge bound. -/
def edgeConst (Mb Ml Ch CL : ℝ) (k N : ℕ) : ℝ :=
  Mb + Ch * topConst * ((k + 2).factorial * Real.exp 1) * Real.exp 1 * (8 / 5) + Ml +
    CL * Real.exp 1 * (N.factorial * 2 ^ N * Real.exp (1 / 2)) * 2

theorem edgeConst_nonneg {Mb Ml Ch CL : ℝ} (k N : ℕ) (hMb : 0 ≤ Mb) (hMl : 0 ≤ Ml) (hCh : 0 ≤ Ch)
    (hCL : 0 ≤ CL) : 0 ≤ edgeConst Mb Ml Ch CL k N := by
  unfold edgeConst
  have ht := topConst_nonneg
  have h1 : 0 ≤ Ch * topConst * ((k + 2).factorial * Real.exp 1) * Real.exp 1 * (8 / 5) := by
    apply mul_nonneg _ (by norm_num)
    apply mul_nonneg _ (Real.exp_pos _).le
    apply mul_nonneg (mul_nonneg hCh ht) (by positivity)
  have h2 : 0 ≤ CL * Real.exp 1 * (N.factorial * 2 ^ N * Real.exp (1 / 2)) * 2 := by
    apply mul_nonneg _ (by norm_num)
    exact mul_nonneg (mul_nonneg hCL (Real.exp_pos _).le) (by positivity)
  linarith

/-- **All edges at once.**  For `H = h · g_T` with `h` holomorphic on `Im s > 0`, the real part of the
zero sum differs from `−(1/4π) Re ∫ F_L` by `O(T)`, given polynomial control of `h` on the edges. -/
theorem abs_re_zeroSum_add_le_edges {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h {s : ℂ | 0 < s.im})
    {Mb Ml Ch CR KR CL : ℝ} {k N : ℕ} (hCh : 0 ≤ Ch) (hCR : 0 ≤ CR) (hKR : 0 ≤ KR) (hCL : 0 ≤ CL)
    (hMb : ∀ T : ℝ, 1 ≤ T → ‖∫ x in (-1 / 2 : ℝ)..(11 / 10), (h ((x : ℂ) + bottomHeight * I) *
      gaussWeight T ((x : ℂ) + bottomHeight * I)) * (deriv riemannZeta ((x : ℂ) + bottomHeight * I) /
        riemannZeta ((x : ℂ) + bottomHeight * I))‖ ≤ Mb)
    (hMl : ∀ T : ℝ, 1 ≤ T → ‖∫ y in (0 : ℝ)..bottomHeight, (h (leftPt y) * gaussWeight T (leftPt y)) *
      (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤ Ml)
    (htop : ∀ Y : ℝ, 2 ≤ Y → ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), ‖h ((x : ℂ) + Y * I)‖ ≤ Ch * (1 + Y) ^ k)
    (hright : ∀ y : ℝ, ‖h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ CR)
    (hrightc : Continuous fun y : ℝ => h (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I))
    (hKRb : ∀ y : ℝ, ‖deriv riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I) /
      riemannZeta (((11 / 10 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ KR)
    (hleft : ∀ y : ℝ, ‖h (leftPt y) * (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))‖ ≤
      CL * (1 + |y|) ^ N)
    {T Y : ℝ} (hT : 2 ≤ T) (hY : GoodTop T Y)
    (hint : Integrable fun y : ℝ => (h (leftPt y) * gaussWeight T (leftPt y)) *
      (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)))
    (hconj : ∀ y : ℝ, (h (leftPt (-y)) * gaussWeight T (leftPt (-y))) *
      (deriv riemannZeta (leftPt (-y)) / riemannZeta (leftPt (-y))) =
      (starRingEnd ℂ) ((h (leftPt y) * gaussWeight T (leftPt y)) *
        (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y)))) :
    |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * (h w * gaussWeight T w)).re +
        (1 / (4 * Real.pi)) * (∫ y : ℝ, (h (leftPt y) * gaussWeight T (leftPt y)) *
          (deriv riemannZeta (leftPt y) / riemannZeta (leftPt y))).re| ≤
      (1 / (2 * Real.pi)) * (edgeConst Mb Ml Ch CL k N + CR * KR * Real.exp 1 * Real.sqrt Real.pi * T) := by
  have hT1 : 1 ≤ T := by linarith
  have hbY := hY.bottom_lt hT
  have hY2 : 2 ≤ Y := by have := hY.1.1; nlinarith
  have hHan : AnalyticOnNhd ℂ (fun s => h s * gaussWeight T s) {s : ℂ | 0 < s.im} := fun s hs =>
    (hh s hs).mul ((differentiable_gaussWeight T).analyticAt s)
  have hdec := abs_re_zeroSum_add_le hHan (by linarith [one_le_bottomHeight]) hbY
    riemannZeta_bottom_ne_zero hY.top_ne_zero hint hconj
  have hE : edgeConst Mb Ml Ch CL k N + CR * KR * Real.exp 1 * Real.sqrt Real.pi * T =
      Mb + Ch * topConst * ((k + 2).factorial * Real.exp 1) * Real.exp 1 * (8 / 5) +
        CR * KR * Real.exp 1 * Real.sqrt Real.pi * T + Ml +
        CL * Real.exp 1 * (N.factorial * 2 ^ N * Real.exp (1 / 2)) * 2 := by
    unfold edgeConst; ring
  rw [hE]
  refine hdec.trans ?_
  gcongr
  · exact hMb T hT1
  · exact top_edge_le hT1 hY.1.1 hCh topConst_nonneg (htop Y hY2) hY.logDeriv_le
  · refine (right_edge_le (h := h) hT1 hbY.le hCR hKR hright hKRb ?_).trans (le_of_eq (by ring))
    exact (hrightc.mul ((differentiable_gaussWeight T).continuous.comp (by fun_prop))).mul
      continuous_logDeriv_quot_rightPt
  · exact hMl T hT1
  · exact left_tail_le hT1 hY.1.1 hCL hleft

/-- `|a| ≤ ((A + B)/(2π) + Q) T L` from `|a + q| ≤ (A + BT)/(2π)` and `|q| ≤ Q T L`. -/
theorem abs_le_of_edge_bound {a q A B Q T L : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hL : 1 ≤ L) (h1 : |a + q| ≤ (1 / (2 * Real.pi)) * (A + B * T)) (h2 : |q| ≤ Q * T * L) :
    |a| ≤ ((A + B) / (2 * Real.pi) + Q) * T * L := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hTL : 1 ≤ T * L := by nlinarith
  have h3 : (1 / (2 * Real.pi)) * (A + B * T) ≤ (A + B) / (2 * Real.pi) * (T * L) := by
    rw [one_div_mul_eq_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]
    have h4 : B * T ≤ B * (T * L) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) hL) hB
    have h5 : A ≤ A * (T * L) := le_mul_of_one_le_right hA hTL
    linarith
  calc |a| = |(a + q) - q| := by ring_nf
    _ ≤ |a + q| + |q| := abs_sub _ _
    _ ≤ (A + B) / (2 * Real.pi) * (T * L) + Q * T * L := add_le_add (h1.trans h3) h2
    _ = _ := by ring

end

end RHTower.GaussZeroSum
