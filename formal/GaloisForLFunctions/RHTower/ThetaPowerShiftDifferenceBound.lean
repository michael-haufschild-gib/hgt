import GaloisForLFunctions.RHTower.ThetaPowerModularTwoSidedBound
import GaloisForLFunctions.RHTower.ThetaPowerHardyZeros

/-!
# The vertical shift difference of the theta-power family

For `0 < a < 1/2` the Hecke bound and the cusp decay combine to the envelope
`|F_a(ζ)| ≤ C₁ (Im ζ)^{-1/4} e^{-(πa/8) Im ζ}` on `ℍ`.  Cauchy's estimate on the disc of radius `Im w/2`
gives `|F_a'(w)| ≤ C₂ (Im w)^{-5/4} e^{-(πa/16) Im w}`, hence
`|F_a(τ) - F_a(τ+iδ)| ≤ C₂ δ (Im τ)^{-5/4} e^{-(πa/16) Im τ}`.  Interpolating with the trivial bound,

  `|F_a(τ) - F_a(τ+iδ)| ≤ K δ^η (Im τ)^{-1/4-η} e^{-(πa/16) Im τ}`   (`0 ≤ η ≤ 1`).
-/

open Complex Real Metric

namespace RHTower

noncomputable section

variable {a : ℝ}

/-- The envelope constant `C₁`. -/
def thetaPowerEnvelopeConstant (a : ℝ) : ℝ :=
  thetaPowerHeckeConstant a * Real.exp (π * a / 8) +
    thetaPowerCuspConstant a * (π * a / 8) ^ (-(1 / 4 : ℝ))

theorem thetaPowerCuspConstant_nonneg' (ha : 0 ≤ a) : 0 ≤ thetaPowerCuspConstant a := by
  have h := norm_thetaPowerForm_le_cusp ha (τ := Complex.I) (by simp)
  exact nonneg_of_mul_nonneg_left (le_trans (norm_nonneg _) h) (Real.exp_pos _)

/-- **Envelope** `|F_a(ζ)| ≤ C₁ (Im ζ)^{-1/4} e^{-(πa/8) Im ζ}`. -/
theorem norm_thetaPowerForm_le_envelope (ha0 : 0 < a) (ha1 : a < 1 / 2) {ζ : ℂ} (hζ : 0 < ζ.im) :
    ‖thetaPowerForm a ζ‖ ≤
      thetaPowerEnvelopeConstant a * ζ.im ^ (-(1 / 4 : ℝ)) * Real.exp (-(π * a / 8 * ζ.im)) := by
  have hCH : 0 < thetaPowerHeckeConstant a := by
    unfold thetaPowerHeckeConstant
    have hmin : 0 < min a (1 - 2 * a) := lt_min ha0 (by linarith)
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hCc := thetaPowerCuspConstant_nonneg' ha0.le
  have hc : 0 < π * a / 8 := by positivity
  have hq : 0 < ζ.im ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hζ _
  have hq4 : ζ.im ^ (1 / 4 : ℝ) * ζ.im ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hζ]; norm_num
  unfold thetaPowerEnvelopeConstant
  rcases le_total ζ.im 1 with h1 | h1
  · have hH := norm_thetaPowerForm_le_hecke ha0 ha1 hζ
    have he : 1 ≤ Real.exp (π * a / 8) * Real.exp (-(π * a / 8 * ζ.im)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    calc ‖thetaPowerForm a ζ‖ ≤ thetaPowerHeckeConstant a * ζ.im ^ (-(1 / 4 : ℝ)) := hH
      _ ≤ thetaPowerHeckeConstant a * ζ.im ^ (-(1 / 4 : ℝ)) *
            (Real.exp (π * a / 8) * Real.exp (-(π * a / 8 * ζ.im))) := le_mul_of_one_le_right (by positivity) he
      _ ≤ _ := by
          have : 0 ≤ thetaPowerCuspConstant a * (π * a / 8) ^ (-(1 / 4 : ℝ)) * ζ.im ^ (-(1 / 4 : ℝ)) *
              Real.exp (-(π * a / 8 * ζ.im)) := by positivity
          nlinarith
  · have hc4 := norm_thetaPowerForm_le_cusp ha0.le h1
    have hk := rpow_quarter_mul_exp_neg_le hc (le_of_lt hζ)
    have hsplit : Real.exp (-(π * a / 4) * ζ.im) =
        (ζ.im ^ (1 / 4 : ℝ) * Real.exp (-(π * a / 8 * ζ.im))) * ζ.im ^ (-(1 / 4 : ℝ)) *
          Real.exp (-(π * a / 8 * ζ.im)) := by
      have hre : (ζ.im ^ (1 / 4 : ℝ) * Real.exp (-(π * a / 8 * ζ.im))) * ζ.im ^ (-(1 / 4 : ℝ)) *
          Real.exp (-(π * a / 8 * ζ.im)) = (ζ.im ^ (1 / 4 : ℝ) * ζ.im ^ (-(1 / 4 : ℝ))) *
            (Real.exp (-(π * a / 8 * ζ.im)) * Real.exp (-(π * a / 8 * ζ.im))) := by ring
      rw [hre, hq4, one_mul, ← Real.exp_add]; congr 1; ring
    calc ‖thetaPowerForm a ζ‖ ≤ thetaPowerCuspConstant a * Real.exp (-(π * a / 4) * ζ.im) := hc4
      _ ≤ thetaPowerCuspConstant a * ((π * a / 8) ^ (-(1 / 4 : ℝ)) * ζ.im ^ (-(1 / 4 : ℝ)) *
            Real.exp (-(π * a / 8 * ζ.im))) := by
          rw [hsplit]; gcongr
      _ ≤ _ := by
          have : 0 ≤ thetaPowerHeckeConstant a * Real.exp (π * a / 8) * ζ.im ^ (-(1 / 4 : ℝ)) *
              Real.exp (-(π * a / 8 * ζ.im)) := by positivity
          nlinarith

theorem thetaPowerEnvelopeConstant_nonneg (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    0 ≤ thetaPowerEnvelopeConstant a := by
  have h := norm_thetaPowerForm_le_envelope ha0 ha1 (ζ := Complex.I) (by simp)
  have hpos : 0 < (Complex.I).im ^ (-(1 / 4 : ℝ)) * Real.exp (-(π * a / 8 * (Complex.I).im)) :=
    mul_pos (Real.rpow_pos_of_pos (by simp) _) (Real.exp_pos _)
  have := le_trans (norm_nonneg _) h
  rw [mul_assoc] at this
  exact nonneg_of_mul_nonneg_left this hpos

/-- **Cauchy estimate** `|F_a'(w)| ≤ 3 C₁ (Im w)^{-5/4} e^{-(πa/16) Im w}`. -/
theorem norm_deriv_thetaPowerForm_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {w : ℂ} (hw : 0 < w.im) :
    ‖deriv (thetaPowerForm a) w‖ ≤
      3 * thetaPowerEnvelopeConstant a * w.im ^ (-(5 / 4 : ℝ)) * Real.exp (-(π * a / 16 * w.im)) := by
  set r : ℝ := w.im / 2 with hr
  have hr0 : 0 < r := by positivity
  have hC1 := thetaPowerEnvelopeConstant_nonneg ha0 ha1
  have him_ge : ∀ ζ ∈ closedBall w r, r ≤ ζ.im := by
    intro ζ hζ
    have h := Complex.abs_im_le_norm (ζ - w)
    rw [mem_closedBall, dist_eq_norm] at hζ
    simp only [Complex.sub_im] at h
    have := (abs_le.mp (h.trans hζ)).1
    linarith
  have hdc : DiffContOnCl ℂ (thetaPowerForm a) (ball w r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball w hr0.ne']
    exact (differentiableOn_thetaPowerForm a).mono fun ζ hζ => by
      show 0 < ζ.im; linarith [him_ge ζ hζ]
  set Cs : ℝ := thetaPowerEnvelopeConstant a * r ^ (-(1 / 4 : ℝ)) * Real.exp (-(π * a / 8 * r))
  have hsphere : ∀ ζ ∈ sphere w r, ‖thetaPowerForm a ζ‖ ≤ Cs := by
    intro ζ hζ
    have hζr := him_ge ζ (sphere_subset_closedBall hζ)
    have hζ0 : 0 < ζ.im := by linarith
    refine (norm_thetaPowerForm_le_envelope ha0 ha1 hζ0).trans ?_
    have h1 : ζ.im ^ (-(1 / 4 : ℝ)) ≤ r ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hr0 hζr (by norm_num)
    have h2 : Real.exp (-(π * a / 8 * ζ.im)) ≤ Real.exp (-(π * a / 8 * r)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hζr (show 0 ≤ π * a / 8 by positivity)])
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC1) h2 (Real.exp_pos _).le
      (mul_nonneg hC1 (Real.rpow_nonneg hr0.le _))
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hdc hsphere
  refine hd.trans ?_
  · have hrr : r ^ (-(1 / 4 : ℝ)) / r = 2 ^ (5 / 4 : ℝ) * w.im ^ (-(5 / 4 : ℝ)) := by
      rw [hr, Real.div_rpow hw.le (by norm_num), div_div_eq_mul_div, Real.rpow_neg (by positivity),
        Real.rpow_neg hw.le, Real.rpow_neg (by norm_num)]
      have h54 : w.im ^ (5 / 4 : ℝ) = w.im ^ (1 / 4 : ℝ) * w.im := by
        rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add hw, Real.rpow_one]
      have h54' : (2 : ℝ) ^ (5 / 4 : ℝ) = 2 ^ (1 / 4 : ℝ) * 2 := by
        rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
      rw [h54, h54']
      have : 0 < w.im ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hw _
      have : 0 < (2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      field_simp
    have h254 : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 3 := by
      have h1 : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
      have h3 : (2 : ℝ) ^ (5 / 4 : ℝ) = 2 * 2 ^ (1 / 4 : ℝ) := by
        rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
      have h4 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 / 2 := by
        have h5 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        have h6 : 0 ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
        nlinarith [sq_nonneg ((2 : ℝ) ^ (1 / 4 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 4 : ℝ) - 3 / 2)]
      linarith
    have he : Real.exp (-(π * a / 8 * r)) = Real.exp (-(π * a / 16 * w.im)) := by
      congr 1; rw [hr]; ring
    calc Cs / r = thetaPowerEnvelopeConstant a * (r ^ (-(1 / 4 : ℝ)) / r) *
          Real.exp (-(π * a / 8 * r)) := by simp only [Cs]; ring
      _ = thetaPowerEnvelopeConstant a * (2 ^ (5 / 4 : ℝ) * w.im ^ (-(5 / 4 : ℝ))) *
          Real.exp (-(π * a / 16 * w.im)) := by rw [hrr, he]
      _ ≤ thetaPowerEnvelopeConstant a * (3 * w.im ^ (-(5 / 4 : ℝ))) *
          Real.exp (-(π * a / 16 * w.im)) := by
          gcongr
      _ = _ := by ring

/-- **Mean-value bound** `|F_a(τ+iδ) - F_a(τ)| ≤ 3 C₁ δ (Im τ)^{-5/4} e^{-(πa/16) Im τ}`. -/
theorem norm_thetaPowerForm_shift_sub_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ : ℝ} (hδ : 0 ≤ δ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ‖thetaPowerForm a (τ + δ * I) - thetaPowerForm a τ‖ ≤
      3 * thetaPowerEnvelopeConstant a * τ.im ^ (-(5 / 4 : ℝ)) * Real.exp (-(π * a / 16 * τ.im)) * δ := by
  set s : Set ℂ := segment ℝ τ (τ + δ * I) with hs
  have hC1 := thetaPowerEnvelopeConstant_nonneg ha0 ha1
  have him : ∀ x ∈ s, τ.im ≤ x.im := by
    intro x hx
    rw [hs, segment_eq_image] at hx
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hx
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.I_re, Complex.I_im, mul_one, mul_zero]
    nlinarith
  have hdiff : ∀ x ∈ s, DifferentiableAt ℂ (thetaPowerForm a) x := by
    intro x hx
    have hx0 : x ∈ modUpperSet := by show 0 < x.im; linarith [him x hx]
    exact (differentiableOn_thetaPowerForm a).differentiableAt (isOpen_modUpperSet.mem_nhds hx0)
  have hderiv : ∀ x ∈ s, ‖deriv (thetaPowerForm a) x‖ ≤
      3 * thetaPowerEnvelopeConstant a * τ.im ^ (-(5 / 4 : ℝ)) * Real.exp (-(π * a / 16 * τ.im)) := by
    intro x hx
    have hxi := him x hx
    have hx0 : 0 < x.im := by linarith
    refine (norm_deriv_thetaPowerForm_le ha0 ha1 hx0).trans ?_
    have h1 : x.im ^ (-(5 / 4 : ℝ)) ≤ τ.im ^ (-(5 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hτ hxi (by norm_num)
    have h2 : Real.exp (-(π * a / 16 * x.im)) ≤ Real.exp (-(π * a / 16 * τ.im)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hxi (show 0 ≤ π * a / 16 by positivity)])
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (Real.exp_pos _).le
      (mul_nonneg (by positivity) (Real.rpow_nonneg hτ.le _))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv (convex_segment _ _)
    (left_mem_segment ℝ τ (τ + δ * I)) (right_mem_segment ℝ τ (τ + δ * I))
  have hn : ‖τ + δ * I - τ‖ = δ := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hδ]
  rwa [hn] at h

/-- **Interpolated shift difference** `|F_a(τ) - F_a(τ+iδ)| ≤ 3 C₁ δ^η (Im τ)^{-1/4-η} e^{-(πa/16) Im τ}`. -/
theorem norm_thetaPowerForm_sub_shift_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) {δ : ℝ} (hδ : 0 < δ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaPowerForm a τ - thetaPowerForm a (τ + δ * I)‖ ≤
      3 * thetaPowerEnvelopeConstant a * δ ^ η * τ.im ^ (-(1 / 4 : ℝ) - η) *
        Real.exp (-(π * a / 16 * τ.im)) := by
  have hC1 := thetaPowerEnvelopeConstant_nonneg ha0 ha1
  set y := τ.im with hy
  have hE : Real.exp (-(π * a / 8 * y)) ≤ Real.exp (-(π * a / 16 * y)) :=
    Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ π * a / 16 * y by positivity])
  rcases le_total δ y with hδy | hδy
  · -- small shift: the mean-value bound
    have hmv := norm_thetaPowerForm_shift_sub_le ha0 ha1 hδ.le hτ
    rw [norm_sub_rev] at hmv
    refine hmv.trans ?_
    have hkey : y ^ (-(5 / 4 : ℝ)) * δ ≤ δ ^ η * y ^ (-(1 / 4 : ℝ) - η) := by
      have h1 : δ = δ ^ η * δ ^ (1 - η) := by
        rw [← Real.rpow_add hδ, show η + (1 - η) = 1 by ring, Real.rpow_one]
      have h2 : y ^ (-(5 / 4 : ℝ)) = y ^ (-(1 / 4 : ℝ) - η) * y ^ (η - 1) := by
        rw [← Real.rpow_add hτ]; congr 1; ring
      have h3 : δ ^ (1 - η) * y ^ (η - 1) ≤ 1 := by
        rw [show η - 1 = -(1 - η) by ring, Real.rpow_neg hτ.le, ← div_eq_mul_inv,
          div_le_one (Real.rpow_pos_of_pos hτ _)]
        exact Real.rpow_le_rpow hδ.le hδy (by linarith)
      have hA : 0 ≤ δ ^ η * y ^ (-(1 / 4 : ℝ) - η) :=
        mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hτ.le _)
      calc y ^ (-(5 / 4 : ℝ)) * δ
          = (y ^ (-(1 / 4 : ℝ) - η) * y ^ (η - 1)) * (δ ^ η * δ ^ (1 - η)) := by rw [← h2, ← h1]
        _ = (δ ^ η * y ^ (-(1 / 4 : ℝ) - η)) * (δ ^ (1 - η) * y ^ (η - 1)) := by ring
        _ ≤ (δ ^ η * y ^ (-(1 / 4 : ℝ) - η)) * 1 := mul_le_mul_of_nonneg_left h3 hA
        _ = δ ^ η * y ^ (-(1 / 4 : ℝ) - η) := mul_one _
    calc 3 * thetaPowerEnvelopeConstant a * y ^ (-(5 / 4 : ℝ)) * Real.exp (-(π * a / 16 * y)) * δ
        = 3 * thetaPowerEnvelopeConstant a * (y ^ (-(5 / 4 : ℝ)) * δ) * Real.exp (-(π * a / 16 * y)) := by ring
      _ ≤ 3 * thetaPowerEnvelopeConstant a * (δ ^ η * y ^ (-(1 / 4 : ℝ) - η)) *
            Real.exp (-(π * a / 16 * y)) := by gcongr
      _ = _ := by ring
  · -- large shift: the trivial bound
    have hτ2 : 0 < (τ + δ * I).im := by simp; linarith
    have h1 := norm_thetaPowerForm_le_envelope ha0 ha1 hτ
    have h2 := norm_thetaPowerForm_le_envelope ha0 ha1 hτ2
    have hy2 : (τ + δ * I).im = y + δ := by simp [hy]
    rw [hy2] at h2
    have h2' : ‖thetaPowerForm a (τ + δ * I)‖ ≤
        thetaPowerEnvelopeConstant a * y ^ (-(1 / 4 : ℝ)) * Real.exp (-(π * a / 8 * y)) := by
      refine h2.trans ?_
      have ha : (y + δ) ^ (-(1 / 4 : ℝ)) ≤ y ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by norm_num)
      have hb : Real.exp (-(π * a / 8 * (y + δ))) ≤ Real.exp (-(π * a / 8 * y)) :=
        Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ π * a / 8 * δ by positivity])
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha hC1) hb (Real.exp_pos _).le
        (mul_nonneg hC1 (Real.rpow_nonneg hτ.le _))
    have hkey : y ^ (-(1 / 4 : ℝ)) ≤ δ ^ η * y ^ (-(1 / 4 : ℝ) - η) := by
      have h3 : y ^ (-(1 / 4 : ℝ)) = y ^ η * y ^ (-(1 / 4 : ℝ) - η) := by
        rw [← Real.rpow_add hτ]; congr 1; ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hτ.le hδy hη0) (Real.rpow_nonneg hτ.le _)
    calc ‖thetaPowerForm a τ - thetaPowerForm a (τ + δ * I)‖
        ≤ ‖thetaPowerForm a τ‖ + ‖thetaPowerForm a (τ + δ * I)‖ := norm_sub_le _ _
      _ ≤ 2 * (thetaPowerEnvelopeConstant a * y ^ (-(1 / 4 : ℝ)) * Real.exp (-(π * a / 8 * y))) := by
          linarith
      _ ≤ 2 * (thetaPowerEnvelopeConstant a * (δ ^ η * y ^ (-(1 / 4 : ℝ) - η)) *
            Real.exp (-(π * a / 16 * y))) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ thetaPowerEnvelopeConstant a * δ ^ η * y ^ (-(1 / 4 : ℝ) - η) *
              Real.exp (-(π * a / 16 * y)) :=
            mul_nonneg (mul_nonneg (mul_nonneg hC1 (Real.rpow_nonneg hδ.le _))
              (Real.rpow_nonneg hτ.le _)) (Real.exp_pos _).le
          nlinarith

end

end RHTower
