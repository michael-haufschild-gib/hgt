import GaloisForLFunctions.RHTower.ThetaCuspChargeWindowLaw

open Complex
open scoped Real

namespace RHTower

noncomputable section

/-! ### The saddle line `Im z = -β` with parameter `a = t²` -/

/-- `b = cos(η/2) = √(1-a²)` with `a = t²`. -/
def chB (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 4)

/-- `θ = η/2 = arcsin a`. -/
def chTheta (t : ℝ) : ℝ := Real.arcsin (t ^ 2)

/-- Height of the saddle line: `β = π/4 - θ`. -/
def chBeta (t : ℝ) : ℝ := π / 4 - chTheta t

/-- `ω = e^{iη} = (1-2a²) + 2ab·i`. -/
def chOmega (t : ℝ) : ℂ := ⟨1 - 2 * t ^ 4, 2 * t ^ 2 * chB t⟩

/-- The saddle frequency `u = 7π/(8a²)`. -/
def chU (t : ℝ) : ℝ := 7 * π / (8 * t ^ 4)

/-- The saddle height `R₀ = (7π/8)cot(η/2) = 7πb/(8a)`. -/
def chR0 (t : ℝ) : ℝ := 7 * π * chB t / (8 * t ^ 2)

/-- `w(s) = e^{2s}ω - 1`, the displacement from the pole cusp `1`. -/
def chW (t s : ℝ) : ℂ := (Real.exp (2 * s) : ℂ) * chOmega t - 1

/-- The inverted variable `v = -1/w`. -/
def chV (t s : ℝ) : ℂ := -1 / chW t s

/-- `|w|² = (ρ-1)² + 4a²ρ`, `ρ = e^{2s}`. -/
def chD (t s : ℝ) : ℝ := (Real.exp (2 * s) - 1) ^ 2 + 4 * t ^ 4 * Real.exp (2 * s)

/-- `σ = e^s - e^{-s} = 2 sinh s`. -/
def chSigma (s : ℝ) : ℝ := Real.exp s - Real.exp (-s)

/-- `κ = e^s + e^{-s} = 2 cosh s`. -/
def chKappa (s : ℝ) : ℝ := Real.exp s + Real.exp (-s)

/-- The phase function of the saddle integrand. -/
def chPsi (t s : ℝ) : ℂ := -(7 * π * Complex.I * chV t s / 4) - Complex.I * chU t * s

section Geometry

variable {t : ℝ}

theorem chB_sq (ht : t ^ 4 ≤ 1) : chB t ^ 2 = 1 - t ^ 4 := by
  unfold chB; rw [Real.sq_sqrt (by linarith)]

theorem chB_nonneg : 0 ≤ chB t := Real.sqrt_nonneg _

theorem chB_le_one : chB t ≤ 1 := by
  unfold chB; rw [Real.sqrt_le_one]; nlinarith [pow_two_nonneg (t ^ 2)]

theorem half_le_chB (ht : t ^ 4 ≤ 3 / 4) : 1 / 2 ≤ chB t := by
  unfold chB; rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith

theorem sin_chTheta (ht : t ^ 2 ≤ 1) : Real.sin (chTheta t) = t ^ 2 := by
  unfold chTheta; exact Real.sin_arcsin (by nlinarith [sq_nonneg t]) ht

theorem cos_chTheta : Real.cos (chTheta t) = chB t := by
  unfold chTheta chB; rw [Real.cos_arcsin]; ring_nf

theorem chTheta_nonneg : 0 ≤ chTheta t := by
  unfold chTheta; exact Real.arcsin_nonneg.mpr (sq_nonneg t)

theorem chTheta_le : chTheta t ≤ π / 2 := Real.arcsin_le_pi_div_two _

theorem cos_two_chBeta (ht : t ^ 2 ≤ 1) : Real.cos (2 * chBeta t) = 2 * t ^ 2 * chB t := by
  unfold chBeta
  rw [show 2 * (π / 4 - chTheta t) = π / 2 - 2 * chTheta t by ring, Real.cos_pi_div_two_sub,
    Real.sin_two_mul, sin_chTheta ht, cos_chTheta]

theorem sin_two_chBeta (ht : t ^ 2 ≤ 1) : Real.sin (2 * chBeta t) = 1 - 2 * t ^ 4 := by
  unfold chBeta
  rw [show 2 * (π / 4 - chTheta t) = π / 2 - 2 * chTheta t by ring, Real.sin_pi_div_two_sub,
    Real.cos_two_mul, cos_chTheta]
  have h := Real.sin_sq_add_cos_sq (chTheta t)
  rw [sin_chTheta ht, cos_chTheta] at h
  nlinarith

theorem chBeta_nonneg (ht : t ^ 2 ≤ 1 / 2) : 0 ≤ chBeta t := by
  unfold chBeta chTheta
  have h1 : Real.arcsin (t ^ 2) ≤ π / 4 := by
    rw [Real.arcsin_le_iff_le_sin (by constructor <;> nlinarith [sq_nonneg t])
      (by constructor <;> linarith [Real.pi_pos])]
    rw [Real.sin_pi_div_four]
    have : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  linarith

theorem chBeta_lt (ht : 0 < t) (ht1 : t ^ 2 ≤ 1) : chBeta t < π / 4 := by
  unfold chBeta chTheta
  have : 0 < Real.arcsin (t ^ 2) := Real.arcsin_pos.mpr (by positivity)
  linarith

/-- **The saddle line is the ray of angle `η`.** -/
theorem I_mul_cexp_line (ht : t ^ 2 ≤ 1) (s : ℝ) :
    Complex.I * Complex.exp (2 * ((s : ℂ) - (chBeta t : ℂ) * Complex.I)) =
      (Real.exp (2 * s) : ℂ) * chOmega t := by
  have h1 : 2 * ((s : ℂ) - (chBeta t : ℂ) * Complex.I) =
      ((2 * s : ℝ) : ℂ) + ((-(2 * chBeta t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    cos_two_chBeta ht, sin_two_chBeta ht]
  have hom : chOmega t = ((1 - 2 * t ^ 4 : ℝ) : ℂ) + ((2 * t ^ 2 * chB t : ℝ) : ℂ) * Complex.I :=
    Complex.mk_eq_add_mul_I _ _
  rw [hom]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  linear_combination (-(Real.exp (2 * s) : ℂ) * (1 - 2 * (t : ℂ) ^ 4)) * Complex.I_sq

theorem chW_re (s : ℝ) : (chW t s).re = Real.exp (2 * s) * (1 - 2 * t ^ 4) - 1 := by
  simp [chW, chOmega, -Complex.ofReal_exp]

theorem chW_im (s : ℝ) : (chW t s).im = Real.exp (2 * s) * (2 * t ^ 2 * chB t) := by
  simp [chW, chOmega, -Complex.ofReal_exp]

theorem normSq_chW (ht : t ^ 4 ≤ 1) (s : ℝ) : Complex.normSq (chW t s) = chD t s := by
  rw [Complex.normSq_apply, chW_re, chW_im, chD]
  have hb := chB_sq ht
  linear_combination (Real.exp (2 * s) ^ 2 * (4 * t ^ 4)) * hb

theorem chSigma_sq_mul (s : ℝ) :
    Real.exp (2 * s) * chSigma s ^ 2 = (Real.exp (2 * s) - 1) ^ 2 := by
  unfold chSigma
  have h1 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (2 * s) = Real.exp s * Real.exp s := by rw [← Real.exp_add]; ring_nf
  rw [h2]
  linear_combination (-2 * Real.exp s * Real.exp s + Real.exp s * Real.exp (-s) + 1) * h1

theorem chD_eq (s : ℝ) : chD t s = Real.exp (2 * s) * (chSigma s ^ 2 + 4 * t ^ 4) := by
  rw [chD, ← chSigma_sq_mul]; ring

theorem chD_pos (ht : 0 < t) (s : ℝ) : 0 < chD t s := by
  rw [chD_eq]; positivity

theorem chW_ne_zero (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) : chW t s ≠ 0 := by
  intro h
  have := normSq_chW ht4 s
  rw [h, Complex.normSq_zero] at this
  exact (chD_pos ht s).ne' this.symm

theorem chV_im (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    (chV t s).im = 2 * t ^ 2 * chB t / (chSigma s ^ 2 + 4 * t ^ 4) := by
  unfold chV
  rw [Complex.div_im, normSq_chW ht4, chW_re, chW_im, chD_eq]
  have hE := Real.exp_pos (2 * s)
  have hq : 0 < chSigma s ^ 2 + 4 * t ^ 4 := by positivity
  simp
  try field_simp

theorem chV_re (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    (chV t s).re = (1 - Real.exp (2 * s) * (1 - 2 * t ^ 4)) / chD t s := by
  unfold chV
  rw [Complex.div_re, normSq_chW ht4, chW_re, chW_im]
  simp
  try ring

theorem chV_im_pos (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (hb : 0 < chB t) (s : ℝ) :
    0 < (chV t s).im := by
  rw [chV_im ht ht4]; positivity

theorem one_add_neg_one_div_chV (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    1 + -1 / chV t s = (Real.exp (2 * s) : ℂ) * chOmega t := by
  have hw := chW_ne_zero ht ht4 s
  have h : -1 / chV t s = chW t s := by unfold chV; field_simp
  rw [h]; unfold chW; ring

theorem chPsi_re (s : ℝ) : (chPsi t s).re = 7 * π / 4 * (chV t s).im := by
  simp [chPsi, Complex.mul_re, Complex.mul_im]; ring

theorem chPsi_im (s : ℝ) : (chPsi t s).im = -(7 * π / 4 * (chV t s).re) - chU t * s := by
  simp [chPsi, Complex.mul_re, Complex.mul_im]; ring

/-- **Height defect of the saddle integrand.** -/
theorem chR0_sub_psi_re (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    chR0 t - (chPsi t s).re =
      7 * π * chB t * chSigma s ^ 2 / (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) := by
  rw [chPsi_re, chV_im ht ht4, chR0]
  have hq : 0 < chSigma s ^ 2 + 4 * t ^ 4 := by positivity
  field_simp
  ring

/-- **Phase defect of the saddle integrand.** -/
theorem chPsi_im_add (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    (chPsi t s).im + 7 * π / 8 =
      7 * π / 8 * (t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2) /
        (t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4)) := by
  rw [chPsi_im, chV_re ht ht4, chU, chD_eq]
  have hq : 0 < chSigma s ^ 2 + 4 * t ^ 4 := by positivity
  have hE : 0 < Real.exp (2 * s) := Real.exp_pos _
  have hsk : chSigma s * chKappa s = Real.exp (2 * s) - Real.exp (-(2 * s)) := by
    unfold chSigma chKappa
    have h1 : Real.exp s * Real.exp s = Real.exp (2 * s) := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-s) * Real.exp (-s) = Real.exp (-(2 * s)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination h1 - h2
  have hinv : Real.exp (2 * s) * Real.exp (-(2 * s)) = 1 := by rw [← Real.exp_add]; simp
  have hsig := chSigma_sq_mul s
  rw [hsk]
  field_simp
  linear_combination (4 * t ^ 4) * hsig + (4 * t ^ 4) * hinv

end Geometry

/-! ### Elementary hyperbolic estimates -/

theorem abs_exp_sub_quadratic_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ 2 / 9 * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  calc |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * (4 / (6 * 3)) := h
    _ = 2 / 9 * |x| ^ 3 := by ring

theorem abs_exp_sub_exp_neg_sub_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - Real.exp (-x) - 2 * x| ≤ 4 / 9 * |x| ^ 3 := by
  have h1 := abs_exp_sub_quadratic_le hx
  have h2 := abs_exp_sub_quadratic_le (x := -x) (by rwa [abs_neg])
  rw [abs_neg] at h2
  have e : Real.exp x - Real.exp (-x) - 2 * x =
      (Real.exp x - (1 + x + x ^ 2 / 2)) - (Real.exp (-x) - (1 + -x + (-x) ^ 2 / 2)) := by ring
  rw [e]
  calc _ ≤ |Real.exp x - (1 + x + x ^ 2 / 2)| + |Real.exp (-x) - (1 + -x + (-x) ^ 2 / 2)| :=
        abs_sub _ _
    _ ≤ 4 / 9 * |x| ^ 3 := by linarith

theorem abs_chSigma_le {s : ℝ} (hs : |s| ≤ 1) : |chSigma s| ≤ 3 * |s| := by
  have h := abs_exp_sub_exp_neg_sub_le hs
  have hs3 : |s| ^ 3 ≤ |s| := by
    have := abs_nonneg s
    nlinarith [pow_le_one₀ this hs (n := 2)]
  unfold chSigma
  calc |Real.exp s - Real.exp (-s)| = |(Real.exp s - Real.exp (-s) - 2 * s) + 2 * s| := by ring_nf
    _ ≤ |Real.exp s - Real.exp (-s) - 2 * s| + |2 * s| := abs_add_le _ _
    _ ≤ 4 / 9 * |s| + 2 * |s| := by rw [abs_mul, abs_two]; nlinarith
    _ ≤ 3 * |s| := by nlinarith [abs_nonneg s]

theorem two_abs_le_abs_chSigma (s : ℝ) : 2 * |s| ≤ |chSigma s| := by
  have h : chSigma s = 2 * Real.sinh s := by unfold chSigma; rw [Real.sinh_eq]; ring
  rw [h, abs_mul, abs_two, Real.abs_sinh]
  have := Real.self_le_sinh_iff.mpr (abs_nonneg s)
  linarith

theorem abs_chSigma_mul_chKappa_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |chSigma s * chKappa s - 4 * s| ≤ 4 * |s| ^ 3 := by
  have h2s : |2 * s| ≤ 1 := by rw [abs_mul, abs_two]; linarith
  have h := abs_exp_sub_exp_neg_sub_le h2s
  have e : chSigma s * chKappa s = Real.exp (2 * s) - Real.exp (-(2 * s)) := by
    unfold chSigma chKappa
    have h1 : Real.exp s * Real.exp s = Real.exp (2 * s) := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-s) * Real.exp (-s) = Real.exp (-(2 * s)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination h1 - h2
  rw [e, show 4 * s = 2 * (2 * s) by ring]
  refine le_trans h ?_
  rw [abs_mul, abs_two]; nlinarith [pow_nonneg (abs_nonneg s) 3]

/-! ### Window estimates -/

section Window

variable {t : ℝ}

theorem chR0_sub_psi_re_nonneg (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    0 ≤ chR0 t - (chPsi t s).re := by
  rw [chR0_sub_psi_re ht ht4]
  have := chB_nonneg (t := t)
  positivity

theorem chR0_sub_psi_re_le_inner (ht : 0 < t) (ht1 : t ≤ 1) {s : ℝ} (hs : |s| ≤ t ^ 3 / 4) :
    chR0 t - (chPsi t s).re ≤ 1 / 2 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have hs1 : |s| ≤ 1 := by
    have : t ^ 3 ≤ 1 := pow_le_one₀ ht.le ht1
    linarith
  rw [chR0_sub_psi_re ht ht4]
  have hb1 := chB_le_one (t := t)
  have hb0 := chB_nonneg (t := t)
  have hσ := abs_chSigma_le hs1
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ t ^ 6 / 16 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this; nlinarith
  have ht0 : 0 < t ^ 2 := by positivity
  have hq : 4 * t ^ 4 ≤ chSigma s ^ 2 + 4 * t ^ 4 := by nlinarith [sq_nonneg (chSigma s)]
  rw [div_le_iff₀ (by positivity)]
  have hπ := Real.pi_lt_four
  calc 7 * π * chB t * chSigma s ^ 2 ≤ 7 * π * 1 * (9 * (t ^ 6 / 16)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by positivity))
          (le_trans hσ2 (by nlinarith)) (sq_nonneg _) (by positivity)
    _ ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := by nlinarith [pow_pos ht 6]
    _ ≤ 1 / 2 * (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) := by gcongr

theorem chR0_sub_psi_re_ge_mid (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 4) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    s ^ 2 / (4 * t ^ 6) ≤ chR0 t - (chPsi t s).re := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have hb := half_le_chB (t := t) (by nlinarith)
  rw [chR0_sub_psi_re ht ht4]
  have hσ := two_abs_le_abs_chSigma s
  have hσ2 : 4 * s ^ 2 ≤ chSigma s ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hσ 2
    rw [mul_pow, sq_abs, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ 4 * t ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this; nlinarith
  have ht2p : 0 < t ^ 2 := by positivity
  have hX : s ^ 2 / (s ^ 2 + t ^ 4) ≤ chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg s, pow_pos ht 4]
  have hY : s ^ 2 / (5 * t ^ 4) ≤ s ^ 2 / (s ^ 2 + t ^ 4) := by
    rcases eq_or_lt_of_le (sq_nonneg s) with h0 | h0
    · rw [← h0]; simp
    · exact div_le_div_of_nonneg_left h0.le (by positivity) (by linarith)
  have hπ := Real.pi_gt_three
  have hmain : 7 * π * chB t * chSigma s ^ 2 / (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) =
      7 * π * chB t / (8 * t ^ 2) * (chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4)) := by
    field_simp
  rw [hmain]
  calc s ^ 2 / (4 * t ^ 6) ≤ 7 * π * (1 / 2) / (8 * t ^ 2) * (s ^ 2 / (5 * t ^ 4)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hπ.le) (mul_nonneg (sq_nonneg s) (pow_pos ht 6).le)]
    _ ≤ 7 * π * chB t / (8 * t ^ 2) * (chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4)) := by
        apply mul_le_mul _ (le_trans hY hX) (by positivity) (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith

theorem abs_chPhi_le (ht : 0 < t) (ht1 : t ≤ 1) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(chPsi t s).im + 7 * π / 8| ≤ 10 * |s| ^ 3 / t ^ 8 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  rw [chPsi_im_add ht ht4]
  have hsk := abs_chSigma_mul_chKappa_sub_le hs
  have hσ := abs_chSigma_le (s := s) (by linarith)
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have ht8 : 0 < t ^ 8 := by positivity
  have hden : 4 * t ^ 8 ≤ t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4) := by
    nlinarith [sq_nonneg (chSigma s), pow_pos ht 4]
  have hnum : |t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2| ≤ 13 * |s| ^ 3 := by
    calc _ ≤ |t ^ 4 * (chSigma s * chKappa s - 4 * s)| + |s * chSigma s ^ 2| := abs_sub _ _
      _ = t ^ 4 * |chSigma s * chKappa s - 4 * s| + |s| * chSigma s ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 4),
            abs_of_nonneg (sq_nonneg (chSigma s))]
      _ ≤ 1 * (4 * |s| ^ 3) + |s| * (9 * s ^ 2) := by
          gcongr
      _ = 13 * |s| ^ 3 := by rw [← sq_abs s]; ring
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 7 * π / 8),
    abs_of_pos (by positivity : (0:ℝ) < t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4))]
  rw [div_le_div_iff₀ (by positivity) ht8]
  have hπ := Real.pi_lt_d2
  calc 7 * π / 8 * |t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2| * t ^ 8
      ≤ 7 * π / 8 * (13 * |s| ^ 3) * t ^ 8 := by gcongr
    _ ≤ 10 * |s| ^ 3 * (4 * t ^ 8) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hπ.le)
          (mul_nonneg (pow_nonneg (abs_nonneg s) 3) ht8.le)]
    _ ≤ 10 * |s| ^ 3 * (t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4)) := by gcongr

theorem four_le_chV_im (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 160) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    4 ≤ (chV t s).im := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have hb := half_le_chB (t := t) (by nlinarith)
  rw [chV_im ht ht4]
  have hσ := abs_chSigma_le (s := s) (by nlinarith)
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ 4 * t ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this; nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [pow_pos ht 2, pow_pos ht 4]

end Window

/-! ### The half-power amplitude and the exact factorization -/

/-- The half-power amplitude `P(s) = (-iv)^{1/2}`. -/
def chP (t s : ℝ) : ℂ := (-Complex.I * chV t s) ^ (1 / 2 : ℂ)

/-- `|P(0)| = (2a)^{-1/2}`. -/
def chP0 (t : ℝ) : ℝ := Real.exp (Real.log (1 / (2 * t ^ 2)) / 2)

/-- The normalized amplitude `A(s) = e^{s/2}P(s)/P(0)`. -/
def chA (t s : ℝ) : ℂ :=
  (Real.exp (s / 2) : ℂ) * chP t s * ((chP0 t : ℂ)⁻¹ * Complex.exp (Complex.I * (chTheta t / 2 : ℝ)))

/-- The saddle size `g₀ = 2⁻⁸(2a)^{-1/2}e^{R₀}`. -/
def chG0 (t : ℝ) : ℝ := (2 ^ 8)⁻¹ * chP0 t * Real.exp (chR0 t)

/-- The shifted-line integrand of the charge transform. -/
def chLine (t s : ℝ) : ℂ :=
  Complex.exp (-Complex.I * chU t * s) *
    chargeTailC (thetaGroupBasis 1) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)

section Amplitude

variable {t : ℝ}

theorem chP0_pos : 0 < chP0 t := Real.exp_pos _

theorem chP0_sq (ht : 0 < t) : chP0 t ^ 2 = 1 / (2 * t ^ 2) := by
  unfold chP0
  rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (Real.log (1 / (2 * t ^ 2)) / 2) =
    Real.log (1 / (2 * t ^ 2)) by push_cast; ring, Real.exp_log (by positivity)]

theorem re_cpow_half_nonneg (x : ℂ) : 0 ≤ (x ^ (1 / 2 : ℂ)).re := by
  by_cases hx : x = 0
  · rw [hx, Complex.zero_cpow (by norm_num)]; simp
  rw [Complex.cpow_def_of_ne_zero hx, Complex.exp_re]
  apply mul_nonneg (Real.exp_pos _).le
  have him : (Complex.log x * (1 / 2)).im = x.arg / 2 := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re]; simp [div_eq_mul_inv]
  rw [him]
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have := Complex.neg_pi_lt_arg x; linarith
  · have := Complex.arg_le_pi x; linarith

theorem chP_sq (s : ℝ) : chP t s ^ 2 = -Complex.I * chV t s := by
  unfold chP; rw [one_div]; exact Complex.cpow_ofNat_inv_pow _ 2

theorem norm_chP_sq (s : ℝ) : ‖chP t s‖ ^ 2 = ‖chV t s‖ := by
  rw [← norm_pow, chP_sq]; simp

theorem norm_chW_sq (ht4 : t ^ 4 ≤ 1) (s : ℝ) : ‖chW t s‖ ^ 2 = chD t s := by
  rw [Complex.sq_norm, normSq_chW ht4]

theorem norm_chV (s : ℝ) : ‖chV t s‖ = 1 / ‖chW t s‖ := by
  unfold chV; rw [norm_div, norm_neg, norm_one]

theorem le_norm_chW (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    2 * t ^ 2 * Real.exp s ≤ ‖chW t s‖ := by
  rw [Complex.norm_def, normSq_chW ht4, Real.le_sqrt (by positivity) (chD_pos ht s).le, chD]
  have h : Real.exp (2 * s) = Real.exp s ^ 2 := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [h]; nlinarith [sq_nonneg (Real.exp s ^ 2 - 1), pow_pos ht 4, Real.exp_pos s]

theorem norm_chA_le_one (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) : ‖chA t s‖ ≤ 1 := by
  have hw := le_norm_chW ht ht4 s
  have hwpos : 0 < ‖chW t s‖ := lt_of_lt_of_le (by positivity) hw
  have hsq : ‖chA t s‖ ^ 2 ≤ 1 := by
    unfold chA
    rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos chP0_pos, Complex.norm_exp]
    have him : (Complex.I * ((chTheta t / 2 : ℝ) : ℂ)).re = 0 := by simp
    rw [him, Real.exp_zero, mul_one]
    rw [mul_pow, mul_pow, inv_pow, norm_chP_sq, chP0_sq ht, norm_chV]
    have he : Real.exp (s / 2) ^ 2 = Real.exp s := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [he]
    rw [show Real.exp s * (1 / ‖chW t s‖) * (1 / (2 * t ^ 2))⁻¹ =
      Real.exp s * (2 * t ^ 2) / ‖chW t s‖ by field_simp]
    rw [div_le_one hwpos]; linarith
  nlinarith [norm_nonneg (chA t s)]

/-- `-iv(0) = (2a)⁻¹e^{-iθ}`. -/
theorem neg_I_mul_chV_zero (ht : 0 < t) (ht2 : t ^ 2 ≤ 1) :
    -Complex.I * chV t 0 = ((1 / (2 * t ^ 2) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (chTheta t : ℝ)) := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have hw := chW_ne_zero ht ht4 0
  have hexp : Complex.exp (-Complex.I * (chTheta t : ℝ)) =
      (chB t : ℂ) - ((t ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [show -Complex.I * ((chTheta t : ℝ) : ℂ) = ((-chTheta t : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, cos_chTheta, sin_chTheta ht2]
    push_cast; ring
  rw [hexp]
  have hW : chW t 0 = ((-2 * t ^ 4 : ℝ) : ℂ) + ((2 * t ^ 2 * chB t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [chW_re]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Real.exp_zero]
      ring
    · rw [chW_im]
      simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, add_zero, zero_add, mul_one, Real.exp_zero]
      ring
  have hb := chB_sq ht4
  have hbC : (chB t : ℂ) ^ 2 = 1 - (t : ℂ) ^ 4 := by exact_mod_cast hb
  have hprod : ((chB t : ℂ) - (t : ℂ) ^ 2 * Complex.I) *
      (-2 * (t : ℂ) ^ 4 + 2 * (t : ℂ) ^ 2 * chB t * Complex.I) = 2 * (t : ℂ) ^ 2 * Complex.I := by
    linear_combination (2 * (t : ℂ) ^ 2 * Complex.I) * hbC +
      (-2 * (t : ℂ) ^ 4 * chB t) * Complex.I_sq
  have ht2' : (2 * (t : ℂ) ^ 2) ≠ 0 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this)
  unfold chV
  rw [show -Complex.I * (-1 / chW t 0) = Complex.I / chW t 0 by ring, div_eq_iff hw, hW]
  calc Complex.I = (2 * (t : ℂ) ^ 2)⁻¹ * (2 * (t : ℂ) ^ 2 * Complex.I) :=
        (inv_mul_cancel_left₀ ht2' _).symm
    _ = _ := by rw [← hprod]; push_cast; ring

/-- **The amplitude at the saddle:** `P(0) = (2a)^{-1/2}e^{-iθ/2}`. -/
theorem chP_zero (ht : 0 < t) (ht2 : t ^ 2 ≤ 1) :
    chP t 0 = (chP0 t : ℂ) * Complex.exp (-Complex.I * (chTheta t / 2 : ℝ)) := by
  unfold chP
  rw [neg_I_mul_chV_zero ht ht2]
  have hr : 0 < 1 / (2 * t ^ 2) := by positivity
  have hne : ((1 / (2 * t ^ 2) : ℝ) : ℂ) * Complex.exp (-Complex.I * (chTheta t : ℝ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log_ofReal_mul hr (Complex.exp_ne_zero _),
    Complex.log_exp]
  · unfold chP0
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  · have h1 := chTheta_le (t := t); have h0 := chTheta_nonneg (t := t)
    simp; linarith [Real.pi_pos]
  · have h0 := chTheta_nonneg (t := t)
    simp; linarith [Real.pi_pos]


theorem norm_chOmega (ht4 : t ^ 4 ≤ 1) : ‖chOmega t‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [chOmega]
  have hb := chB_sq ht4
  rw [show (1 - 2 * t ^ 4) * (1 - 2 * t ^ 4) + 2 * t ^ 2 * chB t * (2 * t ^ 2 * chB t) = 1 by
    linear_combination (4 * t ^ 4) * hb]
  simp

theorem norm_chW_zero (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) : ‖chW t 0‖ = 2 * t ^ 2 := by
  rw [Complex.norm_def, normSq_chW ht4, chD]
  simp only [mul_zero, Real.exp_zero, sub_self]
  rw [show (0 : ℝ) ^ 2 + 4 * t ^ 4 * 1 = (2 * t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem norm_chV_sub_chV_zero_le (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    ‖chV t s - chV t 0‖ ≤ 2 * |s| / t ^ 4 := by
  have hw := chW_ne_zero ht ht4 s
  have hw0 := chW_ne_zero ht ht4 0
  have hdiff : chV t s - chV t 0 = (chW t s - chW t 0) / (chW t s * chW t 0) := by
    unfold chV; field_simp; ring
  have hwd : chW t s - chW t 0 = ((Real.exp (2 * s) - 1 : ℝ) : ℂ) * chOmega t := by
    unfold chW; push_cast; simp; ring
  rw [hdiff, hwd, norm_div, norm_mul, norm_mul, norm_chOmega ht4, norm_chW_zero ht ht4,
    Complex.norm_real, Real.norm_eq_abs, mul_one]
  have h1 : |Real.exp (2 * s) - 1| ≤ 4 * |s| := by
    have := Real.abs_exp_sub_one_le (x := 2 * s) (by rw [abs_mul, abs_two]; linarith)
    rw [abs_mul, abs_two] at this; linarith
  have h2 : t ^ 2 ≤ ‖chW t s‖ := by
    refine le_trans ?_ (le_norm_chW ht ht4 s)
    have he : 1 / 2 ≤ Real.exp s := by
      have hs' : -(1 / 2) ≤ s := by have := neg_abs_le s; linarith
      have h3 : Real.exp (-(1 / 2)) ≤ Real.exp s := Real.exp_le_exp.mpr hs'
      have h4 : 1 / 2 ≤ Real.exp (-(1 / 2)) := by
        rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
        have h5 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        have h6 := Real.exp_one_lt_d9
        nlinarith [Real.exp_pos (1 / 2)]
      linarith
    nlinarith [pow_pos ht 2]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc |Real.exp (2 * s) - 1| * t ^ 4 ≤ 4 * |s| * t ^ 4 := by gcongr
    _ = 2 * |s| * (t ^ 2 * (2 * t ^ 2)) := by ring
    _ ≤ 2 * |s| * (‖chW t s‖ * (2 * t ^ 2)) := by gcongr

theorem half_le_cos_chTheta_half : 1 / 2 ≤ Real.cos (chTheta t / 2) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := chTheta t / 2)
  have h1 := chTheta_le (t := t)
  have h0 := chTheta_nonneg (t := t)
  have hπ := Real.pi_lt_d2
  nlinarith

/-- **Drift of the normalized amplitude across the window.** -/
theorem norm_chA_sub_one_le (ht : 0 < t) (ht1 : t ≤ 1) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    ‖chA t s - 1‖ ≤ 10 * |s| / t ^ 2 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  set P := chP t s with hP
  set P₀ := chP t 0 with hP₀
  set p₀ := chP0 t with hp₀
  have hp0pos : 0 < p₀ := chP0_pos
  have hP₀eq := chP_zero ht ht2
  rw [← hP₀] at hP₀eq
  have hc : ‖Complex.exp (-Complex.I * ((chTheta t / 2 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hnP₀ : ‖P₀‖ = p₀ := by
    rw [hP₀eq, norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0pos]
  have hP₀ne : P₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnP₀; linarith
  -- `A = e^{s/2} P / P₀`
  have hinv : P₀⁻¹ = ((p₀ : ℝ) : ℂ)⁻¹ * Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ)) := by
    rw [hP₀eq, mul_inv, ← Complex.exp_neg]; congr 2; ring
  have hAeq : chA t s = (Real.exp (s / 2) : ℂ) * (P / P₀) := by
    rw [chA, ← hP, div_eq_mul_inv P P₀, hinv]; ring
  -- real part of `P + P₀`
  have hreP₀ : p₀ / 2 ≤ P₀.re := by
    rw [hP₀eq, Complex.re_ofReal_mul]
    have : (Complex.exp (-Complex.I * ((chTheta t / 2 : ℝ) : ℂ))).re = Real.cos (chTheta t / 2) := by
      rw [show -Complex.I * ((chTheta t / 2 : ℝ) : ℂ) = ((-(chTheta t / 2)) : ℝ) * Complex.I by
        push_cast; ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    rw [this]
    have := half_le_cos_chTheta_half (t := t)
    nlinarith
  have hsum : p₀ / 2 ≤ ‖P + P₀‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.add_re]
    have := re_cpow_half_nonneg (-Complex.I * chV t s)
    have hPre : 0 ≤ P.re := this
    linarith
  have hsq : (P - P₀) * (P + P₀) = -Complex.I * (chV t s - chV t 0) := by
    have h1 := chP_sq (t := t) s
    have h2 := chP_sq (t := t) 0
    rw [← hP] at h1; rw [← hP₀] at h2
    linear_combination h1 - h2
  have hv := norm_chV_sub_chV_zero_le ht ht4 hs
  have hPdiff : ‖P - P₀‖ ≤ 2 * |s| / t ^ 4 / (p₀ / 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖P - P₀‖ * (p₀ / 2) ≤ ‖P - P₀‖ * ‖P + P₀‖ :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = ‖chV t s - chV t 0‖ := by rw [← norm_mul, hsq, norm_mul]; simp
      _ ≤ 2 * |s| / t ^ 4 := hv
  have hr1 : ‖P / P₀ - 1‖ ≤ 8 * |s| / t ^ 2 := by
    rw [show P / P₀ - 1 = (P - P₀) / P₀ by field_simp, norm_div, hnP₀,
      div_le_iff₀ hp0pos]
    have hp2 := chP0_sq ht
    rw [← hp₀] at hp2
    calc ‖P - P₀‖ ≤ 2 * |s| / t ^ 4 / (p₀ / 2) := hPdiff
      _ = 8 * |s| / t ^ 2 * p₀ := by
          field_simp
          rw [show p₀ ^ 2 = 1 / (2 * t ^ 2) from hp2] at *
          field_simp
          nlinarith [hp2]
  have hA1 := norm_chA_le_one ht ht4 s
  rw [hAeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hA1
  have hr : ‖P / P₀‖ ≤ 2 := by
    have he : Real.exp (-(1 / 4)) ≤ Real.exp (s / 2) :=
      Real.exp_le_exp.mpr (by have := neg_abs_le s; linarith)
    have he2 : 1 / 2 ≤ Real.exp (-(1 / 4)) := by
      have := Real.add_one_le_exp (-(1 / 4) : ℝ); linarith
    nlinarith [norm_nonneg (P / P₀)]
  have hes : ‖(Real.exp (s / 2) : ℂ) - 1‖ ≤ |s| := by
    rw [show (Real.exp (s / 2) : ℂ) - 1 = ((Real.exp (s / 2) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    have := Real.abs_exp_sub_one_le (x := s / 2) (by rw [abs_div, abs_two]; linarith)
    rw [abs_div, abs_two] at this; linarith
  rw [hAeq, show (Real.exp (s / 2) : ℂ) * (P / P₀) - 1 =
    ((Real.exp (s / 2) : ℂ) - 1) * (P / P₀) + (P / P₀ - 1) by ring]
  have ht2p : 0 < t ^ 2 := by positivity
  calc ‖((Real.exp (s / 2) : ℂ) - 1) * (P / P₀) + (P / P₀ - 1)‖
      ≤ ‖(Real.exp (s / 2) : ℂ) - 1‖ * ‖P / P₀‖ + ‖P / P₀ - 1‖ := by
        refine le_trans (norm_add_le _ _) ?_; rw [norm_mul]
    _ ≤ |s| * 2 + 8 * |s| / t ^ 2 := by
        gcongr
    _ ≤ 10 * |s| / t ^ 2 := by
        have h2 : |s| * 2 ≤ 2 * |s| / t ^ 2 := by
          rw [le_div_iff₀ ht2p]; nlinarith [abs_nonneg s]
        have : 2 * |s| / t ^ 2 + 8 * |s| / t ^ 2 = 10 * |s| / t ^ 2 := by ring
        linarith

end Amplitude

end

end RHTower
