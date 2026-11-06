import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffRealProfile

/-!
# Transverse modulus control for Hausdorff atoms

A vertical displacement of the centered zero changes the modulus of the
complementary factor only quadratically. The reciprocal factor decreases.
Together these bounds transfer the real saddle tails to zeros in the strip.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

private theorem reciprocal_re_error_le {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    1 / a - (a - b) / (a + b) ^ 2 ≤ 4 * b / a ^ 2 := by
  have hab : 0 < a + b := by positivity
  have heq : 1 / a - (a - b) / (a + b) ^ 2 =
      b * (3 * a + b) / (a * (a + b) ^ 2) := by
    field_simp [ha.ne', hab.ne']
    ring
  rw [heq, div_le_div_iff₀ (by positivity) (sq_pos_of_pos ha)]
  have h : 0 ≤ a * b * (a ^ 2 + 7 * a * b + 4 * b ^ 2) := by positivity
  nlinarith only [h]

private theorem shifted_square_le {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hb : 0 ≤ b) :
    R ^ 2 - 2 * R * (a - b) / (a + b) ^ 2 + 1 / (a + b) ^ 2 ≤
      (R - 1 / a) ^ 2 + 8 * R * b / a ^ 2 := by
  have hab : 0 < a + b := by positivity
  have hrec := mul_le_mul_of_nonneg_left (reciprocal_re_error_le ha hb)
    (by positivity : 0 ≤ 2 * R)
  have hN : 1 / (a + b) ^ 2 ≤ 1 / a ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ha) (by nlinarith only [ha, hb])
  have heq : R ^ 2 - 2 * R * (a - b) / (a + b) ^ 2 + 1 / (a + b) ^ 2 =
      (R - 1 / a) ^ 2 + 2 * R * (1 / a - (a - b) / (a + b) ^ 2) +
        (1 / (a + b) ^ 2 - 1 / a ^ 2) := by
    field_simp [ha.ne', hab.ne']
    ring
  rw [heq]
  rw [show 2 * R * (4 * b / a ^ 2) = 8 * R * b / a ^ 2 by ring] at hrec
  linarith only [hrec, hN]

/-- Squared modulus of the complementary reciprocal factor. -/
theorem norm_complement_sq (R : ℝ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖(R : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2‖ ^ 2 =
      R ^ 2 - 2 * R * (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 +
        1 / (x ^ 2 + y ^ 2) ^ 2 := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hN : Complex.normSq z = x ^ 2 + y ^ 2 := by
    simp [z, Complex.normSq_apply, pow_two]
  have hNpos : 0 < x ^ 2 + y ^ 2 := by positivity
  have hRe : (z⁻¹ ^ 2).re = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
    rw [pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im, hN]
    simp only [z, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp [hNpos.ne']
    ring
  have hInv : Complex.normSq (z⁻¹ ^ 2) = 1 / (x ^ 2 + y ^ 2) ^ 2 := by
    rw [pow_two, Complex.normSq_mul, Complex.normSq_inv, hN]
    rw [one_div, ← inv_pow]
    ring
  have hR : Complex.normSq (R : ℂ) = R ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  change ‖(R : ℂ) - z⁻¹ ^ 2‖ ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_sub, hR, hInv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    zero_mul, sub_zero, hRe]
  ring

/-- The complementary factor on the real axis stays at least half the radius. -/
theorem half_radius_le_complement {R x : ℝ} (hx : 0 < x) (hRx : 2 ≤ R * x ^ 2) :
    R / 2 ≤ R - x⁻¹ ^ 2 := by
  have h : 1 / x ^ 2 ≤ R / 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hx)]
    nlinarith only [hRx]
  rw [inv_pow, ← one_div]
  linarith only [h]

/-- Vertical displacement increases the complementary modulus only quadratically. -/
theorem norm_complement_le {R x : ℝ} (hR : 0 < R) (hx : 0 < x)
    (hRx : 2 ≤ R * x ^ 2) (y : ℝ) :
    ‖(R : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2‖ ≤
      (R - x⁻¹ ^ 2) * Real.exp (16 * y ^ 2 / (R * x ^ 4)) := by
  let A := R - x⁻¹ ^ 2
  let v := 32 * y ^ 2 / (R * x ^ 4)
  have hAhalf : R / 2 ≤ A := half_radius_le_complement hx hRx
  have hA : 0 < A := by linarith only [hR, hAhalf]
  have hA2 : R ^ 2 ≤ 4 * A ^ 2 := by nlinarith only [hAhalf, hR]
  have hbase := shifted_square_le hR.le (sq_pos_of_pos hx) (sq_nonneg y)
  have hsq : ‖(R : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2‖ ^ 2 ≤
      A ^ 2 + 8 * R * y ^ 2 / x ^ 4 := by
    rw [norm_complement_sq R hx y]
    norm_num only [← pow_mul] at hbase
    simpa only [A, inv_pow, one_div] using hbase
  have hcoef : 8 * R * y ^ 2 / x ^ 4 ≤ A ^ 2 * v := by
    have h := mul_le_mul_of_nonneg_right hA2
      (show 0 ≤ 8 * y ^ 2 / (R * x ^ 4) by positivity)
    calc
      _ = R ^ 2 * (8 * y ^ 2 / (R * x ^ 4)) := by field_simp [hR.ne']
      _ ≤ 4 * A ^ 2 * (8 * y ^ 2 / (R * x ^ 4)) := h
      _ = A ^ 2 * v := by dsimp [v]; ring
  have hE : 1 + v ≤ Real.exp v := by linarith only [Real.add_one_le_exp v]
  have hsqexp : ‖(R : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2‖ ^ 2 ≤
      A ^ 2 * Real.exp v := by
    have h := mul_le_mul_of_nonneg_left hE (sq_nonneg A)
    nlinarith only [hsq, hcoef, h]
  have hexp : (A * Real.exp (v / 2)) ^ 2 = A ^ 2 * Real.exp v := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hroot : ‖(R : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2‖ ≤
      A * Real.exp (v / 2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hexp]
    exact hsqexp
  have hv : v / 2 = 16 * y ^ 2 / (R * x ^ 4) := by dsimp [v]; ring
  rw [hv] at hroot
  exact hroot

/-- The reciprocal factor decreases under vertical displacement. -/
theorem norm_reciprocal_square_le {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2‖ ≤ x⁻¹ ^ 2 := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm]
  have hN : Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I) = x ^ 2 + y ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  rw [hN, inv_pow]
  exact (inv_le_inv₀ (by positivity) (sq_pos_of_pos hx)).mpr (by nlinarith only [sq_nonneg y])

/-- Transverse modulus control for the complete atom, with the real profile retained. -/
theorem norm_kernel_le_realKernel_exp {R x : ℝ} (hR : 0 < R) (hx : 0 < x)
    (hRx : 2 ≤ R * x ^ 2) (p r : ℕ) (y : ℝ) :
    ‖kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      realKernel R p r x * Real.exp (16 * (r : ℝ) * y ^ 2 / (R * x ^ 4)) := by
  have hA : 0 ≤ R - x⁻¹ ^ 2 := by
    linarith only [half_radius_le_complement hx hRx, hR]
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (norm_reciprocal_square_le hx y) p
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (norm_complement_le hR hx hRx y) r
  rw [kernel, norm_mul, norm_pow _ p, norm_pow _ r]
  calc
    _ ≤ (x⁻¹ ^ 2) ^ p *
        ((R - x⁻¹ ^ 2) * Real.exp (16 * y ^ 2 / (R * x ^ 4))) ^ r :=
      mul_le_mul h₁ h₂ (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      unfold realKernel
      have heq : (r : ℝ) * (16 * y ^ 2 / (R * x ^ 4)) =
          16 * (r : ℝ) * y ^ 2 / (R * x ^ 4) := by ring
      rw [heq]
      ring

/-- At a quarter of the saddle height the real complementary factor is already positive. -/
theorem saddle_radius_mul_sq_ge {R s x : ℝ} {p r : ℕ} (hR : 0 < R) (hs : 0 < s)
    (hp : 0 < p) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * (p : ℝ) ≤ r) (hxs : s / 4 ≤ x) : 2 ≤ R * x ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hRs : 201 ≤ R * s ^ 2 := by
    by_contra h
    have hmul := mul_pos hpR (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hbalance, hpr, hmul]
  have hx2 : s ^ 2 ≤ 16 * x ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ s / 4) hxs 2
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_left hx2 hR.le
  nlinarith only [hRs, h]

/-- The strip displacement costs at most `exp (1024p/s²)` away from low ordinates. -/
theorem norm_kernel_le_realKernel_saddle_exp {R s x : ℝ} {p r : ℕ} (hR : 0 < R)
    (hs : 0 < s) (hp : 0 < p) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * (p : ℝ) ≤ r) (hxs : s / 4 ≤ x) {y : ℝ} (hy : |y| ≤ 1 / 2) :
    ‖kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      realKernel R p r x * Real.exp (1024 * (p : ℝ) / s ^ 2) := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity : 0 < s / 4) hxs
  have hRx := saddle_radius_mul_sq_ge hR hs hp hbalance hpr hxs
  have hA : 0 ≤ R - x⁻¹ ^ 2 := by
    linarith only [half_radius_le_complement hx hRx, hR]
  have hM : 0 ≤ realKernel R p r x := by unfold realKernel; positivity
  have hrbound : (r : ℝ) ≤ (p : ℝ) * R * s ^ 2 := by
    nlinarith only [hbalance, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hs4 : s ^ 4 ≤ 256 * x ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ s / 4) hxs 4
    nlinarith only [h]
  have hcost : 16 * (r : ℝ) * y ^ 2 / (R * x ^ 4) ≤ 1024 * (p : ℝ) / s ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hs)]
    have h₁ := mul_le_mul_of_nonneg_left hy2 (show 0 ≤ 16 * (r : ℝ) * s ^ 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hrbound (show 0 ≤ 4 * s ^ 2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hs4 (show 0 ≤ 4 * (p : ℝ) * R by positivity)
    nlinarith only [h₁, h₂, h₃]
  exact (norm_kernel_le_realKernel_exp hR hx hRx p r y).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) hM)

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
