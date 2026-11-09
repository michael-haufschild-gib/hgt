import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailFilters
import GaloisForLFunctions.HTGeometry.TanhSelfBound
import GaloisForLFunctions.HTGeometry.CosineSublevelPeriodMeasure

/-!
# Complex three-point deletion with summable variation

A phase of `2π/3` annihilates a nonreal exponent with complex translation
coefficients. Their total variation costs at most `exp(3(ha)²/2)`.
Thus bounded depths and square-summable shifts permit signed infinite deletion.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Central coefficient at phase `2π/3`. -/
def signedDeletionCenter (x : ℝ) : ℂ :=
  ((Real.cosh x / 2 : ℝ) : ℂ) -
    ((Real.sinh x * Real.sin (2 * Real.pi / 3) : ℝ) : ℂ) * I

@[simp] theorem signedDeletionCenter_re (x : ℝ) :
    (signedDeletionCenter x).re = Real.cosh x / 2 := by
  simp [signedDeletionCenter]

@[simp] theorem signedDeletionCenter_im (x : ℝ) :
    (signedDeletionCenter x).im = -(Real.sinh x * Real.sin (2 * Real.pi / 3)) := by
  simp [signedDeletionCenter]

theorem norm_signedDeletionCenter_sq (x : ℝ) :
    ‖signedDeletionCenter x‖ ^ 2 = Real.cosh x ^ 2 / 4 + 3 * Real.sinh x ^ 2 / 4 := by
  have hsin : Real.sin (2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    have h := Real.sin_sq_add_cos_sq (2 * Real.pi / 3)
    rw [HTGeometry.cos_two_pi_div_three] at h
    nlinarith only [h]
  rw [Complex.sq_norm, Complex.normSq_apply, signedDeletionCenter_re,
    signedDeletionCenter_im]
  simp only [← sq, neg_sq, mul_pow]
  rw [hsin]
  ring

theorem signedDeletion_denominator_bound (x : ℝ) :
    1 + Real.cosh x / 2 ≤ ‖1 + signedDeletionCenter x‖ := by
  simpa only [Complex.add_re, Complex.one_re, signedDeletionCenter_re] using
    Complex.re_le_norm (1 + signedDeletionCenter x)

theorem signedDeletion_denominator_ne_zero (x : ℝ) :
    1 + signedDeletionCenter x ≠ 0 := by
  apply norm_pos_iff.mp
  have h := signedDeletion_denominator_bound x
  linarith only [h, Real.cosh_pos x]

theorem norm_signedDeletionCenter_le (x : ℝ) :
    ‖signedDeletionCenter x‖ ≤ Real.cosh x * (1 / 2 + 3 / 4 * x ^ 2) := by
  have hs := HTGeometry.sinh_le_mul_cosh (abs_nonneg x)
  rw [← Real.abs_sinh, Real.cosh_abs] at hs
  have hs2 := mul_self_le_mul_self (abs_nonneg (Real.sinh x)) hs
  simp only [← sq, sq_abs, mul_pow] at hs2
  have hsq := norm_signedDeletionCenter_sq x
  have hpos : 0 ≤ Real.cosh x * (1 / 2 + 3 / 4 * x ^ 2) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hpos).mp
  nlinarith only [hs2, hsq, sq_nonneg (Real.cosh x * x ^ 2)]

/-- The complex translation coefficients have a quadratic variation cost. -/
theorem signedDeletion_variation_le (x : ℝ) :
    (1 + ‖signedDeletionCenter x‖) / ‖1 + signedDeletionCenter x‖ ≤
      Real.exp (3 / 2 * x ^ 2) := by
  have hd := signedDeletion_denominator_bound x
  have hd0 := norm_pos_iff.mpr (signedDeletion_denominator_ne_zero x)
  have hb := norm_signedDeletionCenter_le x
  have hn : 1 + ‖signedDeletionCenter x‖ ≤
      (1 + Real.cosh x / 2) * (1 + 3 / 2 * x ^ 2) := by
    nlinarith only [hb, sq_nonneg x]
  have hm := mul_le_mul_of_nonneg_right hd
    (show 0 ≤ 1 + 3 / 2 * x ^ 2 by positivity)
  have he : 1 + 3 / 2 * x ^ 2 ≤ Real.exp (3 / 2 * x ^ 2) := by
    simpa only [add_comm] using Real.add_one_le_exp (3 / 2 * x ^ 2)
  apply (div_le_iff₀ hd0).mpr
  calc
    _ ≤ (1 + Real.cosh x / 2) * (1 + 3 / 2 * x ^ 2) := hn
    _ ≤ ‖1 + signedDeletionCenter x‖ * (1 + 3 / 2 * x ^ 2) := hm
    _ ≤ Real.exp (3 / 2 * x ^ 2) * ‖1 + signedDeletionCenter x‖ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he hd0.le

/-- Laplace multiplier of the complex three-point translation kernel. -/
def signedDeletionFactor (a h : ℝ) (w : ℂ) : ℂ :=
  (Complex.cosh ((h : ℂ) * w) + signedDeletionCenter (h * a)) /
    (1 + signedDeletionCenter (h * a))

@[simp] theorem signedDeletionFactor_zero (a h : ℝ) :
    signedDeletionFactor a h 0 = 1 := by
  simp only [signedDeletionFactor, mul_zero, Complex.cosh_zero]
  exact div_self (signedDeletion_denominator_ne_zero _)

/-- The specified phase kills the exponent exactly, without pairing conjugates. -/
theorem signedDeletionFactor_root (a h γ : ℝ) (hphase : h * γ = 2 * Real.pi / 3) :
    signedDeletionFactor a h ((a : ℂ) + (γ : ℂ) * I) = 0 := by
  have he : (h : ℂ) * ((a : ℂ) + (γ : ℂ) * I) =
      ((h * a : ℝ) : ℂ) + ((2 * Real.pi / 3 : ℝ) : ℂ) * I := by
    rw [← hphase]
    push_cast
    ring
  rw [signedDeletionFactor, he, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, HTGeometry.cos_two_pi_div_three]
  unfold signedDeletionCenter
  have hn : ((Real.cosh (h * a) : ℂ) * ((-(1 / 2) : ℝ) : ℂ) +
      (Real.sinh (h * a) : ℂ) * ((Real.sin (2 * Real.pi / 3) : ℂ) * I)) +
      (((Real.cosh (h * a) / 2 : ℝ) : ℂ) -
        ((Real.sinh (h * a) * Real.sin (2 * Real.pi / 3) : ℝ) : ℂ) * I) = 0 := by
    push_cast
    ring
  rw [hn, zero_div]

/-- At a retained exponent, the multiplier error is quadratic in the shift. -/
theorem norm_signedDeletionFactor_sub_one_le (a h : ℝ) (w : ℂ)
    (hsmall : |h| * ‖w‖ ≤ 1) :
    ‖signedDeletionFactor a h w - 1‖ ≤ 2 / 3 * h ^ 2 * ‖w‖ ^ 2 := by
  have he : signedDeletionFactor a h w - 1 =
      (Complex.cosh ((h : ℂ) * w) - 1) / (1 + signedDeletionCenter (h * a)) := by
    unfold signedDeletionFactor
    apply (eq_div_iff (signedDeletion_denominator_ne_zero _)).mpr
    rw [sub_mul, div_mul_cancel₀ _ (signedDeletion_denominator_ne_zero _), one_mul]
    ring
  have hz : ‖(h : ℂ) * w‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hsmall
  have hd : 3 / 2 ≤ ‖1 + signedDeletionCenter (h * a)‖ := by
    have hb := signedDeletion_denominator_bound (h * a)
    linarith only [hb, Real.one_le_cosh (h * a)]
  rw [he, norm_div]
  calc
    _ ≤ ‖(h : ℂ) * w‖ ^ 2 / ‖1 + signedDeletionCenter (h * a)‖ :=
      div_le_div_of_nonneg_right (norm_cosh_sub_one_le_sq hz) (norm_nonneg _)
    _ ≤ ‖(h : ℂ) * w‖ ^ 2 / (3 / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hd
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring

theorem signedDeletionFactor_ne_zero_of_small (a h : ℝ) (w : ℂ)
    (hsmall : |h| * ‖w‖ ≤ 1) : signedDeletionFactor a h w ≠ 0 := by
  intro hz
  have hb := norm_signedDeletionFactor_sub_one_le a h w hsmall
  rw [hz, zero_sub, norm_neg, norm_one] at hb
  have hs := mul_self_le_mul_self (show 0 ≤ |h| * ‖w‖ by positivity) hsmall
  simp only [← sq, mul_pow, sq_abs, one_pow] at hs
  linarith only [hb, hs]

/-- Square-summable shifts preserve a retained exponent through infinitely many deletions. -/
theorem multipliable_signedDeletionFactor_ne_zero {ι : Type*} (a h : ι → ℝ) (w : ℂ)
    (hsq : Summable fun i => h i ^ 2) (hsmall : ∀ i, |h i| * ‖w‖ ≤ 1) :
    Multipliable (fun i => signedDeletionFactor (a i) (h i) w) ∧
      (∏' i, signedDeletionFactor (a i) (h i) w) ≠ 0 := by
  have hs : Summable fun i => ‖signedDeletionFactor (a i) (h i) w - 1‖ := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _
      (hsq.mul_right (2 / 3 * ‖w‖ ^ 2))
    intro i
    convert norm_signedDeletionFactor_sub_one_le (a i) (h i) w (hsmall i) using 1 <;> ring
  have he : (fun i => 1 + (signedDeletionFactor (a i) (h i) w - 1)) =
      fun i => signedDeletionFactor (a i) (h i) w := by funext i; ring
  have hm := multipliable_one_add_of_summable hs
  have hn := tprod_one_add_ne_zero_of_summable
    (f := fun i => signedDeletionFactor (a i) (h i) w - 1)
    (fun i => by
      simpa only [show 1 + (signedDeletionFactor (a i) (h i) w - 1) =
        signedDeletionFactor (a i) (h i) w by ring] using
        signedDeletionFactor_ne_zero_of_small (a i) (h i) w (hsmall i)) hs
  rw [he] at hm hn
  exact ⟨hm, hn⟩

#print axioms signedDeletion_variation_le
#print axioms signedDeletionFactor_root
#print axioms multipliable_signedDeletionFactor_ne_zero

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
