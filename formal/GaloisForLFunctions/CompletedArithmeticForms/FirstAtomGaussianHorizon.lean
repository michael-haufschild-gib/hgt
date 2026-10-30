import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomRankBoundary
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

/-!
# Explicit Gaussian horizons for the literal first theta atom

A complex unit-circle estimate controls every normalized signed moment with an
explicit factorial dependence on order. The resulting source horizon is simultaneous
in center and order; positivity of mixed Hankel heads is a separate condition.
-/

noncomputable section

open Finset Filter Topology Metric

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Quartic complex remainder after the even quadratic Taylor section. -/
theorem norm_cosh_quadratic_remainder_le (w : ℂ) :
    ‖Complex.cosh w - 1 - w ^ 2 / 2‖ ≤ ‖w‖ ^ 4 / 24 * Real.exp ‖w‖ := by
  have hp : ‖Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6)‖ ≤
      ‖w‖ ^ 4 / 24 * Real.exp ‖w‖ := by
    convert norm_complex_exp_sub_sum_le_factorial_tail w 4 using 1 <;>
      norm_num [Finset.sum_range_succ]
  have hm : ‖Complex.exp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6)‖ ≤
      ‖w‖ ^ 4 / 24 * Real.exp ‖w‖ := by
    convert norm_complex_exp_sub_sum_le_factorial_tail (-w) 4 using 1 <;>
      norm_num [Finset.sum_range_succ]
    ring
  have he : Complex.cosh w - 1 - w ^ 2 / 2 =
      ((Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6)) +
        (Complex.exp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6))) / 2 := by
    rw [Complex.cosh]
    ring
  rw [he, norm_div]
  norm_num only [Complex.norm_ofNat]
  have hsum := norm_add_le
    (Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6))
    (Complex.exp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6))
  linarith only [hp, hm, hsum]

private theorem norm_exp_difference_le (a b : ℂ) :
    ‖Complex.exp a - Complex.exp b‖ ≤
      Real.exp (‖b‖ + ‖a - b‖) * ‖a - b‖ := by
  have hr : ‖Complex.exp (a - b) - 1‖ ≤ ‖a - b‖ * Real.exp ‖a - b‖ := by
    simpa using norm_complex_exp_sub_sum_le_factorial_tail (a - b) 1
  have he : Complex.exp a - Complex.exp b =
      Complex.exp b * (Complex.exp (a - b) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    congr 1
    · congr 1
      ring
    · ring
  rw [he, norm_mul]
  calc
    _ ≤ Real.exp ‖b‖ * (‖a - b‖ * Real.exp ‖a - b‖) :=
      mul_le_mul (Complex.norm_exp_le_exp_norm b) hr (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Uniform absolute constant in the all-order first-atom Gaussian estimate. -/
def firstAtomGaussianErrorConstant : ℝ :=
  Real.exp (4 + 2 * Real.exp 2) * (24 + 10 * Real.exp 2)

theorem firstAtomGaussianErrorConstant_pos : 0 < firstAtomGaussianErrorConstant := by
  unfold firstAtomGaussianErrorConstant
  positivity

/-- Mass-normalized first-atom profile before the inverse-square-root change of variable. -/
def firstAtomGaussianKernel (q : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-2 * (q : ℂ) * (Complex.cosh w - 1)) *
    (1 - ((12 * q / (2 * q - 3) ^ 2 : ℝ) : ℂ) * (Complex.cosh w - 1))

/-- The first-atom kernel has an explicit Gaussian error on its shrinking complex disk. -/
theorem firstAtomGaussianKernel_error_le {q : ℝ} (hq : 3 ≤ q) {w : ℂ}
    (hw : ‖w‖ ^ 2 ≤ 4 / q) :
    ‖firstAtomGaussianKernel q w - Complex.exp (-(q : ℂ) * w ^ 2)‖ ≤
      firstAtomGaussianErrorConstant / q := by
  have hqp : 0 < q := by linarith only [hq]
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hqp
  have hd : 0 < 2 * q - 3 := by linarith only [hq]
  have hB : q ^ 2 ≤ (2 * q - 3) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq)
      (show 0 ≤ 3 * q - 3 by linarith only [hq])]
  have hi : 1 / q ^ 2 ≤ 1 / q := by
    apply (div_le_div_iff₀ hq2 hqp).mpr
    nlinarith only [mul_nonneg hqp.le (sub_nonneg.mpr hq1)]
  have hw2 : ‖w‖ ≤ 2 := by
    have hb : 4 / q ≤ 4 := (div_le_iff₀ hqp).mpr (by linarith only [hq1])
    nlinarith only [hw, hb, norm_nonneg w]
  have hw4 : ‖w‖ ^ 4 ≤ 16 / q ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg ‖w‖) hw 2
    calc
      _ = (‖w‖ ^ 2) ^ 2 := by ring
      _ ≤ (4 / q) ^ 2 := h
      _ = _ := by rw [div_pow]; norm_num
  have hr : ‖Complex.cosh w - 1 - w ^ 2 / 2‖ ≤
      (2 * Real.exp 2 / 3) / q ^ 2 := by
    calc
      _ ≤ ‖w‖ ^ 4 / 24 * Real.exp ‖w‖ := norm_cosh_quadratic_remainder_le w
      _ ≤ (16 / q ^ 2) / 24 * Real.exp 2 :=
        mul_le_mul (div_le_div_of_nonneg_right hw4 (by norm_num))
          (Real.exp_le_exp.mpr hw2) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hc : ‖Complex.cosh w - 1‖ ≤ (2 + 2 * Real.exp 2 / 3) / q := by
    have hs := norm_add_le (Complex.cosh w - 1 - w ^ 2 / 2) (w ^ 2 / 2)
    rw [sub_add_cancel, norm_div, norm_pow] at hs
    norm_num only [Complex.norm_ofNat] at hs
    have hi' := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 2 * Real.exp 2 / 3 by positivity)
    have hw' := div_le_div_of_nonneg_right hw (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      _ ≤ (2 * Real.exp 2 / 3) / q ^ 2 + (4 / q) / 2 := by
        linarith only [hs, hr, hw']
      _ ≤ (2 * Real.exp 2 / 3) / q + (4 / q) / 2 := by
        simp only [div_eq_mul_inv, one_mul] at hi' ⊢
        linarith only [hi']
      _ = _ := by ring
  let a : ℂ := -2 * (q : ℂ) * (Complex.cosh w - 1)
  let b : ℂ := -(q : ℂ) * w ^ 2
  let A : ℝ := 2 * Real.exp 2
  let B : ℝ := 24 + 8 * Real.exp 2
  let E : ℝ := Real.exp (4 + A)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hab : ‖a - b‖ ≤ A / q := by
    have he : a - b = -2 * (q : ℂ) * (Complex.cosh w - 1 - w ^ 2 / 2) := by
      dsimp [a, b]
      ring
    rw [he, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqp]
    norm_num only [norm_neg, Complex.norm_ofNat]
    calc
      _ ≤ (2 * q) * ((2 * Real.exp 2 / 3) / q ^ 2) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (4 * Real.exp 2 / 3) / q := by field_simp; ring
      _ ≤ A / q := by
        apply div_le_div_of_nonneg_right _ hqp.le
        dsimp [A]
        linarith only [Real.exp_pos (2 : ℝ)]
  have hAn : A / q ≤ A := (div_le_iff₀ hqp).mpr
    (by nlinarith only [mul_nonneg hA (sub_nonneg.mpr hq1)])
  have hb : ‖b‖ ≤ 4 := by
    dsimp [b]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqp, norm_pow]
    calc
      _ ≤ q * (4 / q) := mul_le_mul_of_nonneg_left hw hqp.le
      _ = _ := by field_simp
  have ha : ‖a‖ ≤ 4 + A := by
    have h := norm_add_le (a - b) b
    rw [sub_add_cancel] at h
    linarith only [h, hb, hab, hAn]
  have hea : ‖Complex.exp a‖ ≤ E :=
    (Complex.norm_exp_le_exp_norm a).trans (Real.exp_le_exp.mpr ha)
  have heab : ‖Complex.exp a - Complex.exp b‖ ≤ E * (A / q) := by
    refine (norm_exp_difference_le a b).trans ?_
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith only [hb, hab, hAn])) hab
      (norm_nonneg _) hE
  have hcoef : 12 * q / (2 * q - 3) ^ 2 ≤ 12 / q := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) hqp).mpr
    nlinarith only [hB]
  have hfactor : ‖((12 * q / (2 * q - 3) ^ 2 : ℝ) : ℂ) *
      (Complex.cosh w - 1)‖ ≤ B / q ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 12 * q / (2 * q - 3) ^ 2)]
    calc
      _ ≤ (12 / q) * ((2 + 2 * Real.exp 2 / 3) / q) :=
        mul_le_mul hcoef hc (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hsplit : firstAtomGaussianKernel q w - Complex.exp b =
      -(Complex.exp a * (((12 * q / (2 * q - 3) ^ 2 : ℝ) : ℂ) *
        (Complex.cosh w - 1))) + (Complex.exp a - Complex.exp b) := by
    dsimp [firstAtomGaussianKernel, a]
    ring
  change ‖firstAtomGaussianKernel q w - Complex.exp b‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖-(Complex.exp a * (((12 * q / (2 * q - 3) ^ 2 : ℝ) : ℂ) *
        (Complex.cosh w - 1)))‖ + ‖Complex.exp a - Complex.exp b‖ := norm_add_le _ _
    _ ≤ E * (B / q ^ 2) + E * (A / q) := by
      rw [norm_neg, norm_mul]
      exact add_le_add (mul_le_mul hea hfactor (norm_nonneg _) hE) heab
    _ ≤ E * (B / q) + E * (A / q) := by
      have hi' := mul_le_mul_of_nonneg_left hi (mul_nonneg hE hB0)
      simp only [div_eq_mul_inv, one_mul] at hi' ⊢
      nlinarith only [hi']
    _ = _ := by dsimp [firstAtomGaussianErrorConstant, A, B, E]; ring

/-- The literal rotated source in its Gaussian mass and length coordinates. -/
def firstAtomNormalizedRotatedPair (x : ℝ) (z : ℂ) : ℂ :=
  firstAtomRotatedPair x
    (((Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) : ℝ) : ℂ)⁻¹ * z) /
      ((thetaCuspSourceTerm x 1 ^ 2 : ℝ) : ℂ)

theorem firstAtomNormalizedRotatedPair_entire (x : ℝ) :
    Differentiable ℂ (firstAtomNormalizedRotatedPair x) := by
  have hf := firstAtomRotatedPair_entire x
  unfold firstAtomNormalizedRotatedPair
  fun_prop

/-- Exact first-atom mass in physical scale. -/
theorem firstAtom_mass_eq (x : ℝ) :
    thetaCuspSourceTerm x 1 ^ 2 =
      4 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        Real.exp (x - 2 * thetaCuspSingleAtomReflectionScale 1 x) *
          (2 * thetaCuspSingleAtomReflectionScale 1 x - 3) ^ 2 := by
  have h := ThetaCuspOddFour.firstAtomPair_eq_affine x 0
  simpa [ThetaCuspOddFour.affine, ThetaCuspOddFour.gaussian,
    ThetaCuspOddFour.factor, pow_two] using h

theorem firstAtom_mass_pos {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspSourceTerm x 1 ^ 2 := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hd : 0 < 2 * thetaCuspSingleAtomReflectionScale 1 x - 3 := by linarith only [hq]
  rw [firstAtom_mass_eq]
  positivity

theorem firstAtomNormalizedRotatedPair_eq_kernel {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (z : ℂ) :
    firstAtomNormalizedRotatedPair x z =
      firstAtomGaussianKernel (thetaCuspSingleAtomReflectionScale 1 x)
        (2 * (Complex.I *
          (((Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) : ℝ) : ℂ)⁻¹ * z))) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let C := 4 * q ^ 2 * Real.exp (x - 2 * q)
  have hqp : 0 < q := by dsimp [q]; linarith only [hq]
  have hd : 0 < 2 * q - 3 := by linarith only [hq]
  have hC : C ≠ 0 := by dsimp [C]; positivity
  have hCc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC
  have hdc : 2 * (q : ℂ) - 3 ≠ 0 := by exact_mod_cast hd.ne'
  unfold firstAtomNormalizedRotatedPair firstAtomRotatedPair firstAtomComplexPair
    firstAtomGaussianKernel
  rw [firstAtom_mass_eq]
  change (C : ℂ) * _ * _ / ((C * (2 * q - 3) ^ 2 : ℝ) : ℂ) = _
  dsimp only [q] at *
  push_cast
  field_simp [hCc, hdc]

/-- Uniform unit-disk Gaussian approximation, with the actual source mass retained. -/
theorem firstAtomNormalizedRotatedPair_error_le {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖firstAtomNormalizedRotatedPair x z - Complex.exp (4 * z ^ 2)‖ ≤
      firstAtomGaussianErrorConstant / thetaCuspSingleAtomReflectionScale 1 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let w := 2 * (Complex.I * (((Real.sqrt q : ℝ) : ℂ)⁻¹ * z))
  have hqp : 0 < q := by dsimp [q]; linarith only [hq]
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hqp.le
  have hsqc : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast hsq
  have hqn : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqp.ne'
  have hsn : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hwn : ‖w‖ ^ 2 = 4 * ‖z‖ ^ 2 / q := by
    dsimp [w]
    simp only [norm_mul, Complex.norm_I, one_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, mul_pow, inv_pow, hsq]
    norm_num
    ring
  have hw : ‖w‖ ^ 2 ≤ 4 / q := by
    rw [hwn]
    have hz2 : ‖z‖ ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2
    exact div_le_div_of_nonneg_right (by linarith only [hz2]) hqp.le
  have hex : -(q : ℂ) * w ^ 2 = 4 * z ^ 2 := by
    dsimp [w]
    simp only [mul_pow, Complex.I_sq, inv_pow, hsqc]
    field_simp
    ring
  rw [firstAtomNormalizedRotatedPair_eq_kernel hq]
  change ‖firstAtomGaussianKernel q w - Complex.exp (4 * z ^ 2)‖ ≤ _
  rw [← hex]
  exact firstAtomGaussianKernel_error_le hq hw

/-- Even complex jets in Gaussian coordinates are exactly the normalized signed source moments. -/
theorem firstAtomNormalizedRotatedPair_even_jet (x : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k) (firstAtomNormalizedRotatedPair x) 0 =
      (thetaCuspFirstAtomScaledEvenJet k x : ℂ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hsq : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have hscale : (((Real.sqrt q : ℝ) : ℂ)⁻¹) ^ (2 * k) = ((q : ℂ) ^ k)⁻¹ := by
    rw [pow_mul, inv_pow, hsq, inv_pow]
  have hI : Complex.I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    rw [pow_mul, Complex.I_sq]
    norm_cast
  change iteratedDeriv (2 * k)
    (fun z : ℂ => firstAtomRotatedPair x (((Real.sqrt q : ℝ) : ℂ)⁻¹ * z) /
      ((thetaCuspSourceTerm x 1 ^ 2 : ℝ) : ℂ)) 0 = _
  rw [iteratedDeriv_div_const,
    iteratedDeriv_comp_const_mul (firstAtomRotatedPair_entire x).contDiff]
  simp only [mul_zero, firstAtomRotatedPair_jet, hscale, hI,
    thetaCuspFirstAtomScaledEvenJet, Complex.ofReal_mul,
    Complex.ofReal_pow, div_eq_mul_inv, mul_inv_rev]
  push_cast
  dsimp only [q]
  ring

/-- The entire Gaussian model has the same positive Gamma moments as the real Gaussian profile. -/
theorem complexGaussian_even_jet (k : ℕ) :
    iteratedDeriv (2 * k) (fun z : ℂ => Complex.exp (4 * z ^ 2)) 0 =
      (gaussianMoment k : ℂ) := by
  let G : ℂ → ℂ := fun z => Complex.exp (-4 * z ^ 2)
  have hG : Differentiable ℂ G := by dsimp [G]; fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) profile := by unfold profile; fun_prop
  have hr (n : ℕ) : iteratedDeriv n G 0 = ((iteratedDeriv n profile (0 : ℝ) : ℝ) : ℂ) := by
    have h := congrFun (_root_.HTGeometry.iteratedDeriv_comp_ofReal n hG) 0
    have he : (fun t : ℝ => G (t : ℂ)) = fun t : ℝ => (profile t : ℂ) := by
      funext t
      simp only [G, profile, Complex.ofReal_exp, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_pow]
    rw [he, GaloisForLFunctions.iteratedDeriv_ofReal_comp hs n] at h
    exact h.symm
  have he : (fun z : ℂ => Complex.exp (4 * z ^ 2)) = fun z : ℂ => G (Complex.I * z) := by
    funext z
    dsimp [G]
    congr 1
    rw [mul_pow, Complex.I_sq]
    ring
  have hI : Complex.I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    rw [pow_mul, Complex.I_sq]
    norm_cast
  rw [he, iteratedDeriv_comp_const_mul hG.contDiff]
  simp only [mul_zero, hr, hI, ← Complex.ofReal_mul, profile_signed_even_jet]

/-- A single explicit analytic estimate controls every signed first-atom moment. -/
theorem firstAtomScaledEvenJet_gaussian_error_le {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : ℕ) :
    |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k| ≤
      ((2 * k).factorial : ℝ) * firstAtomGaussianErrorConstant /
        thetaCuspSingleAtomReflectionScale 1 x := by
  let G : ℂ → ℂ := fun z => Complex.exp (4 * z ^ 2)
  have hG : Differentiable ℂ G := by dsimp [G]; fun_prop
  have hf := firstAtomNormalizedRotatedPair_entire x
  have hc : ∀ z ∈ sphere (0 : ℂ) 1,
      ‖(firstAtomNormalizedRotatedPair x - G) z‖ ≤
        firstAtomGaussianErrorConstant / thetaCuspSingleAtomReflectionScale 1 x := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact firstAtomNormalizedRotatedPair_error_le hq hzn.le
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * k)
    (by norm_num : (0 : ℝ) < 1) (hf.sub hG).diffContOnCl hc
  rw [iteratedDeriv_sub hf.contDiff.contDiffAt hG.contDiff.contDiffAt,
    firstAtomNormalizedRotatedPair_even_jet, complexGaussian_even_jet,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [one_pow, div_one, mul_div_assoc] using h

/-- Exact factorial form of the Gaussian moments used in the source comparison. -/
theorem gaussianMoment_eq_factorial (k : ℕ) :
    gaussianMoment k = (4 : ℝ) ^ k * ((2 * k).factorial : ℝ) / (k.factorial : ℝ) := by
  have hm (n : ℕ) : gaussianMoment (n + 1) = 8 * (2 * (n : ℝ) + 1) * gaussianMoment n := by
    simp only [gaussianMoment, pow_succ, gammaShapeMoment_succ]
    ring
  have hi : gaussianMoment k * (k.factorial : ℝ) = (4 : ℝ) ^ k * ((2 * k).factorial : ℝ) := by
    induction k with
    | zero => simp [gaussianMoment]
    | succ k ih =>
      rw [hm, Nat.factorial_succ,
        show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ, pow_succ]
      push_cast
      calc
        _ = 8 * (2 * (k : ℝ) + 1) * ((k : ℝ) + 1) *
            (gaussianMoment k * (k.factorial : ℝ)) := by ring
        _ = _ := by rw [ih]; ring
  exact (eq_div_iff (by positivity : (k.factorial : ℝ) ≠ 0)).mpr hi

private theorem firstAtomGaussianErrorConstant_ge : 24 ≤ firstAtomGaussianErrorConstant := by
  have he : 1 ≤ Real.exp (4 + 2 * Real.exp 2) := Real.one_le_exp (by positivity)
  calc
    (24 : ℝ) ≤ 24 + 10 * Real.exp 2 := by linarith only [Real.exp_pos (2 : ℝ)]
    _ ≤ firstAtomGaussianErrorConstant := le_mul_of_one_le_left (by positivity) he

/-- An explicit order-dependent scale forces strict positivity of the actual signed moment. -/
theorem firstAtom_signed_moment_pos_of_scale {x : ℝ} (k : ℕ)
    (hscale : firstAtomGaussianErrorConstant * (k.factorial : ℝ) <
      thetaCuspSingleAtomReflectionScale 1 x) :
    0 < (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hfac2 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by
    exact_mod_cast (2 * k).factorial_pos
  have hfac1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ k.factorial by have h := k.factorial_pos; omega)
  have hD : firstAtomGaussianErrorConstant ≤
      firstAtomGaussianErrorConstant * (k.factorial : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac1
      firstAtomGaussianErrorConstant_pos.le
  have hq : 3 ≤ q := by
    dsimp [q]
    linarith only [hscale, hD, firstAtomGaussianErrorConstant_ge]
  have hqp : 0 < q := by linarith only [hq]
  have herr : ((2 * k).factorial : ℝ) * firstAtomGaussianErrorConstant / q <
      ((2 * k).factorial : ℝ) / (k.factorial : ℝ) := by
    apply (div_lt_div_iff₀ hqp hfac).mpr
    have hm := mul_lt_mul_of_pos_left hscale hfac2
    change ((2 * k).factorial : ℝ) * (firstAtomGaussianErrorConstant *
      (k.factorial : ℝ)) < ((2 * k).factorial : ℝ) * q at hm
    nlinarith only [hm]
  have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ k := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 4) k
  have hgamma : ((2 * k).factorial : ℝ) / (k.factorial : ℝ) ≤ gaussianMoment k := by
    rw [gaussianMoment_eq_factorial]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hfac2.le hpow) hfac.le
  have hbound := abs_le.mp (firstAtomScaledEvenJet_gaussian_error_le hq k)
  have hscaled : 0 < thetaCuspFirstAtomScaledEvenJet k x := by
    have hlow := hbound.1
    change -(((2 * k).factorial : ℝ) * firstAtomGaussianErrorConstant / q) ≤
      thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k at hlow
    linarith only [hlow, herr, hgamma]
  have hden : 0 < thetaCuspSourceTerm x 1 ^ 2 * q ^ k :=
    mul_pos (firstAtom_mass_pos hq) (pow_pos hqp k)
  change 0 < (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x /
    (thetaCuspSourceTerm x 1 ^ 2 * q ^ k) at hscaled
  exact (div_pos_iff_of_pos_right hden).mp hscaled

/-- The least negative order exceeds every order admitted by the explicit factorial scale. -/
theorem firstAtomNegativeOrder_gt_of_scale {x : ℝ} (K : ℕ)
    (hscale : firstAtomGaussianErrorConstant * (K.factorial : ℝ) <
      thetaCuspSingleAtomReflectionScale 1 x) :
    K < firstAtomNegativeOrder x := by
  by_contra h
  have hk : firstAtomNegativeOrder x ≤ K := le_of_not_gt h
  have hf : ((firstAtomNegativeOrder x).factorial : ℝ) ≤ (K.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hk
  have hsmall := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hf firstAtomGaussianErrorConstant_pos.le) hscale
  exact not_lt_of_ge (firstAtom_signed_moment_pos_of_scale (firstAtomNegativeOrder x) hsmall).le
    (firstAtomNegativeOrder_spec x)

/-- An explicit center at which every moment through the specified order is positive. -/
def firstAtomGaussianHorizon (K : ℕ) : ℝ :=
  max 0 (Real.log ((firstAtomGaussianErrorConstant * (K.factorial : ℝ) + 1) / Real.pi) / 2)

/-- The factorial horizon gives a simultaneous lower bound for the escaping negative order. -/
theorem firstAtomNegativeOrder_gt_of_horizon (K : ℕ) {x : ℝ}
    (hx : firstAtomGaussianHorizon K ≤ x) :
    K < firstAtomNegativeOrder x := by
  have hA : 0 < firstAtomGaussianErrorConstant * (K.factorial : ℝ) + 1 := by
    have hD := firstAtomGaussianErrorConstant_pos
    positivity
  have hxlog : Real.log ((firstAtomGaussianErrorConstant * (K.factorial : ℝ) + 1) /
      Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0
      (Real.log ((firstAtomGaussianErrorConstant * (K.factorial : ℝ) + 1) / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos hA Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hq : firstAtomGaussianErrorConstant * (K.factorial : ℝ) + 1 ≤
      thetaCuspSingleAtomReflectionScale 1 x := by
    simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
      mul_div_cancel₀ _ Real.pi_ne_zero] using hm
  apply firstAtomNegativeOrder_gt_of_scale K
  linarith only [hq]

#print axioms firstAtomGaussianKernel_error_le
#print axioms firstAtomNormalizedRotatedPair_error_le
#print axioms firstAtomScaledEvenJet_gaussian_error_le
#print axioms firstAtom_signed_moment_pos_of_scale
#print axioms firstAtomNegativeOrder_gt_of_scale
#print axioms firstAtomNegativeOrder_gt_of_horizon

end GaloisForLFunctions.CompletedArithmeticForms
