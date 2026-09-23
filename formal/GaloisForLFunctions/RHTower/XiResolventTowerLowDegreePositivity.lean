import GaloisForLFunctions.RHTower.XiWeilResolventChartDictionary
import GaloisForLFunctions.RHTower.XiResolventHankelLadder
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment

/-!
# Low-degree positivity of the resolvent moment tower

The formalized height gap `2 < (Im ρ)²` beats the strip bound `(Re ρ − 1/2)² < 1/4`: every
shifted squared spectral point `α² + X` lies strictly inside the 45° cone `|Im| < Re` for
every shift `X ≥ 0`, and satisfies the 30° cone inequality `Re² > 3·Im²` once `X ≥ 3/4`.
Hence not only the zeroth but also the **first** resolvent moment is termwise strictly
positive unconditionally, and the **second** is for `X ≥ 3/4` — explicit algebraic cone laws,
no Gamma averaging.

Through the power-kernel dictionary the same positivity transfers to the Weil chart: the
diagonal Weil values of the squared and cubed imaginary-parameter Cauchy tests are strictly
positive families.  Degrees `0, 1, 2` of the arithmetic moment tower are thereby closed; the
first genuinely open cancellation question starts at degree `3` at small shift, where the
cone angle `π/8` would require height beyond the formalized gap.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Cone laws for the shifted squared spectral point -/

/-- **The 45° cone law.**  The height gap and the strip force every shifted squared spectral
point into the open right 45° cone. -/
theorem xiSpectralSq_add_abs_im_lt_re {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    |(xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im| < (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re := by
  have him : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im =
      2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
    simp [sq, Complex.add_im, Complex.mul_im]
    ring
  have hre : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re =
      (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X := by
    simp [sq, Complex.add_re, Complex.mul_re]
  have hγ2 : 2 < (xiSpectralPoint q).re ^ (2 : ℕ) := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb : |(xiSpectralPoint q).im| < 1 / 2 := abs_xiSpectralPoint_im_lt_half q
  have hγabs : 2 < |(xiSpectralPoint q).re| ^ (2 : ℕ) := by rwa [sq_abs]
  have hbabs : |(xiSpectralPoint q).im| ^ (2 : ℕ) < 1 / 4 := by
    nlinarith [abs_nonneg (xiSpectralPoint q).im]
  have htc : 2 * |(xiSpectralPoint q).re| * |(xiSpectralPoint q).im| ≤
      |(xiSpectralPoint q).re| := by
    nlinarith [abs_nonneg (xiSpectralPoint q).re, abs_nonneg (xiSpectralPoint q).im]
  have hkey : 2 * |(xiSpectralPoint q).re| * |(xiSpectralPoint q).im| <
      (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X := by
    have h12 : 12 * ((xiSpectralPoint q).re ^ (2 : ℕ) - |(xiSpectralPoint q).re| - 1 / 4) > 0 := by
      nlinarith [sq_nonneg (2 * |(xiSpectralPoint q).re| - 3), hγabs,
        sq_abs (xiSpectralPoint q).re]
    have hbsq : (xiSpectralPoint q).im ^ (2 : ℕ) < 1 / 4 := by
      rwa [← sq_abs]
    nlinarith [htc, hbsq, hX]
  have habs : |2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im| =
      2 * |(xiSpectralPoint q).re| * |(xiSpectralPoint q).im| := by
    rw [abs_mul, abs_mul, abs_two]
  rw [him, hre, abs_lt]
  constructor
  · have hlow : -(2 * |(xiSpectralPoint q).re| * |(xiSpectralPoint q).im|) ≤
        2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
      rw [← habs]
      exact neg_abs_le _
    linarith
  · have hup : 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im ≤
        2 * |(xiSpectralPoint q).re| * |(xiSpectralPoint q).im| := by
      rw [← habs]
      exact le_abs_self _
    linarith

/-- **The 30° cone inequality at shift `≥ 3/4`**: the squared real part strictly dominates
three times the squared imaginary part. -/
theorem xiSpectralSq_add_re_sq_gt_three_im_sq {X : ℝ} (hX : 3 / 4 ≤ X) (q : XiZeroCopy) :
    3 * (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im ^ (2 : ℕ) <
      (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re ^ (2 : ℕ) := by
  have him : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im =
      2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
    simp [sq, Complex.add_im, Complex.mul_im]
    ring
  have hre : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re =
      (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X := by
    simp [sq, Complex.add_re, Complex.mul_re]
  have hγ2 : 2 < (xiSpectralPoint q).re ^ (2 : ℕ) := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb : |(xiSpectralPoint q).im| < 1 / 2 := abs_xiSpectralPoint_im_lt_half q
  have hbsq : (xiSpectralPoint q).im ^ (2 : ℕ) < 1 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (xiSpectralPoint q).im]
  rw [him, hre]
  nlinarith [hγ2, hbsq, hX, sq_nonneg ((xiSpectralPoint q).re ^ (2 : ℕ) - 2),
    sq_nonneg ((xiSpectralPoint q).re * (xiSpectralPoint q).im),
    mul_pos (lt_trans zero_lt_two hγ2) (lt_trans zero_lt_two hγ2)]

/-! ## Termwise positivity at degrees one and two -/

/-- **Degree-one termwise positivity**: the square of every resolvent coordinate has strictly
positive real part, unconditionally. -/
theorem xiResolventPoint_sq_re_pos {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    0 < (xiResolventPoint X q ^ (2 : ℕ)).re := by
  rw [xiResolventPoint, inv_pow, Complex.inv_re]
  apply div_pos
  · have hcone := xiSpectralSq_add_abs_im_lt_re hX q
    have hsq : ((xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ)).re =
        (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re ^ (2 : ℕ) -
          (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im ^ (2 : ℕ) := by
      simp [sq, Complex.mul_re]
    rw [hsq]
    nlinarith [abs_nonneg (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im,
      sq_abs (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im]
  · exact Complex.normSq_pos.mpr (pow_ne_zero _ (xiSpectralSq_add_ofReal_ne_zero hX q))

/-- **Degree-two termwise positivity at shift `≥ 3/4`**: the cube of every resolvent
coordinate has strictly positive real part. -/
theorem xiResolventPoint_cube_re_pos {X : ℝ} (hX : 3 / 4 ≤ X) (q : XiZeroCopy) :
    0 < (xiResolventPoint X q ^ (3 : ℕ)).re := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  rw [xiResolventPoint, inv_pow, Complex.inv_re]
  apply div_pos
  · have hcone := xiSpectralSq_add_re_sq_gt_three_im_sq hX q
    have hrepos := xiSpectralSq_add_ofReal_re_pos hX0 q
    have hcube : ((xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (3 : ℕ)).re =
        (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re ^ (3 : ℕ) -
          3 * (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re *
            (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im ^ (2 : ℕ) := by
      simp [pow_succ, Complex.mul_re, Complex.mul_im]
      ring
    rw [hcube]
    nlinarith [hrepos, hcone]
  · exact Complex.normSq_pos.mpr (pow_ne_zero _ (xiSpectralSq_add_ofReal_ne_zero hX0 q))

/-! ## The moments -/

/-- **The first resolvent moment is strictly positive**, unconditionally. -/
theorem xiResolventMoment_one_re_pos {X : ℝ} (hX : 0 ≤ X) :
    0 < (xiResolventMoment 1 X).re := by
  rw [xiResolventMoment, Complex.re_tsum (summable_xiResolventPoint_pow hX 1)]
  have hre : ∀ q : XiZeroCopy, 0 < (xiResolventPoint X q ^ (1 + 1)).re := by
    intro q
    exact xiResolventPoint_sq_re_pos hX q
  have hsumre : Summable (fun q : XiZeroCopy =>
      (xiResolventPoint X q ^ (1 + 1)).re) := by
    simpa only [Function.comp_apply] using!
      (summable_xiResolventPoint_pow hX 1).map Complex.reCLM Complex.reCLM.continuous
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  calc (0 : ℝ) < (xiResolventPoint X q₀ ^ (1 + 1)).re := hre q₀
    _ ≤ ∑' q : XiZeroCopy, (xiResolventPoint X q ^ (1 + 1)).re :=
        hsumre.le_tsum q₀ fun q _ => (hre q).le

/-- **The second resolvent moment is strictly positive for shifts `≥ 3/4`.** -/
theorem xiResolventMoment_two_re_pos {X : ℝ} (hX : 3 / 4 ≤ X) :
    0 < (xiResolventMoment 2 X).re := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  rw [xiResolventMoment, Complex.re_tsum (summable_xiResolventPoint_pow hX0 2)]
  have hre : ∀ q : XiZeroCopy, 0 < (xiResolventPoint X q ^ (2 + 1)).re := by
    intro q
    exact xiResolventPoint_cube_re_pos hX q
  have hsumre : Summable (fun q : XiZeroCopy =>
      (xiResolventPoint X q ^ (2 + 1)).re) := by
    simpa only [Function.comp_apply] using!
      (summable_xiResolventPoint_pow hX0 2).map Complex.reCLM Complex.reCLM.continuous
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  calc (0 : ℝ) < (xiResolventPoint X q₀ ^ (2 + 1)).re := hre q₀
    _ ≤ ∑' q : XiZeroCopy, (xiResolventPoint X q ^ (2 + 1)).re :=
        hsumre.le_tsum q₀ fun q _ => (hre q).le

/-! ## Transfer to the Weil chart -/

/-- **The power-kernel dictionary**: the Weil pair summand of the `(n+1)`-th power of the
imaginary-parameter Cauchy test is the `(n+1)`-th power of the resolvent coordinate. -/
theorem xiWeilPowerKernel_pair_term_eq (t : ℝ) (n : ℕ) (q : XiZeroCopy) :
    (xiWeilCauchyTest (-(t : ℂ) * Complex.I) (xiSpectralPoint q)) ^ (n + 1) *
      xiWeilSharp (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (n + 1))
        (xiSpectralPoint q) =
    xiResolventPoint (t ^ (2 : ℕ)) q ^ (n + 1) := by
  have hsharp : xiWeilSharp
      (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (n + 1))
      (xiSpectralPoint q) =
        (xiWeilSharp (xiWeilCauchyTest (-(t : ℂ) * Complex.I))
          (xiSpectralPoint q)) ^ (n + 1) := by
    rw [xiWeilSharp, xiWeilSharp, map_pow]
  rw [hsharp, ← mul_pow, xiWeilCauchyTest_pair_term_eq_resolventPoint]

/-- The diagonal Weil value of the `(n+1)`-th power kernel is the `n`-th resolvent moment. -/
theorem xiWeilPolarization_powerKernel_eq_moment (t : ℝ) (n : ℕ) :
    xiWeilPolarization
        (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (n + 1))
        (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (n + 1)) =
      xiResolventMoment n (t ^ (2 : ℕ)) := by
  rw [xiWeilPolarization, xiResolventMoment]
  exact tsum_congr fun q => xiWeilPowerKernel_pair_term_eq t n q

/-- **The squared Cauchy family is a strictly positive Weil-diagonal family**,
unconditionally. -/
theorem xiWeilPolarization_squaredKernel_re_pos (t : ℝ) :
    0 < (xiWeilPolarization
        (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (2 : ℕ))
        (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (2 : ℕ))).re := by
  have h := xiWeilPolarization_powerKernel_eq_moment t 1
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [h]
  exact xiResolventMoment_one_re_pos (sq_nonneg t)

/-- **The cubed Cauchy family is a strictly positive Weil-diagonal family** for
`t² ≥ 3/4`. -/
theorem xiWeilPolarization_cubedKernel_re_pos {t : ℝ} (ht : 3 / 4 ≤ t ^ (2 : ℕ)) :
    0 < (xiWeilPolarization
        (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (3 : ℕ))
        (fun a => (xiWeilCauchyTest (-(t : ℂ) * Complex.I) a) ^ (3 : ℕ))).re := by
  have h := xiWeilPolarization_powerKernel_eq_moment t 2
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h
  rw [h]
  exact xiResolventMoment_two_re_pos ht

end

end RHTower
