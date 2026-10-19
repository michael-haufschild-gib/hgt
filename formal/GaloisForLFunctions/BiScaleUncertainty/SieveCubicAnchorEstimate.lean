import GaloisForLFunctions.BiScaleUncertainty.SieveRawMomentPerturbation

/-! Scalar estimates for cubic recovery from a nonvanishing upper coordinate and raw quintic/sixth errors. -/

namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor
set_option autoImplicit false

private theorem abs_sixth (x : ℝ) : |x|^6 = x^6 := by
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x^6)]

private theorem large_magnitude_error (x y ε : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hlarge : 1 ≤ x ∨ 1 ≤ y)
    (h : |x^6-y^6| ≤ ε) : |x-y| ≤ ε := by
  have step (u v : ℝ) (hu : 1 ≤ u) (hv : 0 ≤ v) (hvu : v ≤ u)
      (he : |u^6-v^6| ≤ ε) : u-v ≤ ε := by
    have hp := one_le_pow₀ hu (n := 5)
    have hm := pow_le_pow_left₀ hv hvu 5
    have h₁ := mul_nonneg hv (sub_nonneg.mpr hm)
    have h₂ := mul_nonneg (sub_nonneg.mpr hvu) (sub_nonneg.mpr hp)
    have h₃ := (le_abs_self (u^6-v^6)).trans he
    nlinarith only [h₁, h₂, h₃]
  rcases le_total y x with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact step x y (hlarge.elim id (fun hh => hh.trans hxy)) hy hxy h
  · rw [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub]
    exact step y x (hlarge.elim (fun hh => hh.trans hyx) id) hx hyx
      (by simpa only [abs_sub_comm] using h)

private theorem square_error (X Y ε : ℝ) (hX : 1 ≤ X^2) (hY : 1 ≤ Y^2)
    (h : |X^6-Y^6| ≤ ε) : |X^2-Y^2| ≤ ε := by
  let A := X^2
  let B := Y^2
  have hA : 1 ≤ A := hX
  have hB : 1 ≤ B := hY
  have hfactor : 1 ≤ A^2+A*B+B^2 := by
    nlinarith [mul_nonneg (show 0 ≤ A by linarith) (show 0 ≤ B by linarith)]
  have he : |(A-B)*(A^2+A*B+B^2)| ≤ ε := by
    convert h using 1
    dsimp [A, B]
    congr 1
    ring
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ A^2+A*B+B^2)] at he
  have hm := mul_nonneg (abs_nonneg (A-B)) (sub_nonneg.mpr hfactor)
  change |A-B| ≤ ε
  nlinarith only [hm, he]

private theorem cube_distance (x y : ℝ) : |x-y|^3 ≤ 4*|x^3-y^3| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (x+y)),
      le_abs_self (x^3-y^3)]
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (x+y)),
      neg_le_abs (x^3-y^3)]

private theorem opposite_error (x y X Y δ : ℝ) (hx : 0 ≤ x) (hy : y ≤ 0)
    (hX : 1 ≤ X^2) (hY : 1 ≤ Y^2) (hδ : 0 ≤ δ)
    (h : |x^3*X^2-y^3*Y^2| ≤ δ^3) : |x-y| ≤ 2*δ := by
  have hx3 : 0 ≤ x^3 := pow_nonneg hx _
  have hy3 : 0 ≤ (-y)^3 := pow_nonneg (neg_nonneg.mpr hy) _
  have hX0 : 0 ≤ X^2 := sq_nonneg X
  have hY0 : 0 ≤ Y^2 := sq_nonneg Y
  have he := (le_abs_self (x^3*X^2-y^3*Y^2)).trans h
  have hax := mul_nonneg hx3 (sub_nonneg.mpr hX)
  have hay := mul_nonneg hy3 (sub_nonneg.mpr hY)
  have hxpow : x^3 ≤ δ^3 := by
    nlinarith only [he, hax, mul_nonneg hy3 hY0]
  have hypow : (-y)^3 ≤ δ^3 := by
    nlinarith only [he, hay, mul_nonneg hx3 hX0]
  have hxd := (pow_le_pow_iff_left₀ hx hδ (by decide : 3 ≠ 0)).mp hxpow
  have hyd := (pow_le_pow_iff_left₀ (neg_nonneg.mpr hy) hδ
    (by decide : 3 ≠ 0)).mp hypow
  rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
  linarith

/-- A nonvanishing upper mode converts a noisy quintic product into cubic control. -/
theorem lower_error (x y X Y δ : ℝ) (hX : 1 ≤ |X|) (hY : 1 ≤ |Y|)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : |X^6-Y^6| ≤ δ^3) (hm : |x^6-y^6| ≤ δ^3)
    (hc : |x^3*X^2-y^3*Y^2| ≤ δ^3) : |x-y| ≤ 2*δ := by
  have hX2 : 1 ≤ X^2 := by
    simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hX 2
  have hY2 : 1 ≤ Y^2 := by
    simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY 2
  by_cases hsmall : |x| ≤ 1 ∧ |y| ≤ 1
  · have hsq := square_error X Y (δ^3) hX2 hY2 ha
    have hycube : |y^3| ≤ 1 := by
      simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg y) hsmall.2 3
    have hrem : |y^3*Y^2-y^3*X^2| ≤ δ^3 := by
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ 1 * |Y^2-X^2| :=
          mul_le_mul_of_nonneg_right hycube (abs_nonneg _)
        _ ≤ δ^3 := by simpa only [one_mul, abs_sub_comm] using hsq
    have hprod : |x^3-y^3| * X^2 ≤ 2*δ^3 := calc
      _ = |x^3*X^2-y^3*X^2| := by
        rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg X)]
      _ ≤ |x^3*X^2-y^3*Y^2|+|y^3*Y^2-y^3*X^2| := abs_sub_le _ _ _
      _ ≤ δ^3+δ^3 := add_le_add hc hrem
      _ = _ := by ring
    have hcube : |x^3-y^3| ≤ 2*δ^3 := by
      have hz := mul_nonneg (abs_nonneg (x^3-y^3)) (sub_nonneg.mpr hX2)
      nlinarith only [hprod, hz]
    apply (pow_le_pow_iff_left₀ (abs_nonneg (x-y))
      (by positivity : 0 ≤ 2*δ) (by decide : 3 ≠ 0)).mp
    nlinarith only [cube_distance x y, hcube]
  · have hlarge : 1 ≤ |x| ∨ 1 ≤ |y| := by
      by_contra hn
      push Not at hn
      exact hsmall ⟨hn.1.le, hn.2.le⟩
    have hmag : abs (|x|-|y|) ≤ δ^3 :=
      large_magnitude_error |x| |y| (δ^3) (abs_nonneg _) (abs_nonneg _) hlarge
        (by simpa only [abs_sixth] using hm)
    have hδ3 : δ^3 ≤ δ := by
      have hh := mul_nonneg hδ (sub_nonneg.mpr hδ1)
      have hh' := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ1)
      nlinarith only [hh, hh']
    rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · simpa only [abs_of_nonneg hx, abs_of_nonneg hy] using hmag.trans
        (hδ3.trans (by linarith : δ ≤ 2*δ))
    · exact opposite_error x y X Y δ hx hy hX2 hY2 hδ hc
    · have hh := opposite_error y x Y X δ hy hx hY2 hX2 hδ
        (by simpa only [abs_sub_comm] using hc)
      simpa only [abs_sub_comm] using hh
    · have hh : abs (|x|-|y|) = |x-y| := by
        rw [abs_of_nonpos hx, abs_of_nonpos hy]
        rw [show -x-(-y) = y-x by ring, abs_sub_comm y x]
      rw [hh] at hmag
      exact hmag.trans (hδ3.trans (by linarith : δ ≤ 2*δ))

/-- A large top coordinate has a Lipschitz magnitude inverse, with its two orientations explicit. -/
theorem upper_error (x y ε : ℝ) (hx : 1 ≤ |x|)
    (h : |x^6-y^6| ≤ ε) : |y-x| ≤ ε ∨ |y+x| ≤ ε := by
  have hm : abs (|x|-|y|) ≤ ε :=
    large_magnitude_error |x| |y| ε (abs_nonneg _) (abs_nonneg _) (Or.inl hx)
      (by simpa only [abs_sixth] using h)
  rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
  · left
    simpa only [abs_of_nonneg hx0, abs_of_nonneg hy0, abs_sub_comm] using hm
  · right
    simpa only [abs_of_nonneg hx0, abs_of_nonpos hy0, sub_neg_eq_add, add_comm] using hm
  · right
    rw [abs_of_nonpos hx0, abs_of_nonneg hy0] at hm
    rwa [show -x-y = -(y+x) by ring, abs_neg] at hm
  · left
    rw [abs_of_nonpos hx0, abs_of_nonpos hy0] at hm
    rwa [show -x-(-y) = y-x by ring] at hm

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor
