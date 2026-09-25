import GaloisForLFunctions.RHTower.LiEvenCrossCassiniRadialEulerBridge

open Complex

namespace RHTower

private theorem re_node_div_shift_sq_pos {z : ℂ} {y : ℝ}
    (hz : 0 < z.re) (hy : 0 ≤ y) :
    0 < (z / (z + (y : ℂ)) ^ (2 : ℕ)).re := by
  let a : ℝ := z.re
  let b : ℝ := z.im
  let t : ℝ := a + y
  let d : ℝ := t ^ (2 : ℕ) + b ^ (2 : ℕ)
  have ht : 0 < t := by dsimp [t, a]; linarith
  have hd : 0 < d := by
    dsimp [d]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos ht) (sq_nonneg b)
  have hre : ((z + (y : ℂ)) ^ (2 : ℕ)).re = t ^ (2 : ℕ) - b ^ (2 : ℕ) := by
    simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.ofReal_re]
    dsimp [t, b, a]
    ring
  have him : ((z + (y : ℂ)) ^ (2 : ℕ)).im = 2 * t * b := by
    simp only [pow_two, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    dsimp [t, b, a]
    ring
  have hnorm0 : Complex.normSq (z + (y : ℂ)) = d := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    dsimp [d, t, b, a]
    ring
  have hnorm : Complex.normSq ((z + (y : ℂ)) ^ (2 : ℕ)) = d ^ (2 : ℕ) := by
    rw [pow_two, Complex.normSq_mul, hnorm0]
    ring
  have hvalue :
      (z / (z + (y : ℂ)) ^ (2 : ℕ)).re =
        (a * d + 2 * y * b ^ (2 : ℕ)) / d ^ (2 : ℕ) := by
    rw [Complex.div_re, hre, him, hnorm]
    dsimp [d, t, a, b]
    ring
  rw [hvalue]
  apply div_pos _ (pow_pos hd 2)
  have hmain : 0 < a * d := mul_pos hz hd
  have hrest : 0 ≤ 2 * y * b ^ (2 : ℕ) := by positivity
  linarith

theorem liEvenCrossRadialDilationResponse_pos {y : ℝ} (hy : 0 < y) :
    0 < liEvenCrossRadialDilationResponse y := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ)
  have hsum : Summable f := by
    simpa only [f] using summable_xiSquaredNode_div_add_shift_sq hy.le
  have hsumRe : Summable (fun q : XiZeroCopy => (f q).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hpos (q : XiZeroCopy) : 0 < (f q).re :=
    re_node_div_shift_sq_pos (xiSquaredNode_re_pos q) hy.le
  let q0 : XiZeroCopy := Classical.choice (inferInstance : Nonempty XiZeroCopy)
  have htotal : 0 < ∑' q : XiZeroCopy, (f q).re :=
    hsumRe.tsum_pos (fun q => (hpos q).le) q0 (hpos q0)
  have hresponse :
      liEvenCrossRadialDilationResponse y =
        y * ∑' q : XiZeroCopy, (f q).re := by
    rw [liEvenCrossRadialDilationResponse]
    have hnode := tsum_xiSquaredNode_div_add_shift_sq_eq_shiftedMoment_response hy.le
    change y * ((xiShiftedReciprocalMoment y 0).re -
      y * (xiShiftedReciprocalMoment y 1).re) = _
    rw [← Complex.re_tsum hsum]
    rw [show (∑' q : XiZeroCopy, f q) =
        xiShiftedReciprocalMoment y 0 -
          (y : ℂ) * xiShiftedReciprocalMoment y 1 by exact hnode]
    simp [Complex.sub_re, Complex.mul_re]
  rw [hresponse]
  exact mul_pos hy htotal

end RHTower
