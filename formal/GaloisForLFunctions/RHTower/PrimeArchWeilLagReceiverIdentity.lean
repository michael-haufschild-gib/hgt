import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.WeilLagFunctionHerglotz

/-!
# Exact prime-archimedean and Weil-lag resolvent coordinates

Functional-equation pairing gives an explicit identity between the actual relative
resolvent trace and the weighted lag-pole series on their common half-plane. The native
prime-archimedean source satisfies the same identity without RH or positivity premises.
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set
noncomputable section
namespace RHTower


theorem lagPole_eq_I_mul_xiSpectralPoint (q : XiZeroCopy) :
    lagPole q = Complex.I * xiSpectralPoint q := by
  unfold lagPole xiSpectralPoint
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem lagPole_reflect (q : XiZeroCopy) :
    lagPole (xiZeroCopyReflectEquiv q) = -lagPole q := by
  rw [lagPole_eq_I_mul_xiSpectralPoint, xiSpectralPoint_reflect,
    mul_neg, ← lagPole_eq_I_mul_xiSpectralPoint]

theorem lagWeight_eq_pole (q : XiZeroCopy) :
    lagWeight q = 1 / ((1 / 4 : ℂ) - lagPole q ^ 2) := by
  unfold lagWeight lagPole
  congr 1
  ring

theorem lagWeight_reflect (q : XiZeroCopy) :
    lagWeight (xiZeroCopyReflectEquiv q) = lagWeight q := by
  rw [lagWeight_eq_pole, lagPole_reflect, neg_sq, ← lagWeight_eq_pole]

theorem XiC_ne_zero_at_lagCoordinate {s : ℂ} (hs : 1 / 2 < s.re) : XiC (s * -Complex.I) ≠ 0 := by
  intro hz
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
  have he : lagPole q = s := by
    rw [lagPole_eq_I_mul_xiSpectralPoint, hq]
    ring_nf
    simp [Complex.I_sq]
  have h := lagPole_re_lt_half q
  rw [he] at h
  linarith

theorem reciprocalSquareResolventTerm_lagCoordinate {s : ℂ} (hs : 1 / 2 < s.re)
    (q : XiZeroCopy) :
    xiReciprocalSquareResolventTerm (s * -Complex.I) q = 1 / (s ^ 2 - lagPole q ^ 2) := by
  have hp : lagPole q ≠ 0 := xiZeroCopy_sub_half_ne_zero q
  have hminus : s - lagPole q ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    linarith [lagPole_re_lt_half q]
  have hplus : s + lagPole q ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at he
    linarith [lagPole_re_gt q]
  have hsq : s ^ 2 - lagPole q ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hrev : -s ^ 2 + lagPole q ^ 2 ≠ 0 := by
    intro h
    apply hsq
    linear_combination -h
  have he : xiSpectralPoint q = lagPole q * -Complex.I := rfl
  rw [xiReciprocalSquareResolventTerm, xiZeroCopyReciprocalSquare, he]
  field_simp [hp, hsq, Complex.I_ne_zero]
  simp [Complex.I_sq]
  ring_nf
  field_simp [hrev]
  ring

theorem lag_resolvent_pair_identity {s : ℂ} (hs : 1 / 2 < s.re) (q : XiZeroCopy) :
    2 * s * xiReciprocalSquareResolventTerm (s * -Complex.I) q =
      ((1 / 4 : ℂ) - s ^ 2) *
        (lagWeight q / (s - lagPole q) +
          lagWeight (xiZeroCopyReflectEquiv q) / (s - lagPole (xiZeroCopyReflectEquiv q))) +
      2 * s * lagWeight q := by
  have hm : s - lagPole q ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    linarith [lagPole_re_lt_half q]
  have hp : s + lagPole q ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at he
    linarith [lagPole_re_gt q]
  have hw : (1 / 4 : ℂ) - lagPole q ^ 2 ≠ 0 := by
    have he : (1 / 4 : ℂ) - lagPole q ^ 2 = (q.1 : ℂ) * (1 - (q.1 : ℂ)) := by
      unfold lagPole
      ring
    rw [he]
    exact mul_ne_zero (xiZeroCopy_ne_zero q) (xiZeroCopy_one_sub_ne_zero q)
  have hsq : s ^ 2 - lagPole q ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hp hm
  rw [reciprocalSquareResolventTerm_lagCoordinate hs, lagWeight_reflect, lagPole_reflect,
    sub_neg_eq_add, lagWeight_eq_pole]
  have hw4 : (1 : ℂ) - lagPole q ^ 2 * 4 ≠ 0 := by
    intro h
    apply hw
    linear_combination h / 4
  field_simp [hm, hp, hw, hsq]
  ring_nf

/-- Explicit unconditioned PA-divisor/WL-Laplace coordinate identity in their common half-plane. -/
theorem xiRelativeResolventTrace_eq_lagPoleSeries {s : ℂ} (hs : 1 / 2 < s.re) :
    xiRelativeResolventTrace (s * -Complex.I) = Complex.I *
      (((1 / 4 : ℂ) - s ^ 2) * lagPoleSeries s + s * ∑' q : XiZeroCopy, lagWeight q) := by
  have hf := summable_lagTerm_of_lt_re (fun q => (lagPole_re_lt_half q).le) hs
  have hfr : Summable (fun q : XiZeroCopy => lagWeight (xiZeroCopyReflectEquiv q) /
      (s - lagPole (xiZeroCopyReflectEquiv q))) := (xiZeroCopyReflectEquiv.summable_iff).mpr hf
  have hw : Summable lagWeight := summable_inv_mul_one_sub
  have he : (∑' q : XiZeroCopy, 2 * s * xiReciprocalSquareResolventTerm (s * -Complex.I) q) =
      (∑' q : XiZeroCopy, (((1 / 4 : ℂ) - s ^ 2) *
        (lagWeight q / (s - lagPole q) + lagWeight (xiZeroCopyReflectEquiv q) /
          (s - lagPole (xiZeroCopyReflectEquiv q))) + 2 * s * lagWeight q)) :=
    tsum_congr (lag_resolvent_pair_identity hs)
  rw [tsum_mul_left,
    Summable.tsum_add ((hf.add hfr).mul_left ((1 / 4 : ℂ) - s ^ 2)) (hw.mul_left (2 * s)),
    tsum_mul_left, Summable.tsum_add hf hfr,
    xiZeroCopyReflectEquiv.tsum_eq (fun q => lagWeight q / (s - lagPole q)),
    tsum_mul_left] at he
  rw [xiRelativeResolventTrace_eq_reciprocalSquareResolvent (XiC_ne_zero_at_lagCoordinate hs)]
  unfold lagPoleSeries
  linear_combination (Complex.I / 2) * he

/-- The actual prime--archimedean source uses the same coordinate wherever its natural source
formula is defined; no positivity or RH premise enters this transport. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_lagPoleSeries {s : ℂ}
    (hs : 1 / 2 < s.re) :
    continuedPrimeArchSourceRelativeTrace (s * -Complex.I) = Complex.I *
      (((1 / 4 : ℂ) - s ^ 2) * lagPoleSeries s + s * ∑' q : XiZeroCopy, lagWeight q) := by
  have he : (1 / 2 : ℂ) + (s * -Complex.I) * Complex.I = 1 / 2 + s := by
    ring_nf
    simp [Complex.I_sq]
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace,
    xiRelativeResolventTrace_eq_lagPoleSeries hs]
  · rw [he]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  · rw [he]
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hr
    linarith
  · rw [he]
    apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith

end RHTower

end
