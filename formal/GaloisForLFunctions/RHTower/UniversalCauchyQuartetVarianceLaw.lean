import GaloisForLFunctions.RHTower.XiReciprocalSquareFixedCauchySource

/-!
# Universal one-probe Cauchy quartet-variance law

The fixed Xi Cauchy probe is an instance of a divisor-independent identity.  For any countable
family closed under negation and conjugation, the imaginary reciprocal-square Cauchy response is
one quadrant scalar times a sum of nonnegative quartet variances.  No zero-location or positivity
hypothesis enters the identity.
-/

open Complex

namespace RHTower

noncomputable section

/-- Universal imaginary reciprocal-square contribution of one spectral point. -/
def cauchyQuartetOrientationTerm (z a : ℂ) : ℝ :=
  xiReciprocalSquareCauchySpectralTerm z a

/-- Universal nonnegative variance of one conjugation--negation quartet. -/
def cauchyQuartetVariance (z a : ℂ) : ℝ :=
  xiReciprocalSquareCauchyQuartetVariance z a

/-- Exact universal algebraic identity on one conjugation--negation quartet. -/
theorem cauchyQuartetOrientationTerm_sum_orbit
    (z a : ℂ)
    (ha : a ≠ 0) (haz : a - z ≠ 0)
    (hcaz : (starRingEnd ℂ) a - z ≠ 0)
    (hapz : a + z ≠ 0)
    (hcapz : (starRingEnd ℂ) a + z ≠ 0) :
    cauchyQuartetOrientationTerm z a +
        cauchyQuartetOrientationTerm z ((starRingEnd ℂ) a) +
        cauchyQuartetOrientationTerm z (-a) +
        cauchyQuartetOrientationTerm z (-(starRingEnd ℂ) a) =
      64 * z.re * z.im * cauchyQuartetVariance z a := by
  unfold cauchyQuartetOrientationTerm cauchyQuartetVariance
    xiReciprocalSquareCauchyQuartetVariance
  convert xiReciprocalSquareCauchySpectralTerm_quartet
    z a ha haz hcaz hapz hcapz using 1
  ring

/-- Every universal quartet variance is nonnegative. -/
theorem cauchyQuartetVariance_nonneg (z a : ℂ) :
    0 ≤ cauchyQuartetVariance z a := by
  unfold cauchyQuartetVariance xiReciprocalSquareCauchyQuartetVariance
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
          (Complex.normSq_nonneg _))
        (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _))

/-- A regular quartet variance vanishes exactly on the union of the two coordinate axes. -/
theorem cauchyQuartetVariance_eq_zero_iff
    {z a : ℂ}
    (ha : a ≠ 0) (haz : a - z ≠ 0)
    (hcaz : (starRingEnd ℂ) a - z ≠ 0)
    (hapz : a + z ≠ 0)
    (hcapz : (starRingEnd ℂ) a + z ≠ 0) :
    cauchyQuartetVariance z a = 0 ↔ a.re = 0 ∨ a.im = 0 := by
  have hden :
      Complex.normSq a ^ (2 : ℕ) *
          Complex.normSq (a - z) *
          Complex.normSq ((starRingEnd ℂ) a - z) *
          Complex.normSq (a + z) *
          Complex.normSq ((starRingEnd ℂ) a + z) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (pow_ne_zero 2 (ne_of_gt (Complex.normSq_pos.mpr ha)))
            (ne_of_gt (Complex.normSq_pos.mpr haz)))
          (ne_of_gt (Complex.normSq_pos.mpr hcaz)))
        (ne_of_gt (Complex.normSq_pos.mpr hapz)))
      (ne_of_gt (Complex.normSq_pos.mpr hcapz))
  have hsum : Complex.normSq a + Complex.normSq z ≠ 0 := by
    have hapos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
    have hznonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg _
    positivity
  constructor
  · intro hzero
    have hnum :
        a.re ^ (2 : ℕ) * a.im ^ (2 : ℕ) *
          (Complex.normSq a + Complex.normSq z) = 0 := by
      unfold cauchyQuartetVariance xiReciprocalSquareCauchyQuartetVariance at hzero
      rcases div_eq_zero_iff.mp hzero with hnum | hdenzero
      · exact hnum
      · exact False.elim (hden hdenzero)
    rcases mul_eq_zero.mp hnum with hprod | hnorm
    · rcases mul_eq_zero.mp hprod with hre | him
      · exact Or.inl (sq_eq_zero_iff.mp hre)
      · exact Or.inr (sq_eq_zero_iff.mp him)
    · exact False.elim (hsum hnorm)
  · rintro (hre | him)
    · simp [cauchyQuartetVariance, xiReciprocalSquareCauchyQuartetVariance, hre]
    · simp [cauchyQuartetVariance, xiReciprocalSquareCauchyQuartetVariance, him]

set_option maxHeartbeats 800000 in
/-- **Universal one-probe law.**  On any summable family with multiplicity-preserving
conjugation and negation symmetries, the complete Cauchy orientation response is exactly one
quadrant scalar times the sum of the nonnegative quartet variances. -/
theorem tsum_cauchyQuartetOrientationTerm_eq_variance
    {ι : Type*} (z : ℂ) (a : ι → ℂ)
    (conjEquiv negEquiv : ι ≃ ι)
    (hconj : ∀ i, a (conjEquiv i) = (starRingEnd ℂ) (a i))
    (hneg : ∀ i, a (negEquiv i) = -a i)
    (ha : ∀ i, a i ≠ 0)
    (haz : ∀ i, a i - z ≠ 0)
    (hcaz : ∀ i, (starRingEnd ℂ) (a i) - z ≠ 0)
    (hapz : ∀ i, a i + z ≠ 0)
    (hcapz : ∀ i, (starRingEnd ℂ) (a i) + z ≠ 0)
    (hterm : Summable (fun i => cauchyQuartetOrientationTerm z (a i)))
    (hvariance : Summable (fun i => cauchyQuartetVariance z (a i))) :
    (∑' i, cauchyQuartetOrientationTerm z (a i)) =
      16 * z.re * z.im * ∑' i, cauchyQuartetVariance z (a i) := by
  let t : ι → ℝ := fun i => cauchyQuartetOrientationTerm z (a i)
  let V : ι → ℝ := fun i => cauchyQuartetVariance z (a i)
  have ht : Summable t := hterm
  have hconjSum : Summable (fun i => t (conjEquiv i)) :=
    (conjEquiv.summable_iff).mpr ht
  have hnegSum : Summable (fun i => t (negEquiv i)) :=
    (negEquiv.summable_iff).mpr ht
  have hbothSum : Summable (fun i => t (conjEquiv (negEquiv i))) :=
    (negEquiv.summable_iff).mpr ((conjEquiv.summable_iff).mpr ht)
  have hconjTsum : (∑' i, t (conjEquiv i)) = ∑' i, t i :=
    conjEquiv.tsum_eq t
  have hnegTsum : (∑' i, t (negEquiv i)) = ∑' i, t i :=
    negEquiv.tsum_eq t
  have hbothTsum : (∑' i, t (conjEquiv (negEquiv i))) = ∑' i, t i :=
    (negEquiv.trans conjEquiv).tsum_eq t
  have horbit (i : ι) :
      t i + t (conjEquiv i) + t (negEquiv i) +
          t (conjEquiv (negEquiv i)) =
        64 * z.re * z.im * V i := by
    dsimp only [t, V]
    rw [hconj i, hneg i, hconj (negEquiv i), hneg i, map_neg]
    exact cauchyQuartetOrientationTerm_sum_orbit
      z (a i) (ha i) (haz i) (hcaz i) (hapz i) (hcapz i)
  have hquartet :
      (∑' i, (t i + t (conjEquiv i) + t (negEquiv i) +
        t (conjEquiv (negEquiv i)))) =
      ∑' i, 64 * z.re * z.im * V i := by
    exact tsum_congr horbit
  rw [((ht.add hconjSum).add hnegSum).tsum_add hbothSum,
    (ht.add hconjSum).tsum_add hnegSum,
    ht.tsum_add hconjSum,
    hconjTsum, hnegTsum, hbothTsum,
    tsum_mul_left] at hquartet
  change (∑' i, t i) = _
  change Summable V at hvariance
  linarith

end

end RHTower
