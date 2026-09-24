import GaloisForLFunctions.RHTower.XiHadamardPairSignLaw
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.PrimeArchLineConjSummation
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiHadamardFinitePart

/-!
# Unconditional positivity of the completed logarithmic derivative right of the strip

The Hedenmalm centre-mixed criterion is `Re (ξ'/ξ)(1/2 + a + i b) ≥ 0` on the aperture
`0 < a < 1/2`.  Here the same quantity is shown nonnegative **unconditionally** on `Re s ≥ 1`.

The mechanism is the exact pair sign law: every divisor copy pairs with its line conjugate
`1 - conj ρ`, the Hadamard constants `(ρ - 1/2)^{-1}` cancel in the real part because the pairing
negates the centred coordinate, and the remaining resolvent pair lies outside its off-line disk
since `Re s - 1/2 ≥ 1/2` while every zero satisfies `(Re ρ - 1/2)^2 < 1/4`.

This is exactly where the unconditional argument stops: inside the aperture `Re s ∈ (1/2, 1)` the
disks are no longer avoided, and avoiding them is the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

theorem centralPaired_tsum_re_nonneg_of_lineConj_pairs
    (f : XiZeroCopy → ℂ) (hsum : Summable f)
    (hpair : ∀ q : XiZeroCopy,
      0 ≤ (f q + f (xiZeroCopyLineConjEquiv q)).re) :
    0 ≤ (∑' q : XiZeroCopy, f q).re := by
  have hsumJ : Summable (fun q : XiZeroCopy =>
      f (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs := hsum.add hsumJ
  have hreindex :
      (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q)) =
        ∑' q : XiZeroCopy, f q :=
    xiZeroCopyLineConjEquiv.tsum_eq f
  have hpairsumRe' :
      (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re) =
        (∑' q : XiZeroCopy, f q).re + (∑' q : XiZeroCopy, f q).re := by
    calc
      (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re) =
          (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q))).re :=
        (Complex.re_tsum hpairs).symm
      _ = ((∑' q : XiZeroCopy, f q) +
          (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q))).re := by
        rw [hsum.tsum_add hsumJ]
      _ = ((∑' q : XiZeroCopy, f q) + ∑' q : XiZeroCopy, f q).re := by
        rw [hreindex]
      _ = (∑' q : XiZeroCopy, f q).re + (∑' q : XiZeroCopy, f q).re := by
        rw [Complex.add_re]
  have hpairsign :
      0 ≤ ∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re :=
    tsum_nonneg hpair
  rw [hpairsumRe'] at hpairsign
  linarith

/-- The line conjugate of a divisor copy sits at `1 - conj ρ`. -/
theorem xiZero_lineConj_eq (q : XiZeroCopy) :
    (((xiZeroCopyLineConjEquiv q).1 : ℂ)) = 1 - (starRingEnd ℂ) ((q.1 : ℂ)) := by
  have h := xiSpectralPoint_lineConj q
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [xiSpectralPoint, xiSpectralPoint] at h
  simp only [map_mul, map_sub, map_neg, Complex.conj_I, hhalf] at h
  have hne : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have h2 : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) * (-Complex.I) =
      ((1 - (starRingEnd ℂ) ((q.1 : ℂ))) - 1 / 2) * (-Complex.I) := by
    rw [h]; ring
  have h3 := mul_right_cancel₀ hne h2
  linear_combination h3

/-- **Unconditional positivity of the completed logarithmic derivative right of the strip.**
Every divisor copy pairs with its line conjugate; the Hadamard constants cancel in the real part,
and the remaining resolvent pair lies outside its off-line disk because `Re s - 1/2 ≥ 1/2` while
every zero has `(Re ρ - 1/2)^2 < 1/4`. -/
theorem re_logDeriv_xi_nonneg_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv xi s).re := by
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [logDeriv_xi_eq_partialFraction hxi]
  refine centralPaired_tsum_re_nonneg_of_lineConj_pairs _ ?_ ?_
  · have h := XiAtlasFinitePart.summable_logDerivTerm hxi
    refine h.congr (fun q => ?_)
    show (XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ - (XiAtlasFinitePart.xiZero q - s)⁻¹ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
    rw [XiAtlasFinitePart.xiZero, show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
    ring
  · intro q
    have hstrip : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hrelt : ((q.1 : ℂ)).re < 1 := by nlinarith
    have hregt : 0 < ((q.1 : ℂ)).re := by nlinarith
    have hρ' := xiZero_lineConj_eq q
    have hcenter : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) =
        -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
      rw [hρ', map_sub, hhalf]; ring
    have hconst : ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re =
        -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
      rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
    have h1 : s - (q.1 : ℂ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      rw [hcon] at hs
      linarith
    have h2 : s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      have : s.re = 1 - ((q.1 : ℂ)).re := by
        rw [hcon]; simp
      linarith
    have hpos := re_inv_add_re_inv_lineConj_pos (s := s) (ρ := (q.1 : ℂ)) h1 h2
      (by linarith) (by nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)])
    have hrw : s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)) =
        s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) := by rw [hρ']
    simp only [Complex.add_re]
    rw [hconst, hrw]
    linarith [hpos]

end

end RHTower
