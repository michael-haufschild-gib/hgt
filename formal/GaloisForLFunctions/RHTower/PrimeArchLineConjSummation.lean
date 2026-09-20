import GaloisForLFunctions.RHTower.XiWeilResolventGram

/-!
# Absolute summation of line-conjugate reciprocal-square pairs

The line-conjugation involution preserves the total sum.  Consequently nonnegative imaginary
parts of all literal pairs transfer to the absolutely convergent Xi divisor sum.
-/

open Complex

namespace RHTower

noncomputable section

theorem centralPaired_tsum_im_nonneg_of_lineConj_pairs
    (f : XiZeroCopy → ℂ) (hsum : Summable f)
    (hpair : ∀ q : XiZeroCopy,
      0 ≤ (f q + f (xiZeroCopyLineConjEquiv q)).im) :
    0 ≤ (∑' q : XiZeroCopy, f q).im := by
  have hsumJ : Summable (fun q : XiZeroCopy =>
      f (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs := hsum.add hsumJ
  have hreindex :
      (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q)) =
        ∑' q : XiZeroCopy, f q :=
    xiZeroCopyLineConjEquiv.tsum_eq f
  have hpairsumIm' :
      (∑' q : XiZeroCopy,
          (f q + f (xiZeroCopyLineConjEquiv q)).im) =
        (∑' q : XiZeroCopy, f q).im + (∑' q : XiZeroCopy, f q).im := by
    calc
      (∑' q : XiZeroCopy,
          (f q + f (xiZeroCopyLineConjEquiv q)).im) =
          (∑' q : XiZeroCopy,
            (f q + f (xiZeroCopyLineConjEquiv q))).im :=
        (Complex.im_tsum hpairs).symm
      _ = ((∑' q : XiZeroCopy, f q) +
          (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q))).im := by
        rw [hsum.tsum_add hsumJ]
      _ = ((∑' q : XiZeroCopy, f q) + ∑' q : XiZeroCopy, f q).im := by
        rw [hreindex]
      _ = (∑' q : XiZeroCopy, f q).im + (∑' q : XiZeroCopy, f q).im := by
        rw [Complex.add_im]
  have hpairsign :
      0 ≤ ∑' q : XiZeroCopy,
        (f q + f (xiZeroCopyLineConjEquiv q)).im :=
    tsum_nonneg hpair
  rw [hpairsumIm'] at hpairsign
  linarith

end

end RHTower
