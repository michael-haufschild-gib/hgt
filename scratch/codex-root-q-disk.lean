import GaloisForLFunctions.RHTower.PrimeArchCentralPairedDiagonalAlgebra

open Complex

namespace RHTower

noncomputable section

def centralPairedScaledNegativeDisk (w lam : ℂ) : Prop :=
  (Complex.normSq lam * w.re - lam.re) ^ (2 : ℕ) +
      (Complex.normSq lam * w.im) ^ (2 : ℕ) < lam.im ^ (2 : ℕ)

theorem centralPaired_barrier_eq_scaled_disk (w lam : ℂ) :
    Complex.normSq lam *
        ((1 - w.re * lam.re) ^ (2 : ℕ) +
          (w.re * lam.im) ^ (2 : ℕ) +
          w.im ^ (2 : ℕ) * Complex.normSq lam) -
      2 * lam.im ^ (2 : ℕ) =
    (Complex.normSq lam * w.re - lam.re) ^ (2 : ℕ) +
      (Complex.normSq lam * w.im) ^ (2 : ℕ) -
      lam.im ^ (2 : ℕ) := by
  simp only [Complex.normSq_apply]
  ring

theorem centralPaired_lineConj_pair_im_neg_of_scaledDisk
    (w lam : ℂ) (h : 1 - w * lam ≠ 0)
    (hc : 1 - w * (starRingEnd ℂ) lam ≠ 0)
    (hw : 0 < w.im) (hDisk : centralPairedScaledNegativeDisk w lam) :
    (lam / (1 - w * lam) +
        (starRingEnd ℂ) lam / (1 - w * (starRingEnd ℂ) lam)).im < 0 := by
  have hbar : Complex.normSq lam *
        ((1 - w.re * lam.re) ^ (2 : ℕ) +
          (w.re * lam.im) ^ (2 : ℕ) +
          w.im ^ (2 : ℕ) * Complex.normSq lam) -
      2 * lam.im ^ (2 : ℕ) < 0 := by
    rw [centralPaired_barrier_eq_scaled_disk]
    change (Complex.normSq lam * w.re - lam.re) ^ (2 : ℕ) +
      (Complex.normSq lam * w.im) ^ (2 : ℕ) < lam.im ^ (2 : ℕ) at hDisk
    exact sub_neg.mpr hDisk
  have hden : 0 < Complex.normSq (1 - w * lam) *
      Complex.normSq (1 - w * (starRingEnd ℂ) lam) :=
    mul_pos (Complex.normSq_pos.mpr h) (Complex.normSq_pos.mpr hc)
  rw [centralPaired_reciprocalSquare_lineConj_pair_im_formula w lam h hc]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by positivity) hbar) hden

theorem centralPaired_lineConj_pair_im_nonneg_outside_scaledDisk
    (w lam : ℂ) (h : 1 - w * lam ≠ 0)
    (hc : 1 - w * (starRingEnd ℂ) lam ≠ 0)
    (hw : 0 ≤ w.im)
    (hOutside : ¬ centralPairedScaledNegativeDisk w lam) :
    0 ≤ (lam / (1 - w * lam) +
        (starRingEnd ℂ) lam / (1 - w * (starRingEnd ℂ) lam)).im := by
  have hbar : 0 ≤ Complex.normSq lam *
        ((1 - w.re * lam.re) ^ (2 : ℕ) +
          (w.re * lam.im) ^ (2 : ℕ) +
          w.im ^ (2 : ℕ) * Complex.normSq lam) -
      2 * lam.im ^ (2 : ℕ) := by
    rw [centralPaired_barrier_eq_scaled_disk]
    change ¬ ((Complex.normSq lam * w.re - lam.re) ^ (2 : ℕ) +
      (Complex.normSq lam * w.im) ^ (2 : ℕ) < lam.im ^ (2 : ℕ)) at hOutside
    exact sub_nonneg.mpr (le_of_not_gt hOutside)
  exact centralPaired_lineConj_pair_im_nonneg_of_barrier w lam h hc hw hbar

end
end RHTower
