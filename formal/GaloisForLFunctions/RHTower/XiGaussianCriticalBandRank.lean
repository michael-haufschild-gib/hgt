import GaloisForLFunctions.RHTower.XiGaussianCertifiedPhaseGap

/-!
# The certified phase-free band cannot supply two independent critical nodes

Two distinct critical squared nodes in this band would supply four distinct
Schwarz copies. Their positive fourth reciprocal-trace atoms exceed the
unconditional source budget. Thus the band has at most one distinct critical
squared node. This tests the proposed rate comparison; it is not a negative
witness for the actual Hankel form.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

private theorem critical_fourth_atom_eq (q : {q : XiZeroCopy // (xiSpectralPoint q).im = 0}) :
    (xiZeroCopyReciprocalSquare q.1 ^ 2).re =
      1 / ((xiSpectralPoint q.1).re ^ 2) ^ 2 := by
  have hz : xiSpectralPoint q.1 = ((xiSpectralPoint q.1).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using q.property
  rw [xiZeroCopyReciprocalSquare, hz]
  simp only [← Complex.ofReal_inv,
    ← Complex.ofReal_pow, Complex.ofReal_re, inv_pow, one_div]

/-- The arithmetic phase-free band contains at most one distinct critical squared node. -/
theorem not_exists_two_criticalSquares_in_certifiedPhaseBand :
    ¬ ∃ q r : XiZeroCopy,
      (xiSpectralPoint q).im = 0 ∧ (xiSpectralPoint r).im = 0 ∧
      (xiSpectralPoint q).re ^ 2 ≠ (xiSpectralPoint r).re ^ 2 ∧
      (xiSpectralPoint q).re ^ 2 ≤ xiGaussianCertifiedPhaseGap ∧
      (xiSpectralPoint r).re ^ 2 ≤ xiGaussianCertifiedPhaseGap := by
  classical
  rintro ⟨q, r, hq, hr, hne, hqG, hrG⟩
  let qC := xiZeroCopyConjEquiv q
  let rC := xiZeroCopyConjEquiv r
  let f : XiZeroCopy → ℝ := fun p => (xiZeroCopyReciprocalSquare p ^ 2).re
  have hconj (p : XiZeroCopy) :
      (xiSpectralPoint (xiZeroCopyConjEquiv p)).re ^ 2 = (xiSpectralPoint p).re ^ 2 := by
    rw [xiSpectralPoint_copyConj, Complex.neg_re, Complex.conj_re, neg_sq]
  have hqr : q ≠ r := by
    intro h
    apply hne
    rw [h]
  have hqrC : q ≠ rC := by
    intro h
    apply hne
    rw [h]
    exact hconj r
  have hqCr : qC ≠ r := by
    intro h
    apply hne
    rw [← h]
    exact (hconj q).symm
  have hqCrC : qC ≠ rC := by
    intro h
    exact hqr (xiZeroCopyConjEquiv.injective h)
  have hqqC : q ≠ qC := xiZeroCopy_ne_conj q
  have hrrC : r ≠ rC := xiZeroCopy_ne_conj r
  have hs : Summable f := (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hsum := hs.sum_le_tsum {q, qC, r, rC}
    (fun p _ => xiFourthReciprocalTraceAtom_nonneg p)
  have hfinite : (∑ p ∈ ({q, qC, r, rC} : Finset XiZeroCopy), f p) =
      2 * f q + 2 * f r := by
    rw [Finset.sum_insert (by simp [hqqC, hqr, hqrC]),
      Finset.sum_insert (by simp [hqCr, hqCrC]),
      Finset.sum_insert (by simp [hrrC]), Finset.sum_singleton]
    change f q + (f qC + (f r + f rC)) = _
    rw [show f qC = f q from xiFourthReciprocalTraceAtom_conj q,
      show f rC = f r from xiFourthReciprocalTraceAtom_conj r]
    ring
  rw [hfinite] at hsum
  change 2 * f q + 2 * f r ≤
    ∑' p : XiZeroCopy, (xiZeroCopyReciprocalSquare p ^ 2).re at hsum
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hsum
  have hsmall (p : {p : XiZeroCopy // (xiSpectralPoint p).im = 0 ∧
      (xiSpectralPoint p).re ^ 2 ≤ xiGaussianCertifiedPhaseGap}) :
      (1 / (216 : ℝ) ^ 2) < f p.1 := by
    have hpos : 0 < (xiSpectralPoint p.1).re ^ 2 :=
      (by positivity : (0 : ℝ) < 32).trans (xiSpectral_re_sq_gt_thirtytwo p.1)
    have htop : (xiSpectralPoint p.1).re ^ 2 < 216 := by
      have hG : xiGaussianCertifiedPhaseGap < 216 := by
        rw [xiGaussianCertifiedPhaseGap_eq]
        linarith
      exact p.property.2.trans_lt hG
    have hsquare : ((xiSpectralPoint p.1).re ^ 2) ^ 2 < (216 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hpos.le (by positivity)).2 htop
    change (1 / (216 : ℝ) ^ 2) < (xiZeroCopyReciprocalSquare p.1 ^ 2).re
    rw [critical_fourth_atom_eq ⟨p.1, p.property.1⟩]
    exact one_div_lt_one_div_of_lt (sq_pos_of_pos hpos) hsquare
  have hqsmall := hsmall ⟨q, hq, hqG⟩
  have hrsmall := hsmall ⟨r, hr, hrG⟩
  have hsource := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  nlinarith only [hsum, hqsmall, hrsmall, hsource]

end RHTower
