import GaloisForLFunctions.RHTower.LiEvenCrossGlobalQuotientCompleteMonotonicityNoGo

/-!
# LI real-axis scalar-sign no-go

The existing conjugation-symmetric LI packet has a negative completed-Abel mode and a
strictly completely monotone radial quotient on the positive ray. Its real radial
quotient is in fact strictly positive at every real mass away from its on-line pole.
The off-axis pair is masked by the seven on-line copies on the whole real axis.

Thus even negative-mass real-axis continuation cannot replace the unresolved
source-derived complex singular-support law. This is a spectral countermodel, not
a claim that the literal Xi source has any off-line zero.
-/

open Complex

namespace RHTower

noncomputable section

private theorem norm_liLocalQuotient_offPlus (v : ℝ) :
    ‖liLocalRadialQuotientAtom liLocalOffLineNode (v : ℂ)‖ =
      (5 / 4 : ℝ) / ((v + 3 / 4) ^ (2 : ℕ) + 1) := by
  have hden : ‖((v : ℂ) + liLocalOffLineNode) ^ (2 : ℕ)‖ =
      (v + 3 / 4) ^ (2 : ℕ) + 1 := by
    rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [liLocalOffLineNode, Complex.add_re, Complex.add_im]
    ring
  rw [liLocalRadialQuotientAtom, norm_div, norm_liLocalOffLineNode, hden]

private theorem norm_liLocalQuotient_offMinus (v : ℝ) :
    ‖liLocalRadialQuotientAtom liLocalOffLineNodeConj (v : ℂ)‖ =
      (5 / 4 : ℝ) / ((v + 3 / 4) ^ (2 : ℕ) + 1) := by
  have hden : ‖((v : ℂ) + liLocalOffLineNodeConj) ^ (2 : ℕ)‖ =
      (v + 3 / 4) ^ (2 : ℕ) + 1 := by
    rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [liLocalOffLineNodeConj, Complex.add_re, Complex.add_im]
    ring
  rw [liLocalRadialQuotientAtom, norm_div, norm_liLocalOffLineNodeConj, hden]

private theorem re_liLocalQuotient_base (v : ℝ) :
    (liLocalRadialQuotientAtom liLocalOnLineNode (v : ℂ)).re =
      (1 / 2 : ℝ) / (v + 1 / 2) ^ (2 : ℕ) := by
  have hcomplex : liLocalRadialQuotientAtom liLocalOnLineNode (v : ℂ) =
      (((1 / 2 : ℝ) / (v + 1 / 2) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp [liLocalRadialQuotientAtom, liLocalOnLineNode]
  rw [hcomplex]
  rfl

/-- The existing off-axis LI packet is positive on the entire real mass axis,
not only on the positive ray, away from its on-axis pole. -/
theorem liLocalQuotientResponse_pos_allReal {v : ℝ} (hv : v ≠ -(1 / 2)) :
    0 < liLocalQuotientResponse v := by
  let t : ℝ := v + 1 / 2
  let d : ℝ := (t + 1 / 4) ^ (2 : ℕ) + 1
  have ht : t ≠ 0 := by
    intro h
    apply hv
    dsimp [t] at h
    linarith
  have ht2 : 0 < t ^ (2 : ℕ) := sq_pos_of_ne_zero ht
  have hd : 0 < d := by dsimp [d]; positivity
  have hmargin : 0 < 7 * d - 5 * t ^ (2 : ℕ) := by
    have heq : 7 * d - 5 * t ^ (2 : ℕ) =
        2 * (t + 7 / 8) ^ (2 : ℕ) + 189 / 32 := by
      dsimp [d]
      ring
    rw [heq]
    positivity
  have hdom : (5 / 2 : ℝ) / d < (7 / 2 : ℝ) / t ^ (2 : ℕ) := by
    apply (div_lt_div_iff₀ hd ht2).2
    nlinarith [hmargin]
  have hplus :
      -(5 / 4 : ℝ) / d ≤
        (liLocalRadialQuotientAtom liLocalOffLineNode (v : ℂ)).re := by
    have h := (neg_le_abs _).trans
      (Complex.abs_re_le_norm (liLocalRadialQuotientAtom liLocalOffLineNode (v : ℂ)))
    rw [norm_liLocalQuotient_offPlus] at h
    have hd' : (v + 3 / 4) ^ (2 : ℕ) + 1 = d := by dsimp [d, t]; ring
    rw [hd'] at h
    simp only [neg_div]
    linarith
  have hminus :
      -(5 / 4 : ℝ) / d ≤
        (liLocalRadialQuotientAtom liLocalOffLineNodeConj (v : ℂ)).re := by
    have h := (neg_le_abs _).trans
      (Complex.abs_re_le_norm (liLocalRadialQuotientAtom liLocalOffLineNodeConj (v : ℂ)))
    rw [norm_liLocalQuotient_offMinus] at h
    have hd' : (v + 3 / 4) ^ (2 : ℕ) + 1 = d := by dsimp [d, t]; ring
    rw [hd'] at h
    simp only [neg_div]
    linarith
  have hresponse : liLocalQuotientResponse v =
      (7 / 2 : ℝ) / t ^ (2 : ℕ) +
        (liLocalRadialQuotientAtom liLocalOffLineNode (v : ℂ)).re +
        (liLocalRadialQuotientAtom liLocalOffLineNodeConj (v : ℂ)).re := by
    simp only [liLocalQuotientResponse, liLocalQuotientComplexResponse,
      Complex.add_re, Complex.mul_re]
    norm_num
    rw [re_liLocalQuotient_base]
    dsimp [t]
    ring
  rw [hresponse]
  have hdouble : (5 / 2 : ℝ) / d = (5 / 4 : ℝ) / d + (5 / 4 : ℝ) / d := by ring
  rw [hdouble] at hdom
  simp only [neg_div] at hplus hminus
  linarith [hdom, hplus, hminus]

/-- Full real-axis scalar sign remains compatible with a negative completed LI
endpoint mode for the same conjugation-symmetric spectral packet. -/
theorem liLocalQuotient_allRealSign_and_negativeMode :
    (∀ v : ℝ, v ≠ -(1 / 2) → 0 < liLocalQuotientResponse v) ∧
      (liLocalCompletedAbelEndpointMode 3).re < 0 :=
  ⟨fun _ hv => liLocalQuotientResponse_pos_allReal hv,
    liLocalCompletedAbelEndpointMode_three_re_neg⟩

/-- Whole-real-axis positivity together with all-order positive-ray complete
monotonicity still permits a negative LI endpoint mode. -/
theorem liLocalQuotient_allRealSign_completeMonotonicity_negativeMode :
    StrictCompletelyMonotoneOnPositiveRay liLocalQuotientResponse ∧
      (∀ v : ℝ, v ≠ -(1 / 2) → 0 < liLocalQuotientResponse v) ∧
      (liLocalCompletedAbelEndpointMode 3).re < 0 :=
  ⟨strictCompletelyMonotoneOnPositiveRay_liLocalQuotientResponse,
    (fun _ hv => liLocalQuotientResponse_pos_allReal hv),
    liLocalCompletedAbelEndpointMode_three_re_neg⟩

end

end RHTower
