import GaloisForLFunctions.RHTower.XiParityMassDichotomy

/-!
# The even ladder off the right half-plane

The closed form of the archimedean logarithmic derivative needs only that `s` avoids the poles of
`Γ(s/2)`; the right half-plane is not required.  Along the even ladder `s, s+2, s+4, …` the shift-two
identity additionally needs the archimedean factor to be nonzero, which excludes the odd integers,
where the polynomial factor `s(s-1)/2` vanishes after an even translation.

`ArchLadderRegular s` packages exactly those two conditions.  It is stable under even translation, so
the explicit rational form of the even-shift archimedean correction holds on the whole ladder — in
particular at reflected points, which lie in the left half-plane and were previously out of reach.
-/

namespace RHTower

open Complex

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- `s` avoids the poles of `Γ(s/2)` and the odd integers. -/
def ArchLadderRegular (s : ℂ) : Prop :=
  (∀ m : ℕ, s / 2 ≠ -(m : ℂ)) ∧ ∀ k : ℤ, s ≠ ((2 * k + 1 : ℤ) : ℂ)

theorem ArchLadderRegular.ne_zero {s : ℂ} (h : ArchLadderRegular s) : s ≠ 0 := by
  intro hc
  exact h.1 0 (by rw [hc]; simp)

theorem ArchLadderRegular.ne_one {s : ℂ} (h : ArchLadderRegular s) : s ≠ 1 := by
  intro hc
  exact h.2 0 (by rw [hc]; norm_num)

theorem ArchLadderRegular.ne_neg_one {s : ℂ} (h : ArchLadderRegular s) : s ≠ -1 := by
  intro hc
  exact h.2 (-1) (by rw [hc]; norm_num)

theorem ArchLadderRegular.of_re_pos {s : ℂ} (hs : 0 < s.re) (hodd : ∀ k : ℤ, s ≠ ((2 * k + 1 : ℤ) : ℂ)) :
    ArchLadderRegular s :=
  ⟨div_two_ne_neg_nat_of_re_pos hs, hodd⟩

/-- Even translation preserves ladder regularity. -/
theorem ArchLadderRegular.shift {s : ℂ} (h : ArchLadderRegular s) (j : ℕ) :
    ArchLadderRegular (s + ((2 * j : ℕ) : ℂ)) := by
  refine ⟨fun m hc => h.1 (m + j) ?_, fun k hc => h.2 (k - j) ?_⟩
  · push_cast at hc ⊢
    linear_combination hc
  · push_cast at hc ⊢
    linear_combination hc

/-- **Shift-two archimedean correction off the poles.** -/
theorem logDeriv_archFactor_shift_two_of_ladderRegular {s : ℂ} (h : ArchLadderRegular s) :
    logDeriv archFactor (s + 2) - logDeriv archFactor s =
      1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1) := by
  have hs0 : s ≠ 0 := h.ne_zero
  have hs1 : s ≠ 1 := h.ne_one
  have hsm1 : s ≠ -1 := h.ne_neg_one
  have hs2 : s + 2 ≠ 0 := by
    intro hc
    refine h.1 1 ?_
    push_cast
    linear_combination hc / 2
  have hs3 : s + 2 ≠ 1 := by
    intro hc
    exact hsm1 (by linear_combination hc)
  have hpole2 : ∀ m : ℕ, (s + 2) / 2 ≠ -(m : ℂ) := by
    intro m hc
    refine h.1 (m + 1) ?_
    push_cast
    linear_combination hc
  rw [logDeriv_archFactor_closed_off_poles hpole2 hs2 hs3,
    logDeriv_archFactor_closed_off_poles h.1 hs0 hs1,
    show (s + 2) - 1 = s + 1 by ring]
  unfold gammaRealLogConnection
  rw [show (s + 2) / 2 = s / 2 + 1 by ring,
    GaloisForLFunctions.digamma_half_add_one h.1]
  field_simp [hs0, hs1, hs2, sub_ne_zero.mpr hs1]
  ring

/-- **Even-shift archimedean correction off the poles.** The rational telescope is valid on the whole
even ladder, not merely on the right half-plane. -/
theorem xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular {s : ℂ}
    (h : ArchLadderRegular s) (m : ℕ) :
    xiTransverseShiftArchimedeanCorrection (2 * m) s = xiEvenShiftPrimeCorrection m s := by
  induction m with
  | zero => simp [xiTransverseShiftArchimedeanCorrection, xiEvenShiftPrimeCorrection]
  | succ m ih =>
      have hstep := logDeriv_archFactor_shift_two_of_ladderRegular (h.shift m)
      have hcast : ((2 * (m + 1) : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) + 2 := by push_cast; ring
      have hcorr : xiEvenShiftPrimeCorrection (m + 1) s =
          xiEvenShiftPrimeCorrection m s +
            (1 / (s + ((2 * m : ℕ) : ℂ) + 2) + 1 / (s + ((2 * m : ℕ) : ℂ) + 1) -
              1 / (s + ((2 * m : ℕ) : ℂ) - 1)) := by
        rw [xiEvenShiftPrimeCorrection, xiEvenShiftPrimeCorrection, Finset.sum_range_succ]
      rw [xiTransverseShiftArchimedeanCorrection] at ih ⊢
      rw [hcast, hcorr, show s + (((2 * m : ℕ) : ℂ) + 2) = s + ((2 * m : ℕ) : ℂ) + 2 by ring]
      linear_combination hstep + ih

/-- **Same-parity pairwise archimedean correction off the poles.** -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (h : ArchLadderRegular (s + (b : ℂ))) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) := by
  obtain ⟨m, hm⟩ : ∃ m, a - b = 2 * m := ⟨(a - b) / 2, by omega⟩
  rw [xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le a b s hba, hm,
    xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular h m]
  congr 1
  omega

/-- **Explicit rational reflection cocycle for a same-parity pair.** Both the base point and its
reflection are handled: the reflected point lies in the left half-plane, which the ladder-regular
form reaches. -/
theorem xiPairwiseShiftReflectionCocycle_eq_explicit
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (hbase : ArchLadderRegular (s + (b : ℂ)))
    (hrefl : ArchLadderRegular (1 - (a : ℂ) - s)) :
    xiPairwiseShiftReflectionCocycle a b s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) -
        xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s) := by
  have hrefl' : ArchLadderRegular (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s + (b : ℂ)) := by
    rw [xiPairwiseShiftReflection, show (1 : ℂ) - a - b - s + b = 1 - (a : ℂ) - s by ring]
    exact hrefl
  rw [xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar hbase,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar hrefl',
    xiPairwiseShiftReflection, show (1 : ℂ) - a - b - s + b = 1 - (a : ℂ) - s by ring]

/-- **Same-parity corrected pairwise value off the poles.** -/
theorem xiPairwiseShiftPrimeDifference_eq_explicit_of_ladderRegular
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (h : ArchLadderRegular (s + (b : ℂ))) :
    xiPairwiseShiftPrimeDifference a b s =
      (logDeriv xi (s + (a : ℂ)) - logDeriv xi (s + (b : ℂ))) -
        xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) := by
  rw [xiPairwiseShiftPrimeDifference_eq_raw_sub_correction,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar h,
    xiPairwiseShiftRawLogDerivDifference]

/-- **Explicit centered value for a same-parity pair.** Half-cocycle centering subtracts the average
of the rational telescope at the point and at its reflection.  The correction is manifestly rational
and manifestly symmetric about `(1-a-b)/2`; the completed-Xi content is the raw logarithmic-derivative
difference alone.

The corpus shift-two theory is the pair `(2,0)`: there the average of the telescope at `s` and at
`-1-s` is `1/(s+2) + 1/(s+1) - 1/(s-1) - (1/2)(1/s + 1/(s+1))`. -/
theorem xiPairwiseCenteredShiftPrimeDifference_eq_explicit
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (hbase : ArchLadderRegular (s + (b : ℂ)))
    (hrefl : ArchLadderRegular (1 - (a : ℂ) - s)) :
    xiPairwiseCenteredShiftPrimeDifference a b s =
      (logDeriv xi (s + (a : ℂ)) - logDeriv xi (s + (b : ℂ))) -
        (1 / 2 : ℂ) * (xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) +
          xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s)) := by
  rw [xiPairwiseCenteredShiftPrimeDifference,
    xiPairwiseShiftPrimeDifference_eq_explicit_of_ladderRegular hba hpar hbase,
    xiPairwiseShiftReflectionCocycle_eq_explicit hba hpar hbase hrefl]
  ring

/-- **The centering correction of a same-parity pair is half-plane rational.** -/
theorem isHalfPlaneRational_pairwiseCenteringCorrection (a b : ℕ) :
    IsHalfPlaneRational (fun s : ℂ =>
      (1 / 2 : ℂ) * (xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) +
        xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s))) := by
  have hleft : IsHalfPlaneRational
      (fun s : ℂ => xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ))) :=
    isHalfPlaneRational_xiEvenShiftPrimeCorrection _ _
  have hright : IsHalfPlaneRational
      (fun s : ℂ => xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s)) := by
    have hterm : ∀ j : ℕ, IsHalfPlaneRational
        (fun s : ℂ => 1 / (s + (-(1 - (a : ℂ) + ((2 * j : ℕ) : ℂ) + 2))) +
          1 / (s + (-(1 - (a : ℂ) + ((2 * j : ℕ) : ℂ) + 1))) -
          1 / (s + (-(1 - (a : ℂ) + ((2 * j : ℕ) : ℂ) - 1)))) := fun j =>
      ((isHalfPlaneRational_simple _).add (isHalfPlaneRational_simple _)).sub
        (isHalfPlaneRational_simple _)
    have hsum := isHalfPlaneRational_finsetSum (Finset.range ((a - b) / 2)) _
      (fun j _ => hterm j)
    refine ((hsum.const_mul (-1 : ℂ)).congr Set.finite_empty (fun z _ _ => ?_))
    rw [xiEvenShiftPrimeCorrection, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : (1 : ℂ) - (a : ℂ) - z + ((2 * j : ℕ) : ℂ) + 2 =
        -(z + -(1 - (a : ℂ) + ((2 * j : ℕ) : ℂ) + 2)) := by ring
    have e2 : (1 : ℂ) - (a : ℂ) - z + ((2 * j : ℕ) : ℂ) + 1 =
        -(z + -(1 - (a : ℂ) + ((2 * j : ℕ) : ℂ) + 1)) := by ring
    have e3 : (1 : ℂ) - (a : ℂ) - z + ((2 * j : ℕ) : ℂ) - 1 =
        -(z + -(1 - (a : ℂ) + ((2 * j : ℕ) : ℂ) - 1)) := by ring
    rw [e1, e2, e3]
    field_simp
  exact (hleft.add hright).const_mul _

end

end RHTower
