import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFirstJetWeld

/-!
# Actual-to-canonical completed Eisenstein Maass weld

Corpus conjecture C-A.9t2b2b is the decisive differential weld in the HB cusp-current route.
The preceding module gives genuine value, first, horizontal-second, and mixed jets for every
signed Whittaker tail, but deliberately does not impose a separate vertical-second majorant.

This module first derives the exact square-root Whittaker eigen-equation from the corpus Schlaefli
order recurrence.  Consequently every signed vertical second jet is algebraically determined by
the already-summable value and horizontal second jets.  The resulting full canonical second jet
can then be compared with the literal completed Poincare jet and its two Maass words.

RH chain:

actual/canonical Maass weld -> literal truncated Green/Stokes -> full cusp current finite part ->
actual balanced BM `++-` coefficient -> negative BM leg -> conserved left-QNM projection ->
HC94 -> RH.
-/

open Complex Real Filter Set Topology
open scoped BigOperators

namespace RHTower
noncomputable section

/-- The square-root Whittaker carrier obeys the centered hyperbolic eigen-equation.  This is
derived from the corpus order recurrence, not introduced as a special-function axiom. -/
theorem d4BM_whittakerP0_secondJet_eigenEquation
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    (Y : ℂ) ^ 2 *
        (d4BMWhittakerP0SecondJet c nu Y -
          (c : ℂ) ^ 2 * d4BMWhittakerP0 c nu Y) =
      (nu ^ 2 - 1 / 4) * d4BMWhittakerP0 c nu Y := by
  have hrec0 :=
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder_add_one
      (mul_pos c.2 Y.2) nu
  have hrecp :=
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder_add_one
      (mul_pos c.2 Y.2) (nu + 1)
  have hrecm :=
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder_add_one
      (mul_pos c.2 Y.2) (nu - 1)
  unfold d4BMWhittakerP0SecondJet
    d4BMPositiveFrequencyRaiseZeroModeDeriv
    d4BMPositiveFrequencyRaiseZeroShift
    d4BMWhittakerP1Deriv
    d4BMWhittakerP0FirstJet
    d4BMWhittakerP0Deriv
    d4BMWhittakerP1
    d4BMWhittakerP0
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast c.2.ne'
  have hsqrt : Real.sqrt (Y : ℝ) ≠ 0 := (Real.sqrt_pos.2 Y.2).ne'
  have hsqrt_sq : (Real.sqrt (Y : ℝ) : ℂ) ^ 2 = (Y : ℂ) := by
    exact_mod_cast Real.sq_sqrt Y.2.le
  push_cast at hrec0 hrecp hrecm ⊢
  have hpp :
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * (Y : ℝ)) (nu + 2) =
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            ((c : ℝ) * (Y : ℝ)) nu +
          (2 * (nu + 1) / ((c : ℂ) * (Y : ℂ))) *
            GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
              ((c : ℝ) * (Y : ℝ)) (nu + 1) := by
    convert hrecp using 1 <;> ring_nf
  have hmm :
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * (Y : ℝ)) (nu - 2) =
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            ((c : ℝ) * (Y : ℝ)) nu -
          (2 * (nu - 1) / ((c : ℂ) * (Y : ℂ))) *
            GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
              ((c : ℝ) * (Y : ℝ)) (nu - 1) := by
    apply (eq_sub_iff_add_eq).2
    convert hrecm.symm using 1 <;> ring_nf
  have hpm :
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * (Y : ℝ)) (nu + 1) -
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * (Y : ℝ)) (nu - 1) =
        (2 * nu / ((c : ℂ) * (Y : ℂ))) *
          GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            ((c : ℝ) * (Y : ℝ)) nu := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hrec0
  rw [show nu + 1 + 1 = nu + 2 by ring,
    show nu - 1 - 1 = nu - 2 by ring,
    show nu + 1 - 1 = nu by ring,
    show nu - 1 + 1 = nu by ring,
    hpp, hmm]
  field_simp [hYne, hcne, hsqrt] at hpm ⊢
  rw [hsqrt_sq]
  ring_nf at ⊢
  rw [show 1 + nu = nu + 1 by ring,
    show -1 + nu = nu - 1 by ring]
  linear_combination (8 * (Y : ℂ) * nu) * hpm

/-- Every signed Fourier mode has the same centered hyperbolic eigenvalue. -/
theorem d4BM_signedWhittakerMode_secondJet_eigenEquation
    (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) :
    (Y : ℂ) ^ 2 *
        (d4BMSignedWhittakerModeHorizontalSecondJet
            negative N nu x Y +
          d4BMSignedWhittakerModeVerticalSecondJet
            negative N nu x Y) =
      (nu ^ 2 - 1 / 4) *
        d4BMSignedWhittakerMode negative N nu x Y := by
  have heigen := d4BM_whittakerP0_secondJet_eigenEquation
    (d4BMPositiveFourierScale N) nu Y
  have hrate : d4BMSignedFourierRate negative N ^ 2 =
      -(d4BMPositiveFourierScale N : ℂ) ^ 2 := by
    unfold d4BMSignedFourierRate
    rw [show ((d4BMFourierSign negative : ℂ) *
        (d4BMPositiveFourierScale N : ℂ) * Complex.I) ^ 2 =
      (d4BMFourierSign negative : ℂ) ^ 2 *
        (d4BMPositiveFourierScale N : ℂ) ^ 2 * Complex.I ^ 2 by ring,
      Complex.I_sq]
    cases negative <;> norm_num [d4BMFourierSign]
  unfold d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedWhittakerModeVerticalSecondJet
    d4BMSignedWhittakerMode
  rw [hrate]
  linear_combination
    d4BMCompletedEisensteinFourierPhase negative N x * heigen

/-- One summand of the corpus signed square-root Whittaker tail. -/
def d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) (Y : ℝ) (N : ℕ) : ℂ :=
  (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree *
      d4BMCompletedEisensteinFourierPhase negative N x) *
    (Real.sqrt Y : ℂ) * (Y : ℂ) ^ heightDegree *
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
      (2 * Real.pi * ((N : ℝ) + 1) * Y) nu

theorem d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_summand_tsum
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) (Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative x indexDegree heightDegree Y =
      ∑' N : ℕ,
        d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u nu negative x indexDegree heightDegree Y N := by
  rfl

/-- Every fixed signed square-root Whittaker jet family is absolutely summable on an exterior
cusp edge.  This packages the common admission needed for finite Maass-word linearity. -/
theorem summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
        u nu negative x indexDegree heightDegree Y N) := by
  let C : ℝ := ‖((Y : ℂ) ^ heightDegree)‖ *
    d4BMSignedWhittakerLocalValueConstant Y nu
  let M : ℕ → ℝ := fun N =>
    C * (‖d4BMCompletedEisensteinWhittakerCoefficient
        u ⟨N + 1, by omega⟩ * ((N + 1 : ℕ) : ℂ) ^ indexDegree‖ *
      Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf
      u indexDegree).mul_left C
  apply Summable.of_norm_bounded hM
  intro N
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hvalue := norm_d4BMWhittakerP0_signed_local_le Y hYmem N nu
  have hsummand :
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u nu negative x indexDegree heightDegree Y N =
        (d4BMCompletedEisensteinWhittakerCoefficient
            u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree *
          d4BMCompletedEisensteinFourierPhase negative N x) *
          (Y : ℂ) ^ heightDegree *
          d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y := by
    unfold d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      d4BMWhittakerP0 d4BMPositiveFourierScale
    ring
  have hphase :
      ‖(d4BMCompletedEisensteinWhittakerCoefficient
            u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree) *
          d4BMCompletedEisensteinFourierPhase negative N x‖ =
        ‖d4BMCompletedEisensteinWhittakerCoefficient
            u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree‖ := by
    rw [norm_mul, d4BM_norm_completedEisensteinFourierPhase, mul_one]
  rw [hsummand, norm_mul, norm_mul, hphase]
  calc
    ‖d4BMCompletedEisensteinWhittakerCoefficient
          u ⟨N + 1, by omega⟩ *
        (↑(N + 1) : ℂ) ^ indexDegree‖ *
        ‖(Y : ℂ) ^ heightDegree‖ *
        ‖d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y‖
      ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
            u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree‖ *
        ‖(Y : ℂ) ^ heightDegree‖ *
        (d4BMSignedWhittakerLocalValueConstant Y nu *
          Real.exp (-(((N : ℝ) + 1) / 2))) := by gcongr
    _ = M N := by simp only [M, C]; ring

/-- The coefficientwise six-block expansion underlying one signed phased Maass word. -/
def d4BMCompletedEisensteinPhasedMaassExpansionSummand
    (raise negative : Bool) (u nu : ℂ) (x Y : ℝ) (N : ℕ) : ℂ :=
  (3 / 4 : ℂ) *
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
        u nu negative x 0 0 Y N +
    (if raise then -(3 * (2 * Real.pi : ℂ)) else 3 * (2 * Real.pi : ℂ)) *
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
        u nu negative x 1 1 Y N -
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)) *
      (d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u (nu + 1) negative x 1 1 Y N +
        d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u (nu - 1) negative x 1 1 Y N) +
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ 2) *
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
        u nu negative x 2 2 Y N +
    (if raise then (2 * Real.pi : ℂ) ^ 2 else -(2 * Real.pi : ℂ) ^ 2) *
      (d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u (nu + 1) negative x 2 2 Y N +
        d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u (nu - 1) negative x 2 2 Y N) +
    ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ 2) *
      (d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u (nu + 2) negative x 2 2 Y N +
        d4BMCompletedEisensteinSignedSqrtWhittakerSummand
          u (nu - 2) negative x 2 2 Y N)

/-- The existing canonical phased word is the absolutely convergent sum of its literal
coefficientwise six-block expansion. -/
theorem d4BMCompletedEisensteinPhasedMaassWord_eq_expansion_tsum
    (raise negative : Bool) (u nu : ℂ) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    d4BMCompletedEisensteinPhasedMaassWord raise negative u nu x Y =
      ∑' N : ℕ,
        d4BMCompletedEisensteinPhasedMaassExpansionSummand
          raise negative u nu x Y N := by
  let S := fun mu : ℂ => fun j m : ℕ => fun N : ℕ =>
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u mu negative x j m Y N
  let e00 : ℕ → ℂ := fun N => (3 / 4 : ℂ) * S nu 0 0 N
  let e10 : ℕ → ℂ := fun N =>
    (if raise then -(3 * (2 * Real.pi : ℂ)) else 3 * (2 * Real.pi : ℂ)) *
      S nu 1 1 N
  let e1 : ℕ → ℂ := fun N =>
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)) *
      (S (nu + 1) 1 1 N + S (nu - 1) 1 1 N)
  let e20 : ℕ → ℂ := fun N =>
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ 2) * S nu 2 2 N
  let e2 : ℕ → ℂ := fun N =>
    (if raise then (2 * Real.pi : ℂ) ^ 2 else -(2 * Real.pi : ℂ) ^ 2) *
      (S (nu + 1) 2 2 N + S (nu - 1) 2 2 N)
  let e22 : ℕ → ℂ := fun N =>
    ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ 2) *
      (S (nu + 2) 2 2 N + S (nu - 2) 2 2 N)
  have hs (mu : ℂ) (j m : ℕ) : Summable (S mu j m) := by
    exact summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u mu negative x j m Y
  have he00 : Summable e00 := (hs nu 0 0).mul_left _
  have he10 : Summable e10 := (hs nu 1 1).mul_left _
  have he1 : Summable e1 :=
    ((hs (nu + 1) 1 1).add (hs (nu - 1) 1 1)).mul_left _
  have he20 : Summable e20 := (hs nu 2 2).mul_left _
  have he2 : Summable e2 :=
    ((hs (nu + 1) 2 2).add (hs (nu - 1) 2 2)).mul_left _
  have he22 : Summable e22 :=
    ((hs (nu + 2) 2 2).add (hs (nu - 2) 2 2)).mul_left _
  have h01 : Summable (fun N => e00 N + e10 N) := he00.add he10
  have h011 : Summable (fun N => e00 N + e10 N - e1 N) := h01.sub he1
  have h012 : Summable (fun N => e00 N + e10 N - e1 N + e20 N) := h011.add he20
  have h013 : Summable (fun N => e00 N + e10 N - e1 N + e20 N + e2 N) :=
    h012.add he2
  rw [d4BMCompletedEisensteinPhasedMaassWord]
  simp only [d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_summand_tsum]
  symm
  change (∑' N : ℕ, (e00 N + e10 N - e1 N + e20 N + e2 N + e22 N)) = _
  rw [h013.tsum_add he22, h012.tsum_add he2, h011.tsum_add he20,
    h01.tsum_sub he1, he00.tsum_add he10]
  simp only [e00, e10, e1, e20, e2, e22, S, tsum_mul_left]
  rw [(hs (nu + 1) 1 1).tsum_add (hs (nu - 1) 1 1),
    (hs (nu + 1) 2 2).tsum_add (hs (nu - 1) 2 2),
    (hs (nu + 2) 2 2).tsum_add (hs (nu - 2) 2 2)]

/-- Each canonical phased expansion summand is the arithmetic coefficient and phase times the
literal positive-frequency raising or lowering mode. -/
theorem d4BMCompletedEisensteinPhasedMaassExpansionSummand_eq_mode
    (raise negative : Bool) (u nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) (N : ℕ) :
    d4BMCompletedEisensteinPhasedMaassExpansionSummand
        raise negative u nu x Y N =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMCompletedEisensteinFourierPhase negative N x *
          if raise then
            d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
              (d4BMPositiveFourierScale N) nu Y
          else
            d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
              (d4BMPositiveFourierScale N) nu Y) := by
  cases raise
  · simp only [Bool.false_eq_true, if_false]
    rw [d4BM_positiveFrequencyLowerNegTwoLowerZeroMode_eq_shiftWord]
    unfold d4BMCompletedEisensteinPhasedMaassExpansionSummand
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      d4BMWhittakerP2 d4BMWhittakerP1 d4BMWhittakerP0
      d4BMPositiveFourierScale
    push_cast
    ring
  · simp
    rw [d4BM_positiveFrequencyRaiseTwoRaiseZeroMode_eq_shiftWord]
    unfold d4BMCompletedEisensteinPhasedMaassExpansionSummand
      d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      d4BMWhittakerP2 d4BMWhittakerP1 d4BMWhittakerP0
      d4BMPositiveFourierScale
    simp only [if_true]
    push_cast
    ring

theorem summable_d4BMCompletedEisensteinWeightedSignedWhittakerMode
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinWeightedSignedWhittakerMode
        u negative N nu x Y) := by
  apply (summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    u nu negative x 0 0 Y).congr
  intro N
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerMode
    d4BMSignedWhittakerMode
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    d4BMWhittakerP0 d4BMPositiveFourierScale
  ring

theorem summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
        u negative N nu x Y) := by
  have h := (summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    u nu negative x 2 0 Y).mul_left (-(2 * Real.pi : ℂ) ^ 2)
  apply h.congr
  intro N
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
    d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedFourierRate
    d4BMSignedWhittakerMode
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    d4BMWhittakerP0 d4BMPositiveFourierScale
  cases negative <;> norm_num [d4BMFourierSign]
  all_goals rw [show
    ((2 * Real.pi : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) * Complex.I) ^ 2 =
      ((2 * Real.pi : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ)) ^ 2 *
        Complex.I ^ 2 by ring, Complex.I_sq]
  all_goals push_cast
  all_goals ring

end
end RHTower
