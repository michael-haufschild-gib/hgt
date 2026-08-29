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
  have hrate : d4BMSignedFourierRate negative N ^ 2 =
      -(2 * Real.pi : ℂ) ^ 2 * ((N + 1 : ℕ) : ℂ) ^ 2 := by
    unfold d4BMSignedFourierRate
    rw [show ((d4BMFourierSign negative : ℂ) *
        (d4BMPositiveFourierScale N : ℂ) * Complex.I) ^ 2 =
      (d4BMFourierSign negative : ℂ) ^ 2 *
        (d4BMPositiveFourierScale N : ℂ) ^ 2 * Complex.I ^ 2 by ring,
      Complex.I_sq]
    cases negative <;> norm_num [d4BMFourierSign, d4BMPositiveFourierScale]
    all_goals ring
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
    d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedWhittakerMode
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    d4BMWhittakerP0 d4BMPositiveFourierScale
  rw [hrate]
  push_cast
  ring

theorem summable_d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
        u negative N nu x Y) := by
  let C := d4BMSignedWhittakerLocalFirstJetConstant Y nu
  let M : ℕ → ℝ := fun N =>
    (2 * Real.pi * C) *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 2‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 2).mul_left
      (2 * Real.pi * C)
  apply Summable.of_norm_bounded hM
  intro N
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hfirst :=
    norm_d4BMWhittakerP0FirstJet_signed_local_le Y hYmem N nu
  rw [show d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
        u negative N nu x Y =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMSignedFourierRate negative N *
          (d4BMCompletedEisensteinFourierPhase negative N x *
            d4BMWhittakerP0FirstJet
              (d4BMPositiveFourierScale N) nu Y)) by rfl,
    norm_mul, norm_mul, norm_mul, norm_d4BMSignedFourierRate,
    d4BM_norm_completedEisensteinFourierPhase, one_mul]
  calc
    _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
            u ⟨N + 1, by omega⟩‖ *
          (2 * Real.pi * ((N : ℝ) + 1)) *
            (C * ((N : ℝ) + 1) *
              Real.exp (-(((N : ℝ) + 1) / 2))) := by
          have hnonneg :
              0 ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
                  u ⟨N + 1, by omega⟩‖ *
                (2 * Real.pi * ((N : ℝ) + 1)) := by positivity
          simpa only [C, mul_assoc] using
            mul_le_mul_of_nonneg_left hfirst hnonneg
    _ = M N := by
          have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
            rw [Complex.norm_natCast]
            norm_num [Real.norm_eq_abs, abs_of_nonneg]
          simp only [M, norm_mul, norm_pow, hnNorm]
          ring

/-- Arithmetic coefficient times the genuine vertical second jet of one signed mode. -/
def d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
    d4BMSignedWhittakerModeVerticalSecondJet negative N nu x Y

/-- Vertical second jets are algebraically reconstructed from value and horizontal second jets. -/
theorem d4BM_weightedSignedWhittakerVerticalSecondJet_eq_eigenReconstruction
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) :
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
        u negative N nu x Y =
      ((nu ^ 2 - 1 / 4) / (Y : ℂ) ^ 2) *
          d4BMCompletedEisensteinWeightedSignedWhittakerMode
            u negative N nu x Y -
        d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
          u negative N nu x Y := by
  have heigen := d4BM_signedWhittakerMode_secondJet_eigenEquation
    negative N nu x Y
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hsolve :
      d4BMSignedWhittakerModeVerticalSecondJet negative N nu x Y =
        ((nu ^ 2 - 1 / 4) / (Y : ℂ) ^ 2) *
            d4BMSignedWhittakerMode negative N nu x Y -
          d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y := by
    have hY2ne : (Y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hYne
    have hsum :
        d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y +
            d4BMSignedWhittakerModeVerticalSecondJet negative N nu x Y =
          ((nu ^ 2 - 1 / 4) *
            d4BMSignedWhittakerMode negative N nu x Y) / (Y : ℂ) ^ 2 := by
      apply (eq_div_iff hY2ne).2
      simpa only [mul_comm] using heigen
    calc
      _ = (d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y +
            d4BMSignedWhittakerModeVerticalSecondJet negative N nu x Y) -
          d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y := by ring
      _ = ((nu ^ 2 - 1 / 4) *
            d4BMSignedWhittakerMode negative N nu x Y) / (Y : ℂ) ^ 2 -
          d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y := by rw [hsum]
      _ = ((nu ^ 2 - 1 / 4) / (Y : ℂ) ^ 2) *
            d4BMSignedWhittakerMode negative N nu x Y -
          d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y := by ring
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
    d4BMCompletedEisensteinWeightedSignedWhittakerMode
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
  rw [hsolve]
  ring

theorem summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
        u negative N nu x ⟨Y, zero_lt_one.trans_le Y.2⟩) := by
  let Yp : D4BMPositiveReal := ⟨Y, zero_lt_one.trans_le Y.2⟩
  have hvalue :=
    (summable_d4BMCompletedEisensteinWeightedSignedWhittakerMode
      u nu negative x Y).mul_left ((nu ^ 2 - 1 / 4) / (Y : ℂ) ^ 2)
  have hxx :=
    summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u nu negative x Y
  apply (hvalue.sub hxx).congr
  intro N
  exact (d4BM_weightedSignedWhittakerVerticalSecondJet_eq_eigenReconstruction
    u negative N nu x Yp).symm

/-- Full componentwise `tsum` jet of one signed canonical Whittaker tail. -/
def d4BMCompletedEisensteinSignedTailFullSecondJet
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) : D4BMFullSecondJet where
  first :=
    { value := ∑' N : ℕ,
        d4BMCompletedEisensteinWeightedSignedWhittakerMode
          u negative N nu x Y
      tau := 0
      horizonX := ∑' N : ℕ,
        d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
          u negative N nu x Y
      sigma := ∑' N : ℕ,
        d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
          u negative N nu x Y
      xi := 0 }
  tauTau := 0
  tauHorizonX := 0
  tauSigma := 0
  tauXi := 0
  horizonXHorizonX := ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u negative N nu x Y
  horizonXSigma := ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u negative N nu x Y
  horizonXXi := 0
  sigmaSigma := ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u negative N nu x ⟨Y, zero_lt_one.trans_le Y.2⟩
  sigmaXi := 0
  xiXi := 0

/-- Literal raising commutes with the absolutely convergent signed full-second-jet sum. -/
theorem d4BM_maassRaise_signedTailFullSecondJet_eq_tsum
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinSignedTailFullSecondJet
          u nu negative x Y) =
      ∑' N : ℕ,
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
            (d4BMActualSignedWhittakerModeFullSecondJet
              negative N nu x ⟨Y, zero_lt_one.trans_le Y.2⟩) := by
  let Yp : D4BMPositiveReal := ⟨Y, zero_lt_one.trans_le Y.2⟩
  let yy : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u negative N nu x Yp
  let xx : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u negative N nu x Y
  let xy : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u negative N nu x Y
  let y1 : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u negative N nu x Y
  let x1 : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u negative N nu x Y
  let a : ℕ → ℂ := fun N => yy N - xx N + 2 * Complex.I * xy N
  let b : ℕ → ℂ := fun N => y1 N + Complex.I * x1 N
  have hyy : Summable yy := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u nu negative x Y
  have hxx : Summable xx := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u nu negative x Y
  have hxy : Summable xy := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u nu negative x Y
  have hy1 : Summable y1 := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u nu negative x Y
  have hx1 : Summable x1 := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u nu negative x Y
  have ha : Summable a := (hyy.sub hxx).add (hxy.mul_left (2 * Complex.I))
  have hb : Summable b := hy1.add (hx1.mul_left Complex.I)
  calc
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinSignedTailFullSecondJet u nu negative x Y) =
      (Y : ℂ) ^ 2 * (∑' N : ℕ, a N) +
        2 * (Y : ℂ) * (∑' N : ℕ, b N) := by
          unfold d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
            d4BMCompletedEisensteinSignedTailFullSecondJet
          simp only [a, b, yy, xx, xy, y1, x1]
          rw [(hyy.sub hxx).tsum_add (hxy.mul_left (2 * Complex.I)),
            hyy.tsum_sub hxx, tsum_mul_left,
            hy1.tsum_add (hx1.mul_left Complex.I), tsum_mul_left]
    _ = ∑' N : ℕ,
        ((Y : ℂ) ^ 2 * a N + 2 * (Y : ℂ) * b N) := by
          rw [← tsum_mul_left, ← tsum_mul_left]
          exact ((ha.mul_left ((Y : ℂ) ^ 2)).tsum_add
            (hb.mul_left (2 * (Y : ℂ)))).symm
    _ = ∑' N : ℕ,
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
            (d4BMActualSignedWhittakerModeFullSecondJet
              negative N nu x Yp) := by
          apply tsum_congr
          intro N
          unfold a b yy xx xy y1 x1
          unfold d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
            d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
            d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
            d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
            d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
            d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
            d4BMActualSignedWhittakerModeFullSecondJet
          ring

/-- Literal lowering commutes with the absolutely convergent signed full-second-jet sum. -/
theorem d4BM_maassLower_signedTailFullSecondJet_eq_tsum
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinSignedTailFullSecondJet
          u nu negative x Y) =
      ∑' N : ℕ,
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
            (d4BMActualSignedWhittakerModeFullSecondJet
              negative N nu x ⟨Y, zero_lt_one.trans_le Y.2⟩) := by
  let Yp : D4BMPositiveReal := ⟨Y, zero_lt_one.trans_le Y.2⟩
  let yy : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u negative N nu x Yp
  let xx : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u negative N nu x Y
  let xy : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u negative N nu x Y
  let y1 : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u negative N nu x Y
  let x1 : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u negative N nu x Y
  let a : ℕ → ℂ := fun N => yy N - xx N - 2 * Complex.I * xy N
  let b : ℕ → ℂ := fun N => y1 N - Complex.I * x1 N
  have hyy : Summable yy := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u nu negative x Y
  have hxx : Summable xx := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u nu negative x Y
  have hxy : Summable xy := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u nu negative x Y
  have hy1 : Summable y1 := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u nu negative x Y
  have hx1 : Summable x1 := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u nu negative x Y
  have ha : Summable a := (hyy.sub hxx).sub (hxy.mul_left (2 * Complex.I))
  have hb : Summable b := hy1.sub (hx1.mul_left Complex.I)
  calc
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinSignedTailFullSecondJet u nu negative x Y) =
      (Y : ℂ) ^ 2 * (∑' N : ℕ, a N) +
        2 * (Y : ℂ) * (∑' N : ℕ, b N) := by
          unfold d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
            d4BMCompletedEisensteinSignedTailFullSecondJet
          simp only [a, b, yy, xx, xy, y1, x1]
          rw [(hyy.sub hxx).tsum_sub (hxy.mul_left (2 * Complex.I)),
            hyy.tsum_sub hxx, tsum_mul_left,
            hy1.tsum_sub (hx1.mul_left Complex.I), tsum_mul_left]
    _ = ∑' N : ℕ,
        ((Y : ℂ) ^ 2 * a N + 2 * (Y : ℂ) * b N) := by
          rw [← tsum_mul_left, ← tsum_mul_left]
          exact ((ha.mul_left ((Y : ℂ) ^ 2)).tsum_add
            (hb.mul_left (2 * (Y : ℂ)))).symm
    _ = ∑' N : ℕ,
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
            (d4BMActualSignedWhittakerModeFullSecondJet
              negative N nu x Yp) := by
          apply tsum_congr
          intro N
          unfold a b yy xx xy y1 x1
          unfold d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
            d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
            d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
            d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
            d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
            d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
            d4BMActualSignedWhittakerModeFullSecondJet
          ring

/-- The literal signed-tail raising operator is exactly the canonical phased word; negative
frequency exchanges radial raising and lowering. -/
theorem d4BM_maassRaise_signedTailFullSecondJet_eq_phasedWord
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinSignedTailFullSecondJet
          u nu negative x Y) =
      d4BMCompletedEisensteinPhasedMaassWord
        (!negative) negative u nu x Y := by
  let Yp : D4BMPositiveReal := ⟨Y, zero_lt_one.trans_le Y.2⟩
  rw [d4BM_maassRaise_signedTailFullSecondJet_eq_tsum,
    d4BMCompletedEisensteinPhasedMaassWord_eq_expansion_tsum]
  apply tsum_congr
  intro N
  change d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Yp : ℂ)
        (d4BMActualSignedWhittakerModeFullSecondJet negative N nu x Yp) =
    d4BMCompletedEisensteinPhasedMaassExpansionSummand
      (!negative) negative u nu x Yp N
  rw [d4BMCompletedEisensteinPhasedMaassExpansionSummand_eq_mode]
  cases negative
  · change d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Yp : ℂ)
          (d4BMActualSignedWhittakerModeFullSecondJet false N nu x Yp) =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMCompletedEisensteinFourierPhase false N x *
          d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
            (d4BMPositiveFourierScale N) nu Yp)
    rw [d4BM_actualPositiveWhittakerMode_raise_eq_phase_mul]
  · change d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Yp : ℂ)
          (d4BMActualSignedWhittakerModeFullSecondJet true N nu x Yp) =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMCompletedEisensteinFourierPhase true N x *
          d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
            (d4BMPositiveFourierScale N) nu Yp)
    rw [d4BM_actualNegativeWhittakerMode_raise_eq_phase_mul_lower]

/-- The literal signed-tail lowering operator is exactly the opposite canonical phased word. -/
theorem d4BM_maassLower_signedTailFullSecondJet_eq_phasedWord
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinSignedTailFullSecondJet
          u nu negative x Y) =
      d4BMCompletedEisensteinPhasedMaassWord
        negative negative u nu x Y := by
  let Yp : D4BMPositiveReal := ⟨Y, zero_lt_one.trans_le Y.2⟩
  rw [d4BM_maassLower_signedTailFullSecondJet_eq_tsum,
    d4BMCompletedEisensteinPhasedMaassWord_eq_expansion_tsum]
  apply tsum_congr
  intro N
  change d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Yp : ℂ)
        (d4BMActualSignedWhittakerModeFullSecondJet negative N nu x Yp) =
    d4BMCompletedEisensteinPhasedMaassExpansionSummand
      negative negative u nu x Yp N
  rw [d4BMCompletedEisensteinPhasedMaassExpansionSummand_eq_mode]
  cases negative
  · change d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Yp : ℂ)
          (d4BMActualSignedWhittakerModeFullSecondJet false N nu x Yp) =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMCompletedEisensteinFourierPhase false N x *
          d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
            (d4BMPositiveFourierScale N) nu Yp)
    rw [d4BM_actualPositiveWhittakerMode_lower_eq_phase_mul]
  · change d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Yp : ℂ)
          (d4BMActualSignedWhittakerModeFullSecondJet true N nu x Yp) =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMCompletedEisensteinFourierPhase true N x *
          d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
            (d4BMPositiveFourierScale N) nu Yp)
    rw [d4BM_actualNegativeWhittakerMode_lower_eq_phase_mul_raise]

/-- Full two-sided nonzero-frequency second jet before the cusp-leg factor `2`. -/
def d4BMCompletedEisensteinFullSignedTailFullSecondJet
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) : D4BMFullSecondJet :=
  let Jp := d4BMCompletedEisensteinSignedTailFullSecondJet u u false x Y
  let Jn := d4BMCompletedEisensteinSignedTailFullSecondJet u u true x Y
  { first :=
      { value := Jp.first.value + Jn.first.value
        tau := 0
        horizonX := Jp.first.horizonX + Jn.first.horizonX
        sigma := Jp.first.sigma + Jn.first.sigma
        xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := Jp.horizonXHorizonX + Jn.horizonXHorizonX
    horizonXSigma := Jp.horizonXSigma + Jn.horizonXSigma
    horizonXXi := 0
    sigmaSigma := Jp.sigmaSigma + Jn.sigmaSigma
    sigmaXi := 0
    xiXi := 0 }

theorem d4BM_maassRaise_fullSignedTailFullSecondJet_eq_fullSignedRaiseWord
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y) =
      d4BMCompletedEisensteinFullSignedRaiseWord u u x Y := by
  let Jp := d4BMCompletedEisensteinSignedTailFullSecondJet u u false x Y
  let Jn := d4BMCompletedEisensteinSignedTailFullSecondJet u u true x Y
  have hsplit :
      d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
          (d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y) =
        d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ) Jp +
          d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ) Jn := by
    unfold d4BMCompletedEisensteinFullSignedTailFullSecondJet
      d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet Jp Jn
    ring
  rw [hsplit,
    d4BM_maassRaise_signedTailFullSecondJet_eq_phasedWord,
    d4BM_maassRaise_signedTailFullSecondJet_eq_phasedWord]
  rfl

theorem d4BM_maassLower_fullSignedTailFullSecondJet_eq_fullSignedLowerWord
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y) =
      d4BMCompletedEisensteinFullSignedLowerWord u u x Y := by
  let Jp := d4BMCompletedEisensteinSignedTailFullSecondJet u u false x Y
  let Jn := d4BMCompletedEisensteinSignedTailFullSecondJet u u true x Y
  have hsplit :
      d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
          (d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y) =
        d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ) Jp +
          d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ) Jn := by
    unfold d4BMCompletedEisensteinFullSignedTailFullSecondJet
      d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet Jp Jn
    ring
  rw [hsplit,
    d4BM_maassLower_signedTailFullSecondJet_eq_phasedWord,
    d4BM_maassLower_signedTailFullSecondJet_eq_phasedWord]
  rfl

/-- Literal full-second-jet evaluation of a positive-height complex power. -/
theorem d4BM_zeroFrequency_fullSecondJet_cpow
    (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (w * (w - 1) * (Y : ℂ) ^ (w - 2)) +
        2 * (Y : ℂ) * (w * (Y : ℂ) ^ (w - 1)) =
      w * (w + 1) * (Y : ℂ) ^ w := by
  have h1 := d4BM_zeroFrequency_cpow_mul_deriv w hY
  have hm := d4BM_zeroFrequency_cpow_mul_deriv (w - 1) hY
  have hm' :
      (Y : ℂ) * ((w - 1) * (Y : ℂ) ^ (w - 2)) =
        (w - 1) * (Y : ℂ) ^ (w - 1) := by
    have hshift : w - 1 - 1 = w - 2 := by ring
    simpa only [hshift] using hm
  calc
    (Y : ℂ) ^ 2 * (w * (w - 1) * (Y : ℂ) ^ (w - 2)) +
        2 * (Y : ℂ) * (w * (Y : ℂ) ^ (w - 1)) =
      w * (Y : ℂ) *
          ((Y : ℂ) * ((w - 1) * (Y : ℂ) ^ (w - 2))) +
        2 * ((Y : ℂ) * (w * (Y : ℂ) ^ (w - 1))) := by ring
    _ = w * (Y : ℂ) * ((w - 1) * (Y : ℂ) ^ (w - 1)) +
        2 * ((Y : ℂ) * (w * (Y : ℂ) ^ (w - 1))) := by rw [hm']
    _ = (w - 1) * ((Y : ℂ) * (w * (Y : ℂ) ^ (w - 1))) +
        2 * ((Y : ℂ) * (w * (Y : ℂ) ^ (w - 1))) := by ring
    _ = (w - 1) * (w * (Y : ℂ) ^ w) + 2 * (w * (Y : ℂ) ^ w) := by rw [h1]
    _ = w * (w + 1) * (Y : ℂ) ^ w := by ring

def d4BMCompletedEisensteinCuspConstantFirstJetTerm
    (u : ℂ) (epsilon : Bool) (Y : ℝ) : ℂ :=
  let w := d4BMCompletedEisensteinCuspWeylExponent u epsilon
  d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
    (w * (Y : ℂ) ^ (w - 1))

def d4BMCompletedEisensteinCuspConstantSecondJetTerm
    (u : ℂ) (epsilon : Bool) (Y : ℝ) : ℂ :=
  let w := d4BMCompletedEisensteinCuspWeylExponent u epsilon
  d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
    (w * (w - 1) * (Y : ℂ) ^ (w - 2))

/-- Genuine zero-frequency full second jet of both Weyl powers. -/
def d4BMCompletedEisensteinCuspConstantFullSecondJet
    (u : ℂ) (Y : ℝ) : D4BMFullSecondJet where
  first :=
    { value := d4BMCompletedEisensteinCuspConstantPart .scalar u Y
      tau := 0
      horizonX := 0
      sigma :=
        d4BMCompletedEisensteinCuspConstantFirstJetTerm u false Y +
          d4BMCompletedEisensteinCuspConstantFirstJetTerm u true Y
      xi := 0 }
  tauTau := 0
  tauHorizonX := 0
  tauSigma := 0
  tauXi := 0
  horizonXHorizonX := 0
  horizonXSigma := 0
  horizonXXi := 0
  sigmaSigma :=
    d4BMCompletedEisensteinCuspConstantSecondJetTerm u false Y +
      d4BMCompletedEisensteinCuspConstantSecondJetTerm u true Y
  sigmaXi := 0
  xiXi := 0

theorem d4BM_maassRaise_cuspConstantFullSecondJet_eq_constantPart
    (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinCuspConstantFullSecondJet u Y) =
      d4BMCompletedEisensteinCuspConstantPart .raise u Y := by
  have h0 := d4BM_zeroFrequency_fullSecondJet_cpow
    (d4BMCompletedEisensteinCuspWeylExponent u false) hY
  have h1 := d4BM_zeroFrequency_fullSecondJet_cpow
    (d4BMCompletedEisensteinCuspWeylExponent u true) hY
  unfold d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
    d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspConstantFirstJetTerm
    d4BMCompletedEisensteinCuspConstantSecondJetTerm
    d4BMCompletedEisensteinCuspConstantPart
    d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  linear_combination
    d4BMCompletedEisensteinCuspConstantCoefficient u false * h0 +
      d4BMCompletedEisensteinCuspConstantCoefficient u true * h1

theorem d4BM_maassLower_cuspConstantFullSecondJet_eq_constantPart
    (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinCuspConstantFullSecondJet u Y) =
      d4BMCompletedEisensteinCuspConstantPart .lower u Y := by
  have h0 := d4BM_zeroFrequency_fullSecondJet_cpow
    (d4BMCompletedEisensteinCuspWeylExponent u false) hY
  have h1 := d4BM_zeroFrequency_fullSecondJet_cpow
    (d4BMCompletedEisensteinCuspWeylExponent u true) hY
  unfold d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
    d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspConstantFirstJetTerm
    d4BMCompletedEisensteinCuspConstantSecondJetTerm
    d4BMCompletedEisensteinCuspConstantPart
    d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  linear_combination
    d4BMCompletedEisensteinCuspConstantCoefficient u false * h0 +
      d4BMCompletedEisensteinCuspConstantCoefficient u true * h1

/-- Full canonical scalar cusp jet: both Weyl powers plus twice the two-sided Whittaker jet. -/
def d4BMCompletedEisensteinCanonicalCuspFullSecondJet
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) : D4BMFullSecondJet :=
  let Jc := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
  let Jt := d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y
  { first :=
      { value := Jc.first.value + 2 * Jt.first.value
        tau := 0
        horizonX := 2 * Jt.first.horizonX
        sigma := Jc.first.sigma + 2 * Jt.first.sigma
        xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := 2 * Jt.horizonXHorizonX
    horizonXSigma := 2 * Jt.horizonXSigma
    horizonXXi := 0
    sigmaSigma := Jc.sigmaSigma + 2 * Jt.sigmaSigma
    sigmaXi := 0
    xiXi := 0 }

theorem d4BM_maassRaise_canonicalCuspFullSecondJet_eq_cuspLeg
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y) =
      d4BMCompletedEisensteinCuspLeg .raise u x Y := by
  let Jc := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
  let Jt := d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y
  have hsplit :
      d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y) =
        d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ) Jc +
          2 * d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ) Jt := by
    unfold d4BMCompletedEisensteinCanonicalCuspFullSecondJet
      d4BMCompletedEisensteinCuspConstantFullSecondJet
      d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet Jc Jt
    simp only [d4BMCompletedEisensteinCuspConstantFullSecondJet]
    ring
  rw [hsplit, d4BM_maassRaise_cuspConstantFullSecondJet_eq_constantPart
    u (zero_lt_one.trans_le Y.2),
    d4BM_maassRaise_fullSignedTailFullSecondJet_eq_fullSignedRaiseWord]
  rfl

theorem d4BM_maassLower_canonicalCuspFullSecondJet_eq_cuspLeg
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y) =
      d4BMCompletedEisensteinCuspLeg .lower u x Y := by
  let Jc := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
  let Jt := d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y
  have hsplit :
      d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y) =
        d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ) Jc +
          2 * d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ) Jt := by
    unfold d4BMCompletedEisensteinCanonicalCuspFullSecondJet
      d4BMCompletedEisensteinCuspConstantFullSecondJet
      d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet Jc Jt
    simp only [d4BMCompletedEisensteinCuspConstantFullSecondJet]
    ring
  rw [hsplit, d4BM_maassLower_cuspConstantFullSecondJet_eq_constantPart
    u (zero_lt_one.trans_le Y.2),
    d4BM_maassLower_fullSignedTailFullSecondJet_eq_fullSignedLowerWord]
  rfl

theorem d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.value =
      d4BMCompletedEisensteinCuspLeg .scalar u x Y := by
  unfold d4BMCompletedEisensteinCanonicalCuspFullSecondJet
    d4BMCompletedEisensteinFullSignedTailFullSecondJet
    d4BMCompletedEisensteinSignedTailFullSecondJet
    d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspLeg
    d4BMCompletedEisensteinCuspTailPart
    d4BMCompletedEisensteinFullSignedZeroWord
  rw [d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_weightedMode_tsum,
    d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_weightedMode_tsum]

theorem hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_horizontal
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ => d4BMCompletedEisensteinCuspLeg .scalar u q Y)
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.horizonX x := by
  have hp := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_horizontal
    u u false x Y
  have hn := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_horizontal
    u u true x Y
  have ht := (hp.add hn).const_mul (2 : ℂ)
  simpa [d4BMCompletedEisensteinCuspLeg,
    d4BMCompletedEisensteinCuspTailPart,
    d4BMCompletedEisensteinFullSignedZeroWord,
    d4BMCompletedEisensteinCanonicalCuspFullSecondJet,
    d4BMCompletedEisensteinFullSignedTailFullSecondJet,
    d4BMCompletedEisensteinSignedTailFullSecondJet,
    d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail] using ht

theorem hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_vertical
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ => d4BMCompletedEisensteinCuspLeg .scalar u x q)
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.sigma Y := by
  let w0 := d4BMCompletedEisensteinCuspWeylExponent u false
  let w1 := d4BMCompletedEisensteinCuspWeylExponent u true
  have hc0 := (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
      (zero_lt_one.trans_le Y.2) :
    HasDerivAt (fun q : ℝ => (q : ℂ) ^ w0)
      (w0 * (Y : ℂ) ^ (w0 - 1)) Y).const_mul
        (d4BMCompletedEisensteinCuspConstantCoefficient u false)
  have hc1 := (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
      (zero_lt_one.trans_le Y.2) :
    HasDerivAt (fun q : ℝ => (q : ℂ) ^ w1)
      (w1 * (Y : ℂ) ^ (w1 - 1)) Y).const_mul
        (d4BMCompletedEisensteinCuspConstantCoefficient u true)
  have hp := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_vertical
    u u false x Y
  have hn := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_vertical
    u u true x Y
  have h := (hc0.add hc1).add ((hp.add hn).const_mul (2 : ℂ))
  have hfun :
      (fun q : ℝ => d4BMCompletedEisensteinCuspLeg .scalar u x q) =ᶠ[𝓝 (Y : ℝ)]
        (((fun q : ℝ =>
            d4BMCompletedEisensteinCuspConstantCoefficient u false * (q : ℂ) ^ w0) +
          (fun q : ℝ =>
            d4BMCompletedEisensteinCuspConstantCoefficient u true * (q : ℂ) ^ w1)) +
          fun q : ℝ => 2 *
            (d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false x 0 0 q +
              d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true x 0 0 q)) := by
    exact Filter.Eventually.of_forall fun q => by
      unfold d4BMCompletedEisensteinCuspLeg
        d4BMCompletedEisensteinCuspConstantPart
        d4BMCompletedEisensteinCuspConstantTerm
        d4BMCompletedEisensteinCuspConstantMaassFactor
        d4BMCompletedEisensteinCuspTailPart
        d4BMCompletedEisensteinFullSignedZeroWord w0 w1
      simp only [Pi.add_apply]
      ring
  have h' := h.congr_of_eventuallyEq hfun
  refine h'.congr_deriv ?_
  unfold d4BMCompletedEisensteinCanonicalCuspFullSecondJet
    d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspConstantFirstJetTerm
    d4BMCompletedEisensteinFullSignedTailFullSecondJet
    d4BMCompletedEisensteinSignedTailFullSecondJet
    d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail w0 w1
  ring

theorem hasDerivAt_d4BMCanonicalCuspHorizontalFirstJet_horizontal
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ =>
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u q Y).first.horizonX)
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).horizonXHorizonX x := by
  have hp :=
    hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail_horizontal
      u u false x Y
  have hn :=
    hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail_horizontal
      u u true x Y
  have h := (hp.add hn).const_mul (2 : ℂ)
  simpa [d4BMCompletedEisensteinCanonicalCuspFullSecondJet,
    d4BMCompletedEisensteinFullSignedTailFullSecondJet,
    d4BMCompletedEisensteinSignedTailFullSecondJet,
    d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail,
    d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalSecondJetTail] using h

theorem hasDerivAt_d4BMCanonicalCuspVerticalFirstJet_horizontal
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ =>
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u q Y).first.sigma)
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).horizonXSigma x := by
  have hp :=
    hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail_horizontal
      u u false x Y
  have hn :=
    hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail_horizontal
      u u true x Y
  have ht := (hp.add hn).const_mul (2 : ℂ)
  simpa [d4BMCompletedEisensteinCanonicalCuspFullSecondJet,
    d4BMCompletedEisensteinCuspConstantFullSecondJet,
    d4BMCompletedEisensteinFullSignedTailFullSecondJet,
    d4BMCompletedEisensteinSignedTailFullSecondJet,
    d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail,
    d4BMCompletedEisensteinSignedSqrtWhittakerMixedSecondJetTail] using ht

theorem d4BM_signedTailFullSecondJet_eigenEquation
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    (Y : ℂ) ^ 2 *
        ((d4BMCompletedEisensteinSignedTailFullSecondJet
            u nu negative x Y).horizonXHorizonX +
          (d4BMCompletedEisensteinSignedTailFullSecondJet
            u nu negative x Y).sigmaSigma) =
      (nu ^ 2 - 1 / 4) *
        (d4BMCompletedEisensteinSignedTailFullSecondJet
          u nu negative x Y).first.value := by
  let Yp : D4BMPositiveReal := ⟨Y, zero_lt_one.trans_le Y.2⟩
  let v : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerMode
      u negative N nu x Y
  let xx : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u negative N nu x Y
  let yy : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u negative N nu x Yp
  have hv : Summable v := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerMode
      u nu negative x Y
  have hxx : Summable xx := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u nu negative x Y
  have hyy : Summable yy := by
    exact summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
      u nu negative x Y
  unfold d4BMCompletedEisensteinSignedTailFullSecondJet
  change (Y : ℂ) ^ 2 * ((∑' N : ℕ, xx N) + ∑' N : ℕ, yy N) =
    (nu ^ 2 - 1 / 4) * ∑' N : ℕ, v N
  rw [← hxx.tsum_add hyy, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro N
  unfold v xx yy
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerMode
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalSecondJet
  linear_combination
    d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      d4BM_signedWhittakerMode_secondJet_eigenEquation negative N nu x Yp

theorem d4BM_zeroFrequency_secondJet_cpow_eigenEquation
    (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (w * (w - 1) * (Y : ℂ) ^ (w - 2)) =
      w * (w - 1) * (Y : ℂ) ^ w := by
  have hfull := d4BM_zeroFrequency_fullSecondJet_cpow w hY
  have hfirst := d4BM_zeroFrequency_cpow_mul_deriv w hY
  linear_combination hfull - 2 * hfirst

theorem d4BM_cuspConstantFullSecondJet_eigenEquation
    (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 *
        (d4BMCompletedEisensteinCuspConstantFullSecondJet u Y).sigmaSigma =
      (u ^ 2 - 1 / 4) *
        (d4BMCompletedEisensteinCuspConstantFullSecondJet u Y).first.value := by
  let w0 := d4BMCompletedEisensteinCuspWeylExponent u false
  let w1 := d4BMCompletedEisensteinCuspWeylExponent u true
  have h0 := d4BM_zeroFrequency_secondJet_cpow_eigenEquation w0 hY
  have h1 := d4BM_zeroFrequency_secondJet_cpow_eigenEquation w1 hY
  have hw0 : w0 * (w0 - 1) = u ^ 2 - 1 / 4 := by
    simp [w0, d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
    ring
  have hw1 : w1 * (w1 - 1) = u ^ 2 - 1 / 4 := by
    simp [w1, d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
    ring
  rw [hw0] at h0
  rw [hw1] at h1
  unfold d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspConstantSecondJetTerm
    d4BMCompletedEisensteinCuspConstantPart
    d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  simp only [mul_one]
  dsimp [w0, w1] at h0 h1 hw0 hw1
  rw [hw0, hw1]
  linear_combination
    d4BMCompletedEisensteinCuspConstantCoefficient u false * h0 +
      d4BMCompletedEisensteinCuspConstantCoefficient u true * h1

theorem d4BM_fullSignedTailFullSecondJet_eigenEquation
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    (Y : ℂ) ^ 2 *
        ((d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y).horizonXHorizonX +
          (d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y).sigmaSigma) =
      (u ^ 2 - 1 / 4) *
        (d4BMCompletedEisensteinFullSignedTailFullSecondJet u x Y).first.value := by
  have hp := d4BM_signedTailFullSecondJet_eigenEquation u u false x Y
  have hn := d4BM_signedTailFullSecondJet_eigenEquation u u true x Y
  unfold d4BMCompletedEisensteinFullSignedTailFullSecondJet
  linear_combination hp + hn

theorem d4BM_canonicalCuspFullSecondJet_eigenEquation
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    (Y : ℂ) ^ 2 *
        ((d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).horizonXHorizonX +
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).sigmaSigma) =
      (u ^ 2 - 1 / 4) *
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.value := by
  have hc := d4BM_cuspConstantFullSecondJet_eigenEquation
    u (zero_lt_one.trans_le Y.2)
  have ht := d4BM_fullSignedTailFullSecondJet_eigenEquation u x Y
  unfold d4BMCompletedEisensteinCanonicalCuspFullSecondJet
  linear_combination hc + 2 * ht

/-- Upper-half-plane points in the exterior cusp, with the height condition carried by the
coordinate rather than exposed as a theorem hypothesis. -/
abbrev D4BMExteriorCuspCoordinate :=
  {z : D4BMUpperHalfPlaneCoordinate // 1 ≤ z.y}

def d4BMExteriorCuspHeight (Z : D4BMExteriorCuspCoordinate) :
    {y : ℝ // 1 ≤ y} :=
  ⟨Z.1.y, Z.2⟩

theorem d4BM_actualCanonical_exterior_value_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedEisensteinPoincareSeries Z.1 P =
      d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2)
        Z.1.x (d4BMExteriorCuspHeight Z) := by
  have h := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg Z.1 P Z.1.x
  simpa [d4BMCompletedEisensteinHorizontalFunction,
    d4BMHorizontalCoordinate, d4BMExteriorCuspHeight] using h

theorem d4BM_actualCanonical_exterior_horizontalFirstJet_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate Z.1 x) P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)).first.horizonX := by
  have ha : HasDerivAt
      (fun q : ℝ => d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate Z.1 q) P)
      (d4BMCompletedPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate Z.1 x) P) x := by
    simpa [d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal
        (d4BMHorizontalCoordinate Z.1 x) P
  have hc := hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_horizontal
    (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)
  have hfun :
      (fun q : ℝ => d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate Z.1 q) P) =
      (fun q : ℝ => d4BMCompletedEisensteinCuspLeg .scalar
        (P.s - 1 / 2) q (d4BMExteriorCuspHeight Z)) := by
    funext q
    simpa [d4BMCompletedEisensteinHorizontalFunction,
      d4BMExteriorCuspHeight] using
        d4BM_actualCompletedPoincare_eq_canonicalCuspLeg Z.1 P q
  rw [hfun] at ha
  exact ha.unique hc

theorem d4BM_actualCanonical_exterior_horizontalSecondJet_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedPoincareHorizontalSecondJet
        (d4BMHorizontalCoordinate Z.1 x) P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)).horizonXHorizonX := by
  have ha : HasDerivAt
      (fun q : ℝ => d4BMCompletedPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate Z.1 q) P)
      (d4BMCompletedPoincareHorizontalSecondJet
        (d4BMHorizontalCoordinate Z.1 x) P) x := by
    simpa [d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal
        (d4BMHorizontalCoordinate Z.1 x) P
  have hc := hasDerivAt_d4BMCanonicalCuspHorizontalFirstJet_horizontal
    (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)
  have hfun :
      (fun q : ℝ => d4BMCompletedPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate Z.1 q) P) =
      (fun q : ℝ =>
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
          (P.s - 1 / 2) q (d4BMExteriorCuspHeight Z)).first.horizonX) := by
    funext q
    exact d4BM_actualCanonical_exterior_horizontalFirstJet_eq Z P q
  rw [hfun] at ha
  exact ha.unique hc

theorem d4BM_actualCanonical_exterior_verticalSlice_eventuallyEq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalSlice Z.1 P =ᶠ[𝓝 Z.1.y]
      (fun q : ℝ => d4BMCompletedEisensteinCuspLeg .scalar
        (P.s - 1 / 2) Z.1.x q) := by
  filter_upwards [eventually_gt_nhds Z.1.y_pos] with q hq
  let zq : D4BMUpperHalfPlaneCoordinate := ⟨Z.1.x, q, hq⟩
  calc
    d4BMCompletedPoincareVerticalSlice Z.1 P q =
        d4BMCompletedEisensteinPoincareSeries zq P := by rfl
    _ = d4BMCompletedEisensteinHorizontalFunction zq P Z.1.x := by rfl
    _ = d4BMCompletedEisensteinCuspLeg .scalar
        (P.s - 1 / 2) Z.1.x q := by
      simpa [zq] using
        d4BM_actualCompletedPoincare_eq_canonicalCuspLeg zq P Z.1.x

theorem d4BM_actualCanonical_exterior_verticalFirstJet_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalFirstJet Z.1 P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).first.sigma := by
  have ha := hasDerivAt_d4BMCompletedPoincareVerticalSlice Z.1 P
  have hc := hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_vertical
    (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)
  have hc' := hc.congr_of_eventuallyEq
    (d4BM_actualCanonical_exterior_verticalSlice_eventuallyEq Z P)
  exact ha.unique hc'

def d4BMExteriorCuspHorizontalCoordinate
    (Z : D4BMExteriorCuspCoordinate) (x : ℝ) : D4BMExteriorCuspCoordinate :=
  ⟨d4BMHorizontalCoordinate Z.1 x, by
    simpa [d4BMHorizontalCoordinate] using Z.2⟩

theorem d4BM_actualCanonical_exterior_verticalFirstJet_horizontal_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedPoincareVerticalFirstJet
        (d4BMHorizontalCoordinate Z.1 x) P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)).first.sigma := by
  simpa [d4BMExteriorCuspHorizontalCoordinate, d4BMExteriorCuspHeight,
    d4BMHorizontalCoordinate] using
      d4BM_actualCanonical_exterior_verticalFirstJet_eq
        (d4BMExteriorCuspHorizontalCoordinate Z x) P

theorem d4BM_actualCanonical_exterior_mixedSecondJet_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedPoincareMixedSecondJet
        (d4BMHorizontalCoordinate Z.1 x) P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)).horizonXSigma := by
  have ha : HasDerivAt
      (fun q : ℝ => d4BMCompletedPoincareVerticalFirstJet
        (d4BMHorizontalCoordinate Z.1 q) P)
      (d4BMCompletedPoincareMixedSecondJet
        (d4BMHorizontalCoordinate Z.1 x) P) x := by
    simpa [d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareVerticalFirstJet_horizontal
        (d4BMHorizontalCoordinate Z.1 x) P
  have hc := hasDerivAt_d4BMCanonicalCuspVerticalFirstJet_horizontal
    (P.s - 1 / 2) x (d4BMExteriorCuspHeight Z)
  have hfun :
      (fun q : ℝ => d4BMCompletedPoincareVerticalFirstJet
        (d4BMHorizontalCoordinate Z.1 q) P) =
      (fun q : ℝ =>
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
          (P.s - 1 / 2) q (d4BMExteriorCuspHeight Z)).first.sigma) := by
    funext q
    exact d4BM_actualCanonical_exterior_verticalFirstJet_horizontal_eq Z P q
  rw [hfun] at ha
  exact ha.unique hc

theorem d4BM_actualCanonical_exterior_verticalSecondJet_eq
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalSecondJet Z.1 P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).sigmaSigma := by
  have hactual :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue Z.1 P
  have hcanonical := d4BM_canonicalCuspFullSecondJet_eigenEquation
    (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)
  have hcanonicalValue := d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg
    (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)
  have hvalue := d4BM_actualCanonical_exterior_value_eq Z P
  have hxx : d4BMCompletedPoincareHorizontalSecondJet Z.1 P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).horizonXHorizonX := by
    simpa [d4BMHorizontalCoordinate] using
      d4BM_actualCanonical_exterior_horizontalSecondJet_eq Z P Z.1.x
  have hlambda :
      (P.s - 1 / 2) ^ 2 - 1 / 4 = P.s * (P.s - 1) := by ring
  have hheight : ((d4BMExteriorCuspHeight Z : ℝ) : ℂ) = (Z.1.y : ℂ) := rfl
  rw [hlambda] at hcanonical
  rw [hcanonicalValue] at hcanonical
  rw [hheight] at hcanonical
  rw [hvalue, hxx] at hactual
  have hmul :
      (Z.1.y : ℂ) ^ 2 * d4BMCompletedPoincareVerticalSecondJet Z.1 P =
        (Z.1.y : ℂ) ^ 2 *
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
            (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).sigmaSigma := by
    linear_combination hactual - hcanonical
  exact mul_left_cancel₀
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt Z.1.y_pos))) hmul

/-- **Actual/canonical exterior-cusp second-jet weld.**  Global Fourier uniqueness and genuine
derivative uniqueness determine every first and mixed/horizontal second component.  The two exact
eigen equations then determine the remaining radial second component. -/
theorem d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualCompletedPoincareFullSecondJet Z.1 P =
      d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z) := by
  have hvalue := d4BM_actualCanonical_exterior_value_eq Z P
  have hx : d4BMCompletedPoincareHorizontalFirstJet Z.1 P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).first.horizonX := by
    simpa [d4BMHorizontalCoordinate] using
      d4BM_actualCanonical_exterior_horizontalFirstJet_eq Z P Z.1.x
  have hy := d4BM_actualCanonical_exterior_verticalFirstJet_eq Z P
  have hxx : d4BMCompletedPoincareHorizontalSecondJet Z.1 P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).horizonXHorizonX := by
    simpa [d4BMHorizontalCoordinate] using
      d4BM_actualCanonical_exterior_horizontalSecondJet_eq Z P Z.1.x
  have hxy : d4BMCompletedPoincareMixedSecondJet Z.1 P =
      (d4BMCompletedEisensteinCanonicalCuspFullSecondJet
        (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)).horizonXSigma := by
    simpa [d4BMHorizontalCoordinate] using
      d4BM_actualCanonical_exterior_mixedSecondJet_eq Z P Z.1.x
  have hyy := d4BM_actualCanonical_exterior_verticalSecondJet_eq Z P
  unfold d4BMActualCompletedPoincareFullSecondJet
    d4BMActualCompletedPoincareFullFirstJet
  rw [hvalue, hx, hy, hxx, hxy, hyy]
  rw [← d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg
    (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)]
  rfl

/-- **Literal exterior-cusp raising weld.**  The actual completed Poincare second jet, acted on by
the genuine two-step Maass raising operator, is exactly the canonical completed weight `+4` cusp
leg.  The exterior height condition is data of `Z`, so the theorem has no logical premise. -/
theorem d4BM_actualCompletedPoincareRaiseLeg_eq_canonicalCuspLeg
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualCompletedPoincareRaiseLeg Z.1 P =
      d4BMCompletedEisensteinCuspLeg .raise (P.s - 1 / 2)
        Z.1.x (d4BMExteriorCuspHeight Z) := by
  unfold d4BMActualCompletedPoincareRaiseLeg
  rw [d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z P]
  exact d4BM_maassRaise_canonicalCuspFullSecondJet_eq_cuspLeg
    (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)

/-- **Literal exterior-cusp lowering weld.**  The actual completed Poincare second jet, acted on by
the genuine two-step Maass lowering operator, is exactly the canonical completed weight `-4` cusp
leg, again with no logical premise. -/
theorem d4BM_actualCompletedPoincareLowerLeg_eq_canonicalCuspLeg
    (Z : D4BMExteriorCuspCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualCompletedPoincareLowerLeg Z.1 P =
      d4BMCompletedEisensteinCuspLeg .lower (P.s - 1 / 2)
        Z.1.x (d4BMExteriorCuspHeight Z) := by
  unfold d4BMActualCompletedPoincareLowerLeg
  rw [d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z P]
  exact d4BM_maassLower_canonicalCuspFullSecondJet_eq_cuspLeg
    (P.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z)

end
end RHTower
