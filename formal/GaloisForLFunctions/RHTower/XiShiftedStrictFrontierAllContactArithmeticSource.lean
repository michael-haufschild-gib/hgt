import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWallSecondResidue
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionBilinearContactSource
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Strict-frontier all-contact arithmetic source

This file removes infinite local flatness from the mass-shifted spectral-face frontier.  At every
occupied physical strict frontier, the first Padé defect occurs at a finite contact order.  Simple
contact is exactly the negative first omitted remainder.  Every higher contact is exactly an
admission-sensitive bilinear completed arithmetic source, formed from two null-ideal lifts before
rational--Gamma and von-Mangoldt aggregation.  Its alternating sign is forced by the positive
chamber to the right.

Thus higher contact is not another orientation map or fixed linear reporter: contact order itself
selects the source polynomial `P * X^(d-2)`, and the resulting source lands on the first live normal
coordinate.  The remaining global obstruction is cofinal escape of contact degree/source price,
not infinite-order contact at any one frontier.
-/

open Filter Matrix Polynomial Set Topology Asymptotics

namespace RHTower

noncomputable section

/-- Canonical terminal-normalized null vector on the singular block at the `n`-th strict step. -/
noncomputable def xiShiftedStrictFrontierNullVector (n : ℕ) : Fin (n + 3) → ℝ :=
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)

/-- Padé normal defect observed in the canonical null direction at the strict frontier. -/
noncomputable def xiShiftedStrictFrontierPadeDefect
    (n k : ℕ) : ℝ :=
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  xiShiftedHankelBoundaryPadeDefect y (xiShiftedStrictFrontierNullVector n) k

/-- Source-first higher-contact producer.  Admission chooses `P`; contact order chooses its
`X^(d-2)` lift; bilinear shear is formed before completed arithmetic aggregation. -/
noncomputable def xiShiftedStrictFrontierHigherContactArithmeticSource
    (n d : ℕ) : ℝ :=
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let c := xiShiftedStrictFrontierNullVector n
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  xiShiftedAdaptiveBilinearCompletedArithmeticSource
    (Real.sqrt y) (P * X ^ (d - 2)) P

/-- Complete finite-contact arithmetic law at one strict frontier.  The same witness `d` records
all dead lower normal coordinates, the first signed live coordinate, and its exact arithmetic
capitalization. -/
def XiShiftedStrictFrontierFiniteArithmeticContactLaw (n : ℕ) : Prop :=
  let m := n + 2
  ∃ d : ℕ, 0 < d ∧
    (∀ k < 2 * m + d, xiShiftedStrictFrontierPadeDefect n k = 0) ∧
    0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * m + d) ∧
    ((d = 1 ∧ xiShiftedStrictFrontierFirstOmittedRemainder n < 0) ∨
      (2 ≤ d ∧
        xiShiftedStrictFrontierHigherContactArithmeticSource n d =
          ((2 * m + d : ℕ) : ℝ) *
            xiShiftedStrictFrontierPadeDefect n (2 * m + d) ∧
        0 < (-1 : ℝ) ^ d *
          xiShiftedStrictFrontierHigherContactArithmeticSource n d))

/-- **Finite-contact arithmetic capitalization.**  Every occupied physical strict frontier has a
finite first normal contact.  Order one is the negative omitted remainder; every order at least two
is the exact nonzero adaptive bilinear completed arithmetic source selected before aggregation. -/
theorem xiShiftedStrictFrontier_finiteArithmeticContactLaw
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    XiShiftedStrictFrontierFiniteArithmeticContactLaw n := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let c := xiShiftedStrictFrontierNullVector n
  have hy : 0 < y := by
    dsimp only [y]
    linarith
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y m).PosDef := by
    simpa only [y, m] using hface.1
  have hflat : xiShiftedMomentHankelMatrix y (m + 1) *ᵥ c = 0 := by
    have h := xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
    simpa only [y, m, c, xiShiftedStrictFrontierNullVector, Nat.add_assoc] using h
  have hlast : c (Fin.last m) ≠ 0 := by
    simp [c, xiShiftedStrictFrontierNullVector, m]
  have hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (m + 1)).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hpos : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (y + u) k).re) (n + 3)).PosDef := by
      apply xiShiftedHigherBlock_posDef_of_terminalFrontier_lt (n := n + 1)
      · exact (add_pos hy hu).le
      · simpa only [y] using
          (lt_add_of_pos_right (xiShiftedHigherBlockTerminalFrontier (n + 1)) hu)
    change (xiShiftedMomentHankelMatrix (y + u) (n + 3)).PosSemidef
    exact hpos.posSemidef
  obtain ⟨d, hd, hzero, hsigned⟩ :=
    exists_signed_first_xiShiftedHankelBoundaryPadeDefect_of_right_posSemidef
      hy c hhead hflat hlast hright
  dsimp only [XiShiftedStrictFrontierFiniteArithmeticContactLaw]
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · intro k hk
    simpa only [m, c, xiShiftedStrictFrontierPadeDefect, y,
      xiShiftedStrictFrontierNullVector] using hzero k hk
  · simpa only [m, c, xiShiftedStrictFrontierPadeDefect, y,
      xiShiftedStrictFrontierNullVector] using hsigned
  · by_cases hd1 : d = 1
    · left
      refine ⟨hd1, ?_⟩
      have hfirst := xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
        c hhead hflat hlast
      have hsigned' : 0 < (-1 : ℝ) ^ d *
          xiShiftedHankelBoundaryPadeDefect y c (2 * m + d) := hsigned
      rw [hd1] at hsigned'
      have hrem : xiShiftedHankelBoundaryMonicRemainder y c < 0 := by
        rw [show 2 * m + 1 = 2 * m + 1 by rfl, hfirst] at hsigned'
        norm_num at hsigned'
        linarith
      simpa only [xiShiftedStrictFrontierFirstOmittedRemainder, y, m, c,
        xiShiftedStrictFrontierNullVector] using hrem
    · right
      have hd2 : 2 ≤ d := by omega
      have hy0 : 0 ≤ y := hy.le
      have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
      have hsqrt : 1 / 2 < Real.sqrt y := by
        nlinarith [Real.sqrt_nonneg y]
      have hsource :=
        xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_firstPadeDefect
          (i := d - 2) (j := 0) hsqrt hd2 (by omega)
          c hlast (by
            intro k hk
            rw [hsq]
            exact hzero k hk)
      dsimp only at hsource
      rw [hsq] at hsource
      have hsourceEq : xiShiftedStrictFrontierHigherContactArithmeticSource n d =
          ((2 * m + d : ℕ) : ℝ) * xiShiftedStrictFrontierPadeDefect n (2 * m + d) := by
        change xiShiftedAdaptiveBilinearCompletedArithmeticSource
            (Real.sqrt y)
            (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ (d - 2))
            (HTGeometry.finiteHankelNullMonicPolynomial c) = _
        simpa only [xiShiftedStrictFrontierPadeDefect, y, m, c,
          xiShiftedStrictFrontierNullVector, pow_zero, mul_one] using hsource
      refine ⟨hd2, hsourceEq, ?_⟩
      rw [hsourceEq]
      have hfactor : 0 < (((2 * m + d : ℕ) : ℝ)) := by positivity
      calc
        (-1 : ℝ) ^ d *
            (((2 * m + d : ℕ) : ℝ) *
              xiShiftedStrictFrontierPadeDefect n (2 * m + d)) =
            ((2 * m + d : ℕ) : ℝ) *
              ((-1 : ℝ) ^ d * xiShiftedStrictFrontierPadeDefect n (2 * m + d)) := by ring
        _ > 0 := mul_pos hfactor (by
          simpa only [m, c, xiShiftedStrictFrontierPadeDefect, y,
            xiShiftedStrictFrontierNullVector] using hsigned)

theorem det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
    {y : ℝ} {n : ℕ}
    (hdet : (xiShiftedMomentHankelMatrix y n).det ≠ 0) :
    (xiShiftedMomentHankelMatrix y (n + 1)).det =
      (xiShiftedMomentHankelMatrix y n).det *
        xiShiftedCanonicalAdmissionNorm y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let A : Matrix (Fin n) (Fin n) ℝ := HTGeometry.momentHankelMatrix s n
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  let M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    Matrix.reindex e.symm e.symm (xiShiftedMomentHankelMatrix y (n + 1))
  let B : Matrix (Fin n) (Fin 1) ℝ := M.toBlocks₁₂
  let C : Matrix (Fin 1) (Fin n) ℝ := M.toBlocks₂₁
  let D : Matrix (Fin 1) (Fin 1) ℝ := M.toBlocks₂₂
  have h11 : M.toBlocks₁₁ = A := by
    ext i j
    rfl
  have hblock : Matrix.fromBlocks A B C D = M := by
    rw [← h11]
    exact Matrix.fromBlocks_toBlocks _
  have hAeq : A = xiShiftedMomentHankelMatrix y n := by
    ext i j
    rfl
  have hAdet : A.det ≠ 0 := by
    rw [hAeq]
    exact hdet
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A
    (isUnit_iff_ne_zero.mpr hAdet)
  have hfactor : M.det = A.det * (D - C * A⁻¹ * B).det := by
    rw [← hblock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hMdet : M.det = (xiShiftedMomentHankelMatrix y (n + 1)).det := by
    dsimp only [M]
    rw [Matrix.det_reindex_self]
  have hscalar : (D - C * A⁻¹ * B).det = xiShiftedCanonicalAdmissionNorm y n := by
    rw [Matrix.det_fin_one]
    rw [xiShiftedCanonicalAdmissionNorm_eq_hankelQuadratic]
    let a : Fin n → ℝ := HTGeometry.monicMomentAdmissionCoefficients s n
    let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
    have hdet' : (HTGeometry.momentHankelMatrix s n).det ≠ 0 := by
      simpa only [A] using hAdet
    have hsolve : A *ᵥ a = -HTGeometry.momentHankelTail s n := by
      simpa only [A, a] using
          (HTGeometry.momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients hdet')
    have ha : a = -(A⁻¹ *ᵥ HTGeometry.momentHankelTail s n) := by
      rfl
    rw [xiShiftedMomentHankelQuadratic]
    have hfull : xiShiftedMomentHankelMatrix y (n + 1) =
        HTGeometry.momentHankelMatrix s (n + 1) := by
      ext i j
      rfl
    rw [hfull]
    have hBval (i : Fin n) : B i 0 = s ((i : ℕ) + n) := by rfl
    have hCval (i : Fin n) : C 0 i = s (n + (i : ℕ)) := by rfl
    have hDval : D 0 0 = s (n + n) := by rfl
    have hlower (i : Fin n) :
        (HTGeometry.momentHankelMatrix s (n + 1) *ᵥ c) i.castSucc = 0 := by
      have hi := congrFun hsolve i
      simp only [Matrix.mulVec, dotProduct, A, HTGeometry.momentHankelMatrix,
        HTGeometry.momentHankelTail, Pi.neg_apply] at hi
      change (∑ j : Fin (n + 1), s ((i : ℕ) + (j : ℕ)) * c j) = 0
      rw [Fin.sum_univ_castSucc]
      simp only [c, HTGeometry.monicMomentAdmissionVector,
        Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, mul_one]
      change (∑ x : Fin n, s ((i : ℕ) + (x : ℕ)) * a x) +
          s ((i : ℕ) + n) = 0
      dsimp only [a, s] at hi ⊢
      linarith
    have hquad : c ⬝ᵥ (HTGeometry.momentHankelMatrix s (n + 1) *ᵥ c) =
        s (n + n) + ∑ i : Fin n, a i * s (n + (i : ℕ)) := by
      rw [dotProduct, Fin.sum_univ_castSucc]
      simp only [hlower, mul_zero, Finset.sum_const_zero, zero_add]
      change c (Fin.last n) *
          (∑ j : Fin (n + 1), s (n + (j : ℕ)) * c j) = _
      simp only [c, HTGeometry.monicMomentAdmissionVector, Fin.snoc_last, one_mul]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, mul_one]
      rw [add_comm]
      apply congrArg (fun z : ℝ => s (n + n) + z)
      apply Finset.sum_congr rfl
      intro i _
      simp only [a]
      ring
    let b : Fin n → ℝ := fun i => B i 0
    have hb : b = HTGeometry.momentHankelTail s n := by
      funext i
      simp only [b, hBval, HTGeometry.momentHankelTail]
    have hinvb : A⁻¹ *ᵥ b = -a := by
      rw [hb, ha]
      simp
    have htriple : (C * A⁻¹ * B) 0 0 = (C *ᵥ (A⁻¹ *ᵥ b)) 0 := by
      calc
        (C * A⁻¹ * B) 0 0 = ((C * A⁻¹) *ᵥ b) 0 := by
          simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, b]
        _ = (C *ᵥ (A⁻¹ *ᵥ b)) 0 := by rw [Matrix.mulVec_mulVec]
    calc
      (D - C * A⁻¹ * B) 0 0 = D 0 0 - (C *ᵥ (A⁻¹ *ᵥ b)) 0 := by
        rw [Matrix.sub_apply, htriple]
      _ = s (n + n) - (C *ᵥ (-a)) 0 := by rw [hDval, hinvb]
      _ = s (n + n) + ∑ i : Fin n, a i * s (n + (i : ℕ)) := by
        simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, hCval]
        simp_rw [mul_neg]
        rw [Finset.sum_neg_distrib, sub_neg_eq_add]
        apply congrArg (fun z : ℝ => s (n + n) + z)
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = c ⬝ᵥ (HTGeometry.momentHankelMatrix s (n + 1) *ᵥ c) := hquad.symm
  rw [← hMdet, hfactor, hscalar, hAeq]

theorem tendsto_div_pow_right_of_hasFPowerSeriesAt_of_coeff_zero_before
    {f : ℝ → ℝ} {coeff : ℕ → ℝ} {d : ℕ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ coeff) 0)
    (hzero : ∀ j < d, coeff j = 0) :
    Tendsto (fun u : ℝ => f u / u ^ d) (𝓝[>] (0 : ℝ)) (𝓝 (coeff d)) := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ coeff
  have hpartial (u : ℝ) : p.partialSum (d + 1) u = coeff d * u ^ d := by
    rw [FormalMultilinearSeries.partialSum]
    simp_rw [p, FormalMultilinearSeries.ofScalars_apply_eq]
    rw [Finset.sum_eq_single d]
    · simp
    · intro j hj hjne
      have hjlt : j < d := by
        simp only [Finset.mem_range] at hj
        omega
      rw [hzero j hjlt, zero_smul]
    · simp
  have hO := hf.isBigO_sub_partialSum_pow (d + 1)
  have hsmall :
      (fun u : ℝ => f u - coeff d * u ^ d) =o[𝓝 0]
        (fun u : ℝ => ‖u‖ ^ d) := by
    have hpow : (fun u : ℝ => ‖u‖ ^ (d + 1)) =o[𝓝 0]
        (fun u : ℝ => ‖u‖ ^ d) :=
      isLittleO_norm_pow_norm_pow (Nat.lt_succ_self d)
    apply hO.trans_isLittleO hpow |>.congr'
    · filter_upwards with u
      rw [zero_add, hpartial]
    · exact Eventually.of_forall fun _ => rfl
  have hratio : Tendsto
      (fun u : ℝ => (f u - coeff d * u ^ d) / (‖u‖ ^ d))
      (𝓝 0) (𝓝 0) := hsmall.tendsto_div_nhds_zero
  have hratioRight := hratio.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hrewrite : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      f u / u ^ d = (f u - coeff d * u ^ d) / ‖u‖ ^ d + coeff d := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    rw [Real.norm_eq_abs, abs_of_pos hu]
    field_simp
    ring
  rw [tendsto_congr' hrewrite]
  simpa using hratioRight.add_const (coeff d)

theorem tendsto_xiShiftedCanonicalAdmissionNorm_div_pow_at_firstPadeContact
    {y : ℝ} (hy : 0 < y) {n d : ℕ}
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    Tendsto (fun u : ℝ => xiShiftedCanonicalAdmissionNorm (y + u) n / u ^ d)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
        xiShiftedHankelBoundaryPadeDefect y c (2 * n + d))) := by
  let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)
  let coeff : ℕ → ℝ := fun j => PowerSeries.coeff j A.det
  let f : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det
  have hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ coeff) 0 := by
    simpa only [f, coeff, A, xiShiftedHankelDetFPowerSeries] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (n + 1))
  have hcoeffZero : ∀ j < d, coeff j = 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      dsimp only [coeff, A]
      rw [GaloisForLFunctions.HTGeometry.coeff_zero_det_massShiftHankelPowerSeries]
      have hdet0 : (xiShiftedMomentHankelMatrix y (n + 1)).det = 0 := by
        apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hc
          (i := Fin.last n)
        exact mem_nonZeroDivisors_iff_ne_zero.mpr hlast
      rw [show HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) =
          xiShiftedMomentHankelMatrix y (n + 1) by
        ext i j
        rfl]
      exact hdet0
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hzeroj : ∀ k < 2 * n + j,
          xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
        intro k hk
        exact hzero k (by omega)
      dsimp only [coeff, A]
      rw [coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
        c hhead hc hlast hjpos hzeroj]
      rw [hzero (2 * n + j) (by omega)]
      ring
  have hdetLead :=
    tendsto_div_pow_right_of_hasFPowerSeriesAt_of_coeff_zero_before hf hcoeffZero
  have hcoeffFirst : coeff d =
      (xiShiftedMomentHankelMatrix y n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d)) := by
    dsimp only [coeff, A]
    exact coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
      c hhead hc hlast hd hzero
  rw [hcoeffFirst] at hdetLead
  have hheadContinuous : Tendsto
      (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) n).det)
      (𝓝[>] (0 : ℝ)) (𝓝 ((xiShiftedMomentHankelMatrix y n).det)) := by
    have h := (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy n).continuousAt
    have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := inf_le_left
    simpa only [add_zero] using h.tendsto.mono_left hmono
  have hratio := hdetLead.div hheadContinuous hhead.det_pos.ne'
  have hconst :
      (xiShiftedMomentHankelMatrix y n).det *
          ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
            xiShiftedHankelBoundaryPadeDefect y c (2 * n + d)) /
          (xiShiftedMomentHankelMatrix y n).det =
        (-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) := by
    field_simp [hhead.det_pos.ne']
  rw [hconst] at hratio
  have hheadEv := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hhead
  refine hratio.congr' ?_
  filter_upwards [hheadEv.filter_mono inf_le_left] with u hu
  have hdetEq :=
    det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
      (y := y + u) hu.det_pos.ne'
  change (((xiShiftedMomentHankelMatrix (y + u) (n + 1)).det / u ^ d) /
      (xiShiftedMomentHankelMatrix (y + u) n).det) =
    xiShiftedCanonicalAdmissionNorm (y + u) n / u ^ d
  rw [hdetEq]
  field_simp [hu.det_pos.ne']

/-- Exact arbitrary-order newborn-norm residue at an occupied strict frontier.  Once `d` is the
first live canonical Padé contact, the moving admission norm has precisely the universal
negative-binomial leading coefficient; no moving-admission correction survives the Schur ratio. -/
theorem tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0) :
    Tendsto
      (fun u : ℝ => xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2) / u ^ d)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
        xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let c := xiShiftedStrictFrontierNullVector n
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y m).PosDef := by
    simpa only [y, m] using hface.1
  have hflat : xiShiftedMomentHankelMatrix y (m + 1) *ᵥ c = 0 := by
    have h := xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
    simpa only [y, m, c, xiShiftedStrictFrontierNullVector, Nat.add_assoc] using h
  have hlast : c (Fin.last m) ≠ 0 := by
    simp [c, xiShiftedStrictFrontierNullVector, m]
  have hlimit := tendsto_xiShiftedCanonicalAdmissionNorm_div_pow_at_firstPadeContact
    hy c hhead hflat hlast hd (by
      intro k hk
      simpa only [m, c, xiShiftedStrictFrontierPadeDefect, y,
        xiShiftedStrictFrontierNullVector] using hzero k hk)
  simpa only [y, m, c, xiShiftedStrictFrontierPadeDefect,
    xiShiftedStrictFrontierNullVector] using hlimit

/-! The Schur ratio and analytic contact germ above turn every first live adaptive source into an
exact all-order newborn-norm price. -/

/-- False-RH alternative in exact all-contact source coordinates. -/
def XiShiftedCofinalFiniteArithmeticContactPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      XiShiftedStrictFrontierFiniteArithmeticContactLaw n

/-- False RH supplies cofinally many finite first contacts, each capitalized by its exact adaptive
completed arithmetic source. -/
theorem xiShiftedCofinalFiniteArithmeticContactPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalFiniteArithmeticContactPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot
      (max A (1 / 4))
  have hA' : A < xiShiftedHigherBlockTerminalFrontier n :=
    lt_of_le_of_lt (le_max_left _ _) hA
  have hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hA) hstrict
  exact ⟨n, hne, hA', hstrict, hphysical,
    xiShiftedStrictFrontier_finiteArithmeticContactLaw hne hstrict hphysical⟩

/-- RH excludes the cofinal finite-contact source phase because every failure set is empty. -/
theorem not_xiShiftedCofinalFiniteArithmeticContactPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalFiniteArithmeticContactPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- Premise-free exact phase equivalence.  This is a closed alternative, not an RH proof: closing
RH now means excluding cofinal escape of these finite adaptive arithmetic contacts. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalFiniteArithmeticContactPhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalFiniteArithmeticContactPhase := by
  constructor
  · exact not_xiShiftedCofinalFiniteArithmeticContactPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalFiniteArithmeticContactPhase_of_not_riemannHypothesis hnotRH)

/-- Premise-free RH-or-cofinal-source-contact dichotomy. -/
theorem riemannHypothesis_or_xiShiftedCofinalFiniteArithmeticContactPhase :
    RiemannHypothesis ∨ XiShiftedCofinalFiniteArithmeticContactPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (xiShiftedCofinalFiniteArithmeticContactPhase_of_not_riemannHypothesis hRH)

end

end RHTower
