import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionPaugam
import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionTraceClass

/-! # A bounded insertion recovers the full Paugam pairing from source traces

Ordinary convolution trace annihilates the alternating original-source product.
One fixed contraction, sending each upper block's top Hasse slot to its bottom
slot, recovers the complete nondegenerate Paugam pairing. Trace-class admission
holds for every original source, with no damping or multiplicity bound.

The product below is literal alternating source convolution. Its identification
with a geometric cup, source preservation by the insertion, and positivity are
not consequences of this trace identity.
-/

noncomputable section
open Complex Set ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped Classical InnerProductSpace

namespace RHTower

/-- Upper-block top-to-bottom insertion in the full Hasse carrier. -/
def deningerHasseTopInsertionLM :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun x := ⟨fun q => if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then
      x (deningerHasseJetReverse q) else 0, by
    apply (lp.memℓp (deningerHasseHilbertReindex deningerHasseJetReverse x)).mono'
    intro q
    change ‖if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then
      x (deningerHasseJetReverse q) else 0‖ ≤ ‖x (deningerHasseJetReverse q)‖
    split_ifs
    · exact le_rfl
    · simp⟩
  map_add' x y := by
    apply lp.ext
    funext q
    change (if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then
      x (deningerHasseJetReverse q) + y (deningerHasseJetReverse q) else 0) =
      (if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then x (deningerHasseJetReverse q) else 0) +
      (if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then y (deningerHasseJetReverse q) else 0)
    split_ifs <;> simp
  map_smul' c x := by
    apply lp.ext
    funext q
    change (if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then
      c * x (deningerHasseJetReverse q) else 0) =
      c * (if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then x (deningerHasseJetReverse q) else 0)
    split_ifs <;> simp

private theorem topInsertion_norm_le (x : DeningerArithmeticJetHilbert) :
    ‖deningerHasseTopInsertionLM x‖ ≤ ‖x‖ := by
  rw [← deningerHasseHilbertReindex_norm deningerHasseJetReverse x]
  apply lp.norm_mono (by norm_num)
  intro q
  change ‖if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then
    x (deningerHasseJetReverse q) else 0‖ ≤ _
  split_ifs
  · exact le_rfl
  · simp

/-- One bounded insertion handles all multiplicities simultaneously. -/
def deningerHasseTopInsertion :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  deningerHasseTopInsertionLM.mkContinuous 1 (fun x => by
    simpa using topInsertion_norm_le x)

@[simp] theorem deningerHasseTopInsertion_apply (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerHasseTopInsertion x q =
      if 0 < (q.1 : ℂ).im ∧ q.2.val = 0 then x (deningerHasseJetReverse q) else 0 := rfl

theorem norm_deningerHasseTopInsertion_le : ‖deningerHasseTopInsertion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖deningerHasseTopInsertionLM x‖ ≤ 1 * ‖x‖
  simpa using topInsertion_norm_le x

private theorem topInsertion_diagonal (g : DeningerMeyerStrongLogTarget)
    (q : DeningerArithmeticJetCoordinate) :
    ⟪xiDivisorHilbertBasis q,
      deningerMeyerHilbertConvolution g (deningerHasseTopInsertion (xiDivisorHilbertBasis q))⟫_ℂ =
      if 0 < (q.1 : ℂ).im ∧ q.2.val = xiSupportMultiplicity q.1 - 1 then
        deningerMeyerHasseMoment g (xiSupportMultiplicity q.1 - 1) (q.1 : ℂ) else 0 := by
  rw [xiDivisorHilbertBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [deningerMeyerHilbertConvolution_jets, Finset.sum_eq_single q.2.val]
  · rw [deningerHasseTopInsertion_apply]
    have hb : (deningerHasseLower q q.2.val).2.val = 0 := Nat.sub_self _
    change deningerMeyerHasseMoment g q.2.val (q.1 : ℂ) *
      (if 0 < (q.1 : ℂ).im ∧ (deningerHasseLower q q.2.val).2.val = 0 then
        (lp.single 2 q 1 : DeningerArithmeticJetHilbert)
          (deningerHasseJetReverse (deningerHasseLower q q.2.val)) else 0) = _
    rw [hb]
    by_cases hp : 0 < (q.1 : ℂ).im
    · simp only [hp, true_and, and_self, ↓reduceIte]
      by_cases hj : q.2.val = xiSupportMultiplicity q.1 - 1
      · have he : deningerHasseJetReverse (deningerHasseLower q q.2.val) = q := by
          refine Sigma.ext ?_ ?_
          · rfl
          apply heq_of_eq
          apply Fin.ext
          simp only [deningerHasseJetReverse_apply, Fin.val_rev, hb]
          change xiSupportMultiplicity q.1 - 1 = q.2.val
          exact hj.symm
        rw [he, lp.single_apply_self, mul_one, if_pos hj, hj]
      · have he : deningerHasseJetReverse (deningerHasseLower q q.2.val) ≠ q := by
          intro he
          have hv := congrArg (fun r : DeningerArithmeticJetCoordinate => r.2.val) he
          simp only [deningerHasseJetReverse_apply, Fin.val_rev, hb] at hv
          exact hj hv.symm
        rw [lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q 1 he,
          mul_zero, if_neg hj]
    · simp [hp]
  · intro k hk hkj
    have hkn : k ≤ q.2.val := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hne : (deningerHasseLower q k).2.val ≠ 0 := by
      change q.2.val-k ≠ 0
      omega
    simp [deningerHasseTopInsertion_apply, hne]
  · simp

/-- The ordinary trace with this insertion reads the highest Hasse coefficient
of every upper block, including all multiple zeros. -/
theorem deningerMeyerHilbertConvolution_topInsertion_trace
    (g : DeningerMeyerStrongLogTarget) :
    opTrace ((deningerMeyerHilbertConvolution g).comp deningerHasseTopInsertion) =
      ∑' rho : XiDivisorSupport, if 0 < (rho : ℂ).im then
        deningerMeyerHasseMoment g (xiSupportMultiplicity rho - 1) (rho : ℂ) else 0 := by
  have ht := hsTraceIdeal_comp_right (deningerMeyerHilbertConvolution_mem_hsTraceIdeal g)
    deningerHasseTopInsertion
  let f := fun q : DeningerArithmeticJetCoordinate =>
    if 0 < (q.1 : ℂ).im ∧ q.2.val = xiSupportMultiplicity q.1 - 1 then
      deningerMeyerHasseMoment g (xiSupportMultiplicity q.1 - 1) (q.1 : ℂ) else 0
  have hf : Summable f :=
    (summable_diag_basis_of_mem ht xiDivisorHilbertBasis).congr
      (fun q => topInsertion_diagonal g q)
  rw [opTrace_eq_tsum_basis_of_mem ht xiDivisorHilbertBasis]
  calc
    _ = ∑' q, f q := tsum_congr (fun q => topInsertion_diagonal g q)
    _ = ∑' rho, ∑' j : DeningerArithmeticJetIndex rho, f ⟨rho,j⟩ := hf.tsum_sigma
    _ = _ := by
      apply tsum_congr
      intro rho
      let top : DeningerArithmeticJetIndex rho :=
        ⟨xiSupportMultiplicity rho - 1, by have := xiSupportMultiplicity_pos rho; omega⟩
      rw [tsum_eq_single top]
      · simp [f, top]
      · intro j hj
        have hn : j.val ≠ xiSupportMultiplicity rho - 1 := by
          intro h
          exact hj (Fin.ext h)
        simp [f, hn]

/-- Literal alternating source convolution; no geometric cup identification is assumed. -/
def deningerMeyerSourceCup (g h : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerSourceConvolution g (deningerMeyerStrongLogJ h) -
    deningerMeyerSourceConvolution h (deningerMeyerStrongLogJ g)

/-- The source product represents the existing product on genuine Poisson cohomology. -/
theorem deningerMeyerSourceCup_class (g h : DeningerMeyerStrongLogTarget) :
    (Submodule.Quotient.mk (deningerMeyerSourceCup g h) : DeningerMeyerStrongLogCohomology) =
      deningerMeyerConvolutionSkewProduct (Submodule.Quotient.mk g) (Submodule.Quotient.mk h) := by
  simp only [deningerMeyerSourceCup, Submodule.Quotient.mk_sub,
    deningerMeyerConvolutionSkewProduct, deningerMeyerStrongLogCohomologyJ_mk,
    deningerMeyerCohomologyConvolution_mk]

theorem deningerMeyerSourceCup_mellin (g h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceCup g h) s =
      deningerMeyerPaugamMellinProduct g h s := by
  change deningerMeyerStrongLogMellinLM s (_-_) = _
  rw [map_sub]
  change deningerMeyerStrongLogMellin
      (deningerMeyerSourceConvolution g (deningerMeyerStrongLogJ h)) s -
    deningerMeyerStrongLogMellin
      (deningerMeyerSourceConvolution h (deningerMeyerStrongLogJ g)) s = _
  simp only [deningerMeyerSourceConvolution_mellin, deningerMeyerPaugamMellinProduct]

private theorem sourceCup_top (g h : DeningerMeyerStrongLogTarget) (rho : XiDivisorSupport) :
    deningerMeyerHasseMoment (deningerMeyerSourceCup g h)
        (xiSupportMultiplicity rho - 1) (rho : ℂ) =
      deningerMeyerHassePaugamBlock rho (Submodule.Quotient.mk g) (Submodule.Quotient.mk h) := by
  rw [deningerMeyerHassePaugamBlock_eq, deningerMeyerPaugamGeneralizedJetPairing_mk]
  simp only [deningerMeyerHasseMoment, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    deningerMeyerXiFullJetDatum]
  congr 2
  funext s
  exact deningerMeyerSourceCup_mellin g h s

/-- Exact whole-source trace realization of the full nondegenerate Paugam form. -/
theorem deningerMeyerSourceCup_inserted_trace (g h : DeningerMeyerStrongLogTarget) :
    opTrace ((deningerMeyerHilbertConvolution (deningerMeyerSourceCup g h)).comp
      deningerHasseTopInsertion) =
      deningerMeyerGlobalHassePaugamPairing (Submodule.Quotient.mk g) (Submodule.Quotient.mk h) := by
  rw [deningerMeyerHilbertConvolution_topInsertion_trace,
    deningerMeyerGlobalHassePaugamPairing_blocks]
  simp only [sourceCup_top]

/-- The unmodified scalar trace loses every alternating source product. -/
theorem deningerMeyerSourceCup_ordinary_trace (g h : DeningerMeyerStrongLogTarget) :
    opTrace (deningerMeyerHilbertConvolution (deningerMeyerSourceCup g h)) = 0 := by
  rw [deningerMeyerHilbertConvolution_opTrace]
  let f : XiZeroCopy → ℂ := fun q =>
    deningerMeyerStrongLogMellin (deningerMeyerSourceCup g h) (q.1 : ℂ)
  have he (q : XiZeroCopy) : f (xiZeroCopyReflectEquiv q) = -f q := by
    simp only [f, deningerMeyerSourceCup_mellin, deningerMeyerPaugamMellinProduct,
      deningerMeyerStrongLogMellin_J]
    change deningerMeyerStrongLogMellin g (1-(q.1:ℂ)) *
        deningerMeyerStrongLogMellin h (1-(1-(q.1:ℂ))) -
      deningerMeyerStrongLogMellin h (1-(q.1:ℂ)) *
        deningerMeyerStrongLogMellin g (1-(1-(q.1:ℂ))) = _
    simp only [sub_sub_cancel]
    ring
  have hs := xiZeroCopyReflectEquiv.tsum_eq f
  simp only [he, tsum_neg] at hs
  change (∑' q, f q) = 0
  linear_combination -hs / 2

/-- Inserted traces detect the complete original class, including its higher jets. -/
theorem deningerMeyerSourceCup_trace_detects (g : DeningerMeyerStrongLogTarget) :
    (∀ h : DeningerMeyerStrongLogTarget,
      opTrace ((deningerMeyerHilbertConvolution (deningerMeyerSourceCup g h)).comp
        deningerHasseTopInsertion) = 0) ↔
      (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 := by
  simp only [deningerMeyerSourceCup_inserted_trace]
  constructor
  · intro h
    have hk : (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) ∈
        LinearMap.ker deningerMeyerGlobalHassePaugamPairing := by
      apply LinearMap.ext
      intro v
      obtain ⟨h', rfl⟩ :=
        (Submodule.Quotient.mk_surjective (LinearMap.range deningerMeyerStrongLogSumLM)) v
      exact h h'
    rwa [deningerMeyerGlobalHassePaugamPairing_ker, Submodule.mem_bot] at hk
  · intro hg h
    simp [hg]

end RHTower
