import GaloisForLFunctions.RHTower.Deninger.DeningerHasseHilbertOperators
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # The full Hasse shift on the native source Hilbert space

The nilpotent part of every original source block extends to one contraction,
without a bound on Xi multiplicities. Its coefficient is fixed by the source
generator, rather than chosen by a spectral model.
-/

noncomputable section
open Complex

namespace RHTower

private def hassePrevious : Equiv.Perm DeningerArithmeticJetCoordinate :=
  Equiv.sigmaCongrRight fun rho => (finRotate (xiSupportMultiplicity rho)).symm

private theorem hassePrevious_succ (rho : XiDivisorSupport) (j : ℕ)
    (hj : j + 1 < xiSupportMultiplicity rho) :
    hassePrevious ⟨rho, ⟨j + 1, hj⟩⟩ =
      ⟨rho, ⟨j, by omega⟩⟩ := by
  let i : Fin (xiSupportMultiplicity rho) := ⟨j + 1, hj⟩
  letI := i.neZero
  have hi : i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [i] at this
  change (⟨rho, (finRotate _).symm i⟩ : DeningerArithmeticJetCoordinate) = _
  apply congrArg (fun k : Fin (xiSupportMultiplicity rho) =>
    (⟨rho, k⟩ : DeningerArithmeticJetCoordinate))
  apply Fin.ext
  exact (coe_finRotate_symm_of_ne_zero hi).trans (by simp [i])

def deningerHasseHilbertShiftLM :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun x := ⟨fun q => if q.2.val = 0 then 0 else x (hassePrevious q), by
    apply (lp.memℓp (deningerHasseHilbertReindex hassePrevious x)).mono'
    intro q
    split_ifs
    · change ‖(0 : ℂ)‖ ≤ ‖x (hassePrevious q)‖
      simpa only [norm_zero] using norm_nonneg (x (hassePrevious q))
    · exact le_rfl⟩
  map_add' x y := by
    apply lp.ext
    funext q
    change (if q.2.val = 0 then 0 else x (hassePrevious q) + y (hassePrevious q)) = _
    split_ifs <;> simp_all
  map_smul' c x := by
    apply lp.ext
    funext q
    change (if q.2.val = 0 then 0 else c * x (hassePrevious q)) = _
    split_ifs <;> simp_all

theorem deningerHasseHilbertShiftLM_norm_le (x : DeningerArithmeticJetHilbert) :
    ‖deningerHasseHilbertShiftLM x‖ ≤ ‖x‖ := by
  rw [← deningerHasseHilbertReindex_norm hassePrevious x]
  apply lp.norm_mono (by norm_num)
  intro q
  change ‖if q.2.val = 0 then 0 else x (hassePrevious q)‖ ≤ ‖x (hassePrevious q)‖
  split_ifs
  · simpa only [norm_zero] using norm_nonneg (x (hassePrevious q))
  · exact le_rfl

/-- All Jordan shifts at once, with the original factorial normalization. -/
def deningerHasseHilbertShift :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  deningerHasseHilbertShiftLM.mkContinuous 1 (by
    intro x
    simpa using deningerHasseHilbertShiftLM_norm_le x)

theorem norm_deningerHasseHilbertShift_le : ‖deningerHasseHilbertShift‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (by
    intro x
    simpa [deningerHasseHilbertShift] using deningerHasseHilbertShiftLM_norm_le x)

@[simp] theorem deningerHasseHilbertShift_zero (x : DeningerArithmeticJetHilbert)
    (rho : XiDivisorSupport) (h : 0 < xiSupportMultiplicity rho) :
    deningerHasseHilbertShift x ⟨rho, ⟨0, h⟩⟩ = 0 := by
  change (if (0 : ℕ) = 0 then 0 else x (hassePrevious ⟨rho, ⟨0, h⟩⟩)) = 0
  simp

@[simp] theorem deningerHasseHilbertShift_succ (x : DeningerArithmeticJetHilbert)
    (rho : XiDivisorSupport) (j : ℕ) (hj : j + 1 < xiSupportMultiplicity rho) :
    deningerHasseHilbertShift x ⟨rho, ⟨j + 1, hj⟩⟩ =
      x ⟨rho, ⟨j, by omega⟩⟩ := by
  change (if j + 1 = 0 then 0 else x (hassePrevious _)) = _
  rw [if_neg (by omega), hassePrevious_succ]

/-- The centered original generator, in the XiC spectral coordinate. -/
def deningerMeyerCenteredGenerator : Module.End ℂ DeningerMeyerStrongLogCohomology :=
  (-I) • deningerMeyerCohomologyShift (1 / 2)

/-- Exact full-Jordan source identity, including every repeated-zero slot. -/
theorem deningerMeyerHasseHilbert_centeredGenerator
    (u : DeningerMeyerStrongLogCohomology) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u) q =
      xiSpectralPoint q * deningerMeyerHasseHilbertLM u q -
        I * deningerHasseHilbertShift (deningerMeyerHasseHilbertLM u) q := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    rcases q with ⟨rho, j, hj⟩
    simp only [deningerMeyerCenteredGenerator, LinearMap.smul_apply,
      deningerMeyerCohomologyShift_apply, map_smul, map_sub,
      deningerMeyerCohomologyGenerator_mk]
    change -I * (deningerMeyerHasseMoment (deningerMeyerStrongLogGenerator g) j rho -
      (1 / 2) * deningerMeyerHasseMoment g j rho) = _
    cases j with
    | zero =>
      rw [deningerMeyerHasseMoment_generator_zero, deningerHasseHilbertShift_zero]
      change _ = ((rho : ℂ) - 1 / 2) * -I * deningerMeyerHasseMoment g 0 rho - I * 0
      ring
    | succ j =>
      rw [deningerMeyerHasseMoment_generator_succ, deningerHasseHilbertShift_succ]
      change _ = ((rho : ℂ) - 1 / 2) * -I * deningerMeyerHasseMoment g (j + 1) rho -
        I * deningerMeyerHasseMoment g j rho
      ring

end RHTower
