import GaloisForLFunctions.RHTower.Deninger.DeningerHasseHilbertOperators
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Convergent complementary Hasse pairing on the full jet Hilbert space -/

noncomputable section
open Complex Set
open scoped Classical

namespace RHTower

def deningerHasseHalfTerm (x y : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) : ℂ :=
  if 0 < (q.1 : ℂ).im then x q * y (deningerHasseJetReverse q) else 0

private theorem hasseHolder : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
  rw [Real.holderConjugate_iff]
  norm_num

private theorem hasseHalfTerm_bound (x y : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    ‖deningerHasseHalfTerm x y q‖ ≤
      ‖x q‖ * ‖deningerHasseHilbertReindex deningerHasseJetReverse y q‖ := by
  unfold deningerHasseHalfTerm
  split_ifs
  · simp
  · simp only [norm_zero]
    positivity

theorem deningerHasseHalfTerm_summable (x y : DeningerArithmeticJetHilbert) :
    Summable (deningerHasseHalfTerm x y) :=
  .of_norm_bounded (lp.summable_mul hasseHolder x
    (deningerHasseHilbertReindex deningerHasseJetReverse y)) (hasseHalfTerm_bound x y)

/-- Absolute convergence includes all multiplicity slots, without spectral damping. -/
theorem deningerHasseHalfTerm_norm_summable (x y : DeningerArithmeticJetHilbert) :
    Summable (fun q => ‖deningerHasseHalfTerm x y q‖) := by
  apply Summable.of_norm_bounded (lp.summable_mul hasseHolder x
    (deningerHasseHilbertReindex deningerHasseJetReverse y))
  intro q
  simpa only [norm_norm] using hasseHalfTerm_bound x y q

def deningerHasseHalfPairing (x y : DeningerArithmeticJetHilbert) : ℂ :=
  ∑' q, deningerHasseHalfTerm x y q

theorem deningerHasseHalfPairing_bound (x y : DeningerArithmeticJetHilbert) :
    ‖deningerHasseHalfPairing x y‖ ≤ ‖x‖ * ‖y‖ := by
  have h := tsum_of_norm_bounded
    (lp.summable_mul hasseHolder x
      (deningerHasseHilbertReindex deningerHasseJetReverse y)).hasSum
    (hasseHalfTerm_bound x y)
  have hh := lp.tsum_mul_le_mul_norm' hasseHolder x
    (deningerHasseHilbertReindex deningerHasseJetReverse y)
  simpa only [deningerHasseHalfPairing, deningerHasseHilbertReindex_norm] using h.trans hh

def deningerHasseHalfPairingLM :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ deningerHasseHalfPairing
    (by
      intro x y z
      unfold deningerHasseHalfPairing
      rw [← (deningerHasseHalfTerm_summable x z).tsum_add
        (deningerHasseHalfTerm_summable y z)]
      apply tsum_congr
      intro q
      simp only [deningerHasseHalfTerm, lp.coeFn_add, Pi.add_apply]
      split_ifs <;> ring)
    (by
      intro c x y
      unfold deningerHasseHalfPairing
      rw [smul_eq_mul, ← tsum_mul_left]
      apply tsum_congr
      intro q
      simp only [deningerHasseHalfTerm, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring)
    (by
      intro x y z
      unfold deningerHasseHalfPairing
      rw [← (deningerHasseHalfTerm_summable x y).tsum_add
        (deningerHasseHalfTerm_summable x z)]
      apply tsum_congr
      intro q
      simp only [deningerHasseHalfTerm, lp.coeFn_add, Pi.add_apply]
      split_ifs <;> ring)
    (by
      intro c x y
      unfold deningerHasseHalfPairing
      rw [smul_eq_mul, ← tsum_mul_left]
      apply tsum_congr
      intro q
      simp only [deningerHasseHalfTerm, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring)

def deningerHasseHalfPairingCLM :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert →L[ℂ] ℂ :=
  deningerHasseHalfPairingLM.mkContinuous₂ 1 (fun x y => by
    change ‖deningerHasseHalfPairing x y‖ ≤ 1 * ‖x‖ * ‖y‖
    simpa using deningerHasseHalfPairing_bound x y)

@[simp] theorem deningerHasseHalfPairingCLM_apply (x y : DeningerArithmeticJetHilbert) :
    deningerHasseHalfPairingCLM x y = deningerHasseHalfPairing x y := rfl

theorem deningerHasseHalfPairing_symm (x y : DeningerArithmeticJetHilbert) :
    deningerHasseHalfPairing x y = deningerHasseHalfPairing y x := by
  unfold deningerHasseHalfPairing
  rw [← deningerHasseJetReverse.tsum_eq (deningerHasseHalfTerm x y)]
  apply tsum_congr
  intro q
  simp only [deningerHasseHalfTerm, deningerHasseJetReverse_apply, Fin.rev_rev]
  split_ifs <;> ring

theorem deningerHasseHalfPairing_single_left (q : DeningerArithmeticJetCoordinate)
    (c : ℂ) (y : DeningerArithmeticJetHilbert) :
    deningerHasseHalfPairing (lp.single 2 q c) y =
      if 0 < (q.1 : ℂ).im then c * y (deningerHasseJetReverse q) else 0 := by
  unfold deningerHasseHalfPairing
  rw [tsum_eq_single q]
  · simp [deningerHasseHalfTerm]
  · intro r hr
    unfold deningerHasseHalfTerm
    rw [lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q c hr]
    simp

theorem deningerHasseHalfPairing_single_right (q : DeningerArithmeticJetCoordinate)
    (c : ℂ) (x : DeningerArithmeticJetHilbert) :
    deningerHasseHalfPairing x (lp.single 2 q c) =
      if 0 < (q.1 : ℂ).im then c * x (deningerHasseJetReverse q) else 0 := by
  rw [deningerHasseHalfPairing_symm, deningerHasseHalfPairing_single_left]

end RHTower
