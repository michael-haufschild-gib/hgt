import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Partial transpose of a charge-difference kernel

The bit-flip argument in Qian and Zhang (arXiv:2611.24473, Theorem 4(a))
works for any additive charge on a finite qubit register. Every partial
transpose is a permutation similarity. The normalized Cauchy coherence
matrix for additive logarithmic rates gives an unconditional positive example.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

private def swapBits (S : Finset σ) (x y : σ → Bool) : σ → Bool :=
  fun i => if i ∈ S then y i else x i

private def flipBits (S : Finset σ) (x : σ → Bool) : σ → Bool :=
  fun i => if i ∈ S then !(x i) else x i

private def flipEquiv (S : Finset σ) : (σ → Bool) ≃ (σ → Bool) where
  toFun := flipBits S
  invFun := flipBits S
  left_inv x := by funext i; by_cases h : i ∈ S <;> simp [flipBits, h]
  right_inv x := by funext i; by_cases h : i ∈ S <;> simp [flipBits, h]

/-- Partial transpose on the indicated qubits exchanges row and column bits. -/
def partialTransposeOn (S : Finset σ) (M : Matrix (σ → Bool) (σ → Bool) ℂ) :
    Matrix (σ → Bool) (σ → Bool) ℂ :=
  fun x y => M (swapBits S x y) (swapBits S y x)

/-- A weighted sum of occupied sites, also allowing vector-valued charges. -/
def bitCharge {A : Type*} [AddCommGroup A] (w : σ → A) (x : σ → Bool) : A :=
  ∑ i, if x i then w i else 0

/-- The charge-difference kernel on the qubit basis. -/
def chargeDifferenceMatrix {A : Type*} [AddCommGroup A] (w : σ → A) (f : A → ℂ) :
    Matrix (σ → Bool) (σ → Bool) ℂ :=
  fun x y => f (bitCharge w x - bitCharge w y)

private theorem chargeDifference_swap_eq_flip {A : Type*} [AddCommGroup A]
    (S : Finset σ) (w : σ → A) (x y : σ → Bool) :
    bitCharge w (swapBits S x y) - bitCharge w (swapBits S y x) =
      bitCharge w (flipBits S x) - bitCharge w (flipBits S y) := by
  simp only [bitCharge, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · cases hx : x i <;> cases hy : y i <;> simp [swapBits, flipBits, hi, hx, hy]
  · simp only [swapBits, flipBits, if_neg hi]

/-- Partial transpose on a charge-difference matrix equals simultaneous bit flips. -/
theorem partialTransposeOn_chargeDifference {A : Type*} [AddCommGroup A]
    (S : Finset σ) (w : σ → A) (f : A → ℂ) :
    partialTransposeOn S (chargeDifferenceMatrix w f) =
      (chargeDifferenceMatrix w f).submatrix (flipBits S) (flipBits S) := by
  ext x y
  exact congrArg f (chargeDifference_swap_eq_flip S w x y)

/-- A partial transpose preserves the entire characteristic polynomial. -/
theorem charpoly_partialTransposeOn_chargeDifference {A : Type*} [AddCommGroup A]
    (S : Finset σ) (w : σ → A) (f : A → ℂ) :
    (partialTransposeOn S (chargeDifferenceMatrix w f)).charpoly =
      (chargeDifferenceMatrix w f).charpoly := by
  rw [partialTransposeOn_chargeDifference]
  exact Matrix.charpoly_reindex (flipEquiv S).symm _

/-- Positivity of this kernel is equivalent to positivity of any partial transpose. -/
theorem partialTransposeOn_chargeDifference_posSemidef_iff {A : Type*} [AddCommGroup A]
    (S : Finset σ) (w : σ → A) (f : A → ℂ) :
    (partialTransposeOn S (chargeDifferenceMatrix w f)).PosSemidef ↔
      (chargeDifferenceMatrix w f).PosSemidef := by
  rw [partialTransposeOn_chargeDifference]
  constructor
  · intro h
    have hh := h.submatrix (flipEquiv S).symm
    have he : ((chargeDifferenceMatrix w f).submatrix (flipBits S) (flipBits S)).submatrix
        (flipEquiv S).symm (flipEquiv S).symm = chargeDifferenceMatrix w f := by
      ext x y
      simp only [Matrix.submatrix_apply,
        show ∀ z, flipBits S ((flipEquiv S).symm z) = z from (flipEquiv S).apply_symm_apply]
    rwa [he] at hh
  · exact fun h => h.submatrix _

/-- Inverse dimension times the corpus's Cauchy coherence on an additive rate register. -/
def cauchyChargeState (w : σ → ℝ) : Matrix (σ → Bool) (σ → Bool) ℂ :=
  chargeDifferenceMatrix w (fun d =>
    ((Fintype.card (σ → Bool) : ℝ)⁻¹ * (Real.cosh (d / 2))⁻¹ : ℝ))

theorem cauchyChargeState_trace (w : σ → ℝ) : (cauchyChargeState w).trace = 1 := by
  have hn : (Fintype.card (σ → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (σ → Bool) ≠ 0)
  simp only [Matrix.trace, Matrix.diag_apply, cauchyChargeState, chargeDifferenceMatrix,
    sub_self, zero_div, Real.cosh_zero, inv_one, mul_one, Finset.sum_const, Finset.card_univ]
  exact_mod_cast (show Fintype.card (σ → Bool) • (Fintype.card (σ → Bool) : ℝ)⁻¹ = 1 by
    rw [nsmul_eq_mul, mul_inv_cancel₀ hn])

/-- The normalized Cauchy matrix is a density matrix with positive partial
transpose across every split of the register. -/
theorem cauchyChargeState_ppt (w : σ → ℝ) (S : Finset σ) :
    (partialTransposeOn S (cauchyChargeState w)).PosSemidef := by
  unfold cauchyChargeState
  rw [partialTransposeOn_chargeDifference_posSemidef_iff]
  let e := Fintype.equivFin (σ → Bool)
  let r := bitCharge w ∘ e.symm
  have hp := (CauchyDephasing.symbol_posSemidef r).submatrix e
  have he : chargeDifferenceMatrix w
      (fun d => ((Fintype.card (σ → Bool) : ℝ)⁻¹ * (Real.cosh (d / 2))⁻¹ : ℝ)) =
      ((Fintype.card (σ → Bool) : ℝ)⁻¹ : ℂ) • (CauchyDephasing.symbol r).submatrix e e := by
    ext x y
    simp only [chargeDifferenceMatrix, Matrix.smul_apply, smul_eq_mul,
      Matrix.submatrix_apply, CauchyDephasing.symbol, r, Function.comp_apply,
      Equiv.symm_apply_apply, CauchyDephasing.coherence_eq_cosh_inv, Complex.ofReal_mul]
  rw [he]
  have hc : 0 ≤ (Fintype.card (σ → Bool) : ℝ)⁻¹ := by positivity
  exact hp.smul (by exact_mod_cast hc)

#print axioms partialTransposeOn_chargeDifference
#print axioms charpoly_partialTransposeOn_chargeDifference
#print axioms partialTransposeOn_chargeDifference_posSemidef_iff
#print axioms cauchyChargeState_trace
#print axioms cauchyChargeState_ppt

end

end GaloisForLFunctions.HilbertMetric
