import GaloisForLFunctions.BiScaleUncertainty.SieveTripleFourier
import Mathlib.Algebra.BigOperators.Fin

/-!
# Full translated-moment Fourier readouts

A Fourier transform in all translation variables isolates exactly zero-sum
frequency products. For actual divisor-sieve residue signals these are products
of Selberg multiples coordinates with the explicit factorial normalization.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
variable {P : ℕ} [NeZero P]

private theorem dft_translate (f : ZMod P → ℂ) (t r : ZMod P) :
    ZMod.dft (fun h => f (t+h)) r = ZMod.stdAddChar (t*r) * ZMod.dft f r := by
  rw [ZMod.dft_apply,ZMod.dft_apply,Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft t) _ _ ?_
  intro h
  change ZMod.stdAddChar (-(h*r)) * f (t+h) =
    ZMod.stdAddChar (t*r) * (ZMod.stdAddChar (-((t+h)*r)) * f (t+h))
  rw [← mul_assoc,← AddChar.map_add_eq_mul]
  congr 2
  ring

private theorem prod_char {ι : Type*} (s : Finset ι) (r : ι → ZMod P) :
    (∏ i ∈ s, ZMod.stdAddChar (r i)) = ZMod.stdAddChar (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,ih,AddChar.map_add_eq_mul]

private theorem sum_char (t : ZMod P) :
    (∑ n : ZMod P, ZMod.stdAddChar (n*t)) = if t = 0 then (P : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht,ZMod.card]
  · rw [if_neg ht]
    simpa only [AddChar.mulShift_apply,mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar P ht))

/-- Unnormalized Fourier transform in every translation variable of a finite observation. -/
def momentDFT {m : ℕ} (T : (Fin m → ZMod P) → ℂ) (r : Fin m → ZMod P) : ℂ :=
  ∑ h : Fin m → ZMod P, (∏ i, ZMod.stdAddChar (-(h i*r i))) * T h

/-- Every Fourier coefficient of a translated product is an exact zero-sum frequency product. -/
theorem momentDFT_translationMoment (f : ZMod P → ℂ) {m : ℕ} (r : Fin m → ZMod P) :
    momentDFT (translationMoment f) r =
      if (∑ i, r i) = 0 then ∏ i, ZMod.dft f (r i) else 0 := by
  have hinner (n : ZMod P) :
      (∑ h : Fin m → ZMod P,
        (∏ i, ZMod.stdAddChar (-(h i*r i))) * ∏ i, f (n+h i)) =
        ZMod.stdAddChar (n*∑ i, r i) * ∏ i, ZMod.dft f (r i) := by
    calc
      _ = ∏ i, ZMod.dft (fun h => f (n+h)) (r i) := by
        simp_rw [← Finset.prod_mul_distrib]
        simp only [ZMod.dft_apply,smul_eq_mul]
        exact (Fintype.prod_sum (fun (i : Fin m) (h : ZMod P) =>
          ZMod.stdAddChar (-(h*r i)) * f (n+h))).symm
      _ = (∏ i, ZMod.stdAddChar (n*r i)) * ∏ i, ZMod.dft f (r i) := by
        simp_rw [dft_translate]
        rw [Finset.prod_mul_distrib]
      _ = _ := by rw [prod_char,Finset.mul_sum]
  have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
  calc
    _ = (P : ℂ)⁻¹ * ∑ n : ZMod P, ∑ h : Fin m → ZMod P,
        (∏ i, ZMod.stdAddChar (-(h i*r i))) * ∏ i, f (n+h i) := by
      unfold momentDFT translationMoment
      simp only [mul_left_comm _ (P : ℂ)⁻¹]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (P : ℂ)⁻¹ * ((∑ n : ZMod P, ZMod.stdAddChar (n*∑ i, r i)) *
        ∏ i, ZMod.dft f (r i)) := by
      simp_rw [hinner]
      rw [Finset.sum_mul]
    _ = _ := by
      rw [sum_char]
      by_cases hr : (∑ i, r i) = 0 <;> simp [hr,hP]

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Full translated sieve data read exact products of multiples coordinates on each resonance. -/
theorem momentDFT_sieve (N : ℕ) (c : ℕ → ℂ) {m : ℕ}
    (r : Fin m → ZMod N.factorial) :
    momentDFT (translationMoment (residueSignal N c)) r =
      if (∑ i, r i) = 0 then
        (N.factorial : ℂ)^m * ∏ i, coordinate N c (addOrderOf (r i)) else 0 := by
  rw [momentDFT_translationMoment]
  simp only [dft_residueSignal]
  split_ifs <;> simp [Finset.prod_mul_distrib]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
