import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# Exact cyclic Fourier Parseval identity

This file supplies the finite harmonic-analysis theorem needed to prove the
nonarchimedean part of Connes--Marcolli Lemma 2.33 from finite quotients.  No
Fourier isometry is assumed: character orthogonality is proved from the
primitive standard additive character and then expanded into the exact
unnormalized Parseval identity.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Finset AddChar ZMod
open scoped BigOperators ComplexConjugate

/-- Exact orthogonality kernel for the standard characters of `ZMod N`. -/
theorem fieldOneFiniteCyclicFourier_orthogonality
    (N : ℕ) [NeZero N] (j l : ZMod N) :
    ∑ k : ZMod N,
        star (ZMod.stdAddChar (-(j * k))) *
          ZMod.stdAddChar (-(l * k)) =
      if j = l then N else 0 := by
  calc
    _ = ∑ k : ZMod N, ZMod.stdAddChar (k * (j - l)) := by
      apply Finset.sum_congr rfl
      intro k _
      change conj (ZMod.stdAddChar (-(j * k))) *
          ZMod.stdAddChar (-(l * k)) = _
      rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = if j - l = 0 then Fintype.card (ZMod N) else 0 :=
      AddChar.sum_mulShift (j - l) (ZMod.isPrimitive_stdAddChar N)
    _ = if j = l then N else 0 := by
      simp [sub_eq_zero]

/-- Unnormalized Parseval identity for the literal `ZMod N` discrete Fourier
transform.  The factor is exactly the quotient cardinality. -/
theorem fieldOneFiniteCyclicFourier_parseval
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    ∑ k : ZMod N, Complex.normSq (ZMod.dft f k) =
      N * ∑ j : ZMod N, Complex.normSq (f j) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp only [ZMod.dft_apply, map_sum, smul_eq_mul,
    starRingEnd_apply]
  simp only [star_mul, Finset.sum_mul, Finset.mul_sum]
  let T : ZMod N → ZMod N → ZMod N → ℂ := fun k l j =>
    star (f j) * star (ZMod.stdAddChar (-(j * k))) *
      (ZMod.stdAddChar (-(l * k)) * f l)
  change (∑ k, ∑ l, ∑ j, T k l j) = _
  calc
    _ = ∑ k, ∑ j, ∑ l, T k l j := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, T k l j := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, T k l j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j, ∑ l, (star (f j) * f l) *
          ∑ k, star (ZMod.stdAddChar (-(j * k))) *
            ZMod.stdAddChar (-(l * k)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [T]
      ring
    _ = ∑ j, ∑ l, (star (f j) * f l) *
          (if j = l then (N : ℂ) else 0) := by
      simp_rw [fieldOneFiniteCyclicFourier_orthogonality N]
      simp
    _ = ∑ j, (N : ℂ) * (star (f j) * f j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp
      ring

/-- Parseval identity for the probability-normalized cyclic Fourier
transform. -/
theorem fieldOneFiniteCyclicFourier_normalized_parseval
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    ∑ k : ZMod N,
        Complex.normSq ((N : ℂ)⁻¹ * ZMod.dft f k) =
      (N : ℝ)⁻¹ * ∑ j : ZMod N, Complex.normSq (f j) := by
  simp_rw [Complex.normSq_mul]
  rw [← Finset.mul_sum]
  rw [fieldOneFiniteCyclicFourier_parseval]
  simp only [map_inv₀, Complex.normSq_natCast]
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  field_simp

end

end GaloisForLFunctions.RHTower
