import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# Rank-one Hilbert--Schmidt polarization

This module supplies the coordinate-free rank-one formulas missing from the generic
Hilbert--Schmidt operator layer.  Besides the product norm law, it computes the exact
Hilbert--Schmidt pairing of two rank-one operators and hence the full squared norm of their sum.
These are the finite-rank algebraic inputs for cutoff Ward-curvature laws.
-/

open Complex
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap InnerProductSpace

/-- Every rank-one operator between complex Hilbert spaces is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_rankOne
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (x : E) (y : F) :
    IsHilbertSchmidt (rankOne ℂ x y) := by
  unfold IsHilbertSchmidt
  have hs := (hsBasis ℂ F).summable_norm_inner_sq y
  apply (hs.mul_right (‖x‖ ^ 2)).congr
  intro i
  rw [rankOne_apply, norm_smul, mul_pow]
  rw [norm_inner_symm]

/-- The Hilbert--Schmidt norm of a rank-one operator is the product of the vector norms. -/
theorem hsNormSq_rankOne
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (x : E) (y : F) :
    hsNormSq (rankOne ℂ x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  let b := hsBasis ℂ F
  have hHS := isHilbertSchmidt_rankOne x y
  rw [hsNormSq_eq hHS b]
  simp_rw [rankOne_apply, norm_smul, mul_pow]
  rw [tsum_mul_right]
  have hsum : (∑' i, ‖inner ℂ y (b i)‖ ^ 2) = ‖y‖ ^ 2 := by
    calc
      _ = ∑' i, ‖inner ℂ (b i) y‖ ^ 2 := by
        apply tsum_congr
        intro i
        rw [norm_inner_symm]
      _ = _ := b.tsum_norm_inner_sq y
  rw [hsum]
  ring

/-- Exact Hilbert--Schmidt pairing of two rank-one operators. -/
theorem hsInner_rankOne
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (x u : E) (y v : F) :
    hsInner (rankOne ℂ x y) (rankOne ℂ u v) =
      inner ℂ x u * inner ℂ v y := by
  unfold hsInner
  simp_rw [rankOne_apply, inner_smul_left, inner_smul_right]
  let b := hsBasis ℂ F
  calc
    (∑' i, (starRingEnd ℂ) (inner ℂ y (b i)) *
        (inner ℂ v (b i) * inner ℂ x u)) =
        ∑' i, (inner ℂ v (b i) * inner ℂ (b i) y) * inner ℂ x u := by
      apply tsum_congr
      intro i
      rw [inner_conj_symm (b i) y]
      ring
    _ = (∑' i, inner ℂ v (b i) * inner ℂ (b i) y) * inner ℂ x u := by
      rw [tsum_mul_right]
    _ = inner ℂ v y * inner ℂ x u := by
      rw [b.tsum_inner_mul_inner]
    _ = inner ℂ x u * inner ℂ v y := by ring

/-- Scalar multiplication scales squared Hilbert--Schmidt norm by the scalar norm squared. -/
theorem hsNormSq_smul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) (c : ℂ) :
    hsNormSq (c • T) = ‖c‖ ^ 2 * hsNormSq T := by
  let b := hsBasis ℂ E
  rw [hsNormSq_eq (hT.smul c) b, hsNormSq_eq hT b, ← tsum_mul_left]
  apply tsum_congr
  intro i
  simp only [smul_apply, norm_smul]
  ring

/-- Full Hilbert--Schmidt polarization for the squared norm of a sum. -/
theorem hsNormSq_add
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {S T : E →L[ℂ] F}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNormSq (S + T) = hsNormSq S + hsNormSq T +
      2 * Complex.re (hsInner S T) := by
  have hST := hS.add hT
  have hpair : hsInner (S + T) (S + T) =
      (hsInner S S + hsInner S T) + (hsInner T S + hsInner T T) := by
    rw [hsInner_add_left hS hT hST,
      hsInner_add_right hS hS hT,
      hsInner_add_right hT hS hT]
  have hcross : Complex.re (hsInner T S) = Complex.re (hsInner S T) := by
    rw [hsInner_conj_symm T S, Complex.conj_re]
  have hSS : Complex.re (hsInner S S) = hsNormSq S := hsInner_self_re hS
  have hTT : Complex.re (hsInner T T) = hsNormSq T := hsInner_self_re hT
  calc
    hsNormSq (S + T) = Complex.re (hsInner (S + T) (S + T)) :=
      (hsInner_self_re hST).symm
    _ = Complex.re (hsInner S S) + Complex.re (hsInner S T) +
        (Complex.re (hsInner T S) + Complex.re (hsInner T T)) := by
      rw [hpair]
      simp only [Complex.add_re]
    _ = hsNormSq S + hsNormSq T + 2 * Complex.re (hsInner S T) := by
      rw [hSS, hTT, hcross]
      ring

/-- Exact squared norm of a sum of two rank-one operators. -/
theorem hsNormSq_rankOne_add_rankOne
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (x u : E) (y v : F) :
    hsNormSq (rankOne ℂ x y + rankOne ℂ u v) =
      ‖x‖ ^ 2 * ‖y‖ ^ 2 + ‖u‖ ^ 2 * ‖v‖ ^ 2 +
        2 * Complex.re (inner ℂ x u * inner ℂ v y) := by
  rw [hsNormSq_add (isHilbertSchmidt_rankOne x y)
      (isHilbertSchmidt_rankOne u v),
    hsNormSq_rankOne, hsNormSq_rankOne, hsInner_rankOne]

end

end GaloisForLFunctions.HTGeometry
