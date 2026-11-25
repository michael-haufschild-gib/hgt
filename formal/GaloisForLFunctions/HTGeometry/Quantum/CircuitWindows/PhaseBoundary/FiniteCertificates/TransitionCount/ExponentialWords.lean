import Mathlib.Algebra.MonoidAlgebra.Basic
import GaloisForLFunctions.HTGeometry.ExpPolyZeroCount

/-! # Uniform local zero counts for real exponential sums -/

open Finset Set
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount
noncomputable section

abbrev Word := AddMonoidAlgebra ℂ ℂ

private def character (t : ℝ) : Multiplicative ℂ →* ℂ where
  toFun y := Complex.exp (y.toAdd * t)
  map_one' := by change Complex.exp (0 * _) = 1; rw [zero_mul,Complex.exp_zero]
  map_mul' y z := by change Complex.exp ((y.toAdd+z.toAdd)*_) = _; rw [add_mul,Complex.exp_add]

/-- Equal exponents are collected in the coefficient of one group element. -/
def evaluate (t : ℝ) : Word →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ ℂ (character t)

theorem evaluate_single (t : ℝ) (y c : ℂ) :
    evaluate t (AddMonoidAlgebra.single y c) = c * Complex.exp (y*t) := by
  rw [evaluate,AddMonoidAlgebra.lift_single]; rfl

private theorem evaluate_sum (w : Word) (t : ℝ) :
    evaluate t w = ∑ y ∈ w.coeff.support, w.coeff y * Complex.exp (y*t) := by
  rw [evaluate,AddMonoidAlgebra.lift_apply']; rfl

/-- A nontrivial real-valued word has a linear zero-count bound on every
interval, with the same constant at all time origins. -/
theorem word_zero_bound (w : Word) (hreal : ∀ t, (evaluate t w).im=0)
    (hne : ∃ t, evaluate t w≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ a b : ℝ, a<b → ∀ Z : Finset ℝ, (∀ t∈Z, t∈Icc a b) →
      (∀ t∈Z, evaluate t w=0) → (Z.card:ℝ) ≤ C*(1+(b-a)) := by
  classical
  let S := w.coeff.support
  have hs : S.Nonempty := by
    obtain ⟨t,ht⟩ := hne
    by_contra h
    rw [evaluate_sum, show w.coeff.support=∅ from Finset.not_nonempty_iff_eq_empty.mp h,
      Finset.sum_empty] at ht
    exact ht rfl
  let g := ∑ y ∈ S, |y.im|
  have hg : 0≤g := Finset.sum_nonneg (fun y _ => abs_nonneg y.im)
  have hgy (y : ℂ) (hy : y∈S) : |y.im|≤g :=
    Finset.single_le_sum (fun z _ => abs_nonneg z.im) hy
  let A : ℝ := 3^S.card * ((S.card:ℝ)+1)
  let B : ℝ := 3^S.card * (2*g/Real.pi)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro a b hab Z hm hz
  have h := card_zeros_le_expPoly (S := S) (C := w.coeff) hs
    (fun _ hy => Finsupp.mem_support_iff.mp hy) hgy
    (fun t => by rw [←evaluate_sum]; exact hreal t) hab Z hm
    (fun t ht => by rw [←evaluate_sum,hz t ht,Complex.zero_re])
  have hρ : 0≤(b-a)*g/Real.pi := by positivity
  have hbound : (Z.card : ℝ) ≤ A+B*(b-a) := by
    calc
      _ ≤ _ := h
      _ ≤ 3^S.card * ((S.card:ℝ) + 2 * ((b-a)*g/Real.pi) + 1) := by linarith
      _ = _ := by dsimp only [A,B]; ring
  nlinarith only [hbound,mul_nonneg hA (sub_nonneg.mpr hab.le),hB]

#print axioms word_zero_bound
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount

