import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Units
import Mathlib.Tactic

/-!
# Exact trace–determinant fibres in rank two

Lapid and Shusterman, Lemma C.1 and Proposition C.2 (arXiv:2611.09555),
separate the chart with invertible upper-right entry from triangular
reduction. On the first chart the two coefficients are free coordinates.
Over a field the other chart records one root of the characteristic
polynomial. This gives a single fibre formula in all characteristics.
-/

namespace GaloisForLFunctions.RepresentationLifting
noncomputable section
open Matrix Polynomial
open scoped Matrix

/-- Fixing one diagonal entry and an invertible off-diagonal entry makes
the trace and determinant affine coordinates on the remaining row. -/
def traceDetChart {R : Type*} [CommRing R] (x : R) (y : Rˣ) : R × R ≃ R × R where
  toFun p := (x + p.2, x*p.2 - y*p.1)
  invFun p := ((↑y⁻¹ : R) * (x*(p.1-x)-p.2), p.1-x)
  left_inv := by
    rintro ⟨z,w⟩
    ext
    · change (↑y⁻¹ : R) * (x*(x+w-x) - (x*w-y*z)) = z
      rw [add_sub_cancel_left, sub_sub_cancel, ← mul_assoc, Units.inv_mul, one_mul]
    · exact add_sub_cancel_left x w
  right_inv := by
    rintro ⟨t,d⟩
    ext
    · change x + (t-x) = t
      abel
    · change x*(t-x) - y*((↑y⁻¹ : R)*(x*(t-x)-d)) = d
      rw [← mul_assoc, Units.mul_inv, one_mul, sub_sub_cancel]

/-- The quadratic root equation expressed without dividing by 2. -/
abbrev traceDetRoot {R : Type*} [CommRing R] (t d : R) := {x : R // x*(t-x)=d}

/-- A trace–determinant fibre is partitioned into the invertible-entry
chart and one affine line for each root in the ground field. -/
def traceDetFibreEquiv {K : Type*} [Field K] (t d : K) :
    {A : Matrix (Fin 2) (Fin 2) K // A.trace = t ∧ A.det = d} ≃
      (K × Kˣ) ⊕ (traceDetRoot t d × K) := by
  classical
  let encode (M : {A : Matrix (Fin 2) (Fin 2) K // A.trace=t ∧ A.det=d}) :
      (K × Kˣ) ⊕ (traceDetRoot t d × K) :=
    if h : M.1 0 1 = 0 then
      Sum.inr (⟨M.1 0 0, by
        have ht := M.2.1
        have hd := M.2.2
        rw [trace_fin_two] at ht
        rw [det_fin_two, h, zero_mul, sub_zero] at hd
        rwa [show t-M.1 0 0 = M.1 1 1 by linear_combination -ht]⟩, M.1 1 0)
    else Sum.inl (M.1 0 0, Units.mk0 _ h)
  let decode : (K × Kˣ) ⊕ (traceDetRoot t d × K) →
      {A : Matrix (Fin 2) (Fin 2) K // A.trace=t ∧ A.det=d}
    | Sum.inl (x,y) =>
        let p := (traceDetChart x y).symm (t,d)
        ⟨!![x, (y:K); p.1, p.2], by
          have h := (traceDetChart x y).apply_symm_apply (t,d)
          exact ⟨congrArg Prod.fst h, (det_fin_two_of ..).trans (congrArg Prod.snd h)⟩⟩
    | Sum.inr (x,z) =>
        ⟨!![(x:K),0;z,t-x], by
          rw [trace_fin_two_of, det_fin_two_of, zero_mul, sub_zero]
          exact ⟨by abel, x.2⟩⟩
  refine ⟨encode, decode, ?_, ?_⟩
  · intro M
    have ht := M.2.1
    have hd := M.2.2
    rw [trace_fin_two] at ht
    rw [det_fin_two] at hd
    have hw : t - M.1 0 0 = M.1 1 1 := by linear_combination -ht
    by_cases h : M.1 0 1 = 0
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [encode, decode, h, hw]
    · let y := Units.mk0 (M.1 0 1) h
      have hy : (traceDetChart (M.1 0 0) y) (M.1 1 0,M.1 1 1) = (t,d) := Prod.ext ht hd
      have hi := (traceDetChart (M.1 0 0) y).symm_apply_apply (M.1 1 0,M.1 1 1)
      rw [hy] at hi
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact congrArg Prod.fst hi | exact congrArg Prod.snd hi |
          simp [encode, decode, h, y, hi]
  · rintro (⟨x,y⟩ | ⟨x,z⟩)
    · simp [encode, decode, y.ne_zero]
    · simp [encode, decode]

/-- Uniform mass of one characteristic polynomial over a finite field
depends only on its number of distinct ground-field roots. -/
theorem card_traceDetFibre {K : Type*} [Field K] [Finite K] (t d : K) :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // A.trace=t ∧ A.det=d} =
      Nat.card K * (Nat.card K - 1 + Nat.card (traceDetRoot t d)) := by
  classical
  letI := Fintype.ofFinite K
  rw [Nat.card_congr (traceDetFibreEquiv t d), Nat.card_sum, Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Kˣ), Fintype.card_units, ← Nat.card_eq_fintype_card]
  ring

/-- Moving the origin of the eigenvalue transports the entire root fibre. -/
def traceDetRootTranslate {R : Type*} [CommRing R] (t d u : R) :
    traceDetRoot t d ≃ traceDetRoot (t+2*u) (d+u*t+u^2) where
  toFun x := ⟨x+u, by linear_combination x.2⟩
  invFun x := ⟨x-u, by linear_combination x.2⟩
  left_inv x := Subtype.ext (add_sub_cancel_right _ _)
  right_inv x := Subtype.ext (sub_add_cancel _ _)

/-- Above a repeated characteristic root there are exactly q² matrices,
in residue characteristic two as well. -/
theorem card_traceDetFibre_repeated {K : Type*} [Field K] [Finite K] (u : K) :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // A.trace=2*u ∧ A.det=u^2} = (Nat.card K)^2 := by
  letI : Unique (traceDetRoot (2*u) (u^2)) := {
    default := ⟨u,by ring⟩
    uniq := fun x => Subtype.ext (by
      change (x : K) = u
      have h : ((x:K)-u)^2=0 := by linear_combination -x.2
      exact sub_eq_zero.mp (pow_eq_zero h)) }
  rw [card_traceDetFibre, Nat.card_unique, Nat.sub_add_cancel (Nat.card_pos (α := K)), sq]

#print axioms card_traceDetFibre
#print axioms card_traceDetFibre_repeated
end
end GaloisForLFunctions.RepresentationLifting
