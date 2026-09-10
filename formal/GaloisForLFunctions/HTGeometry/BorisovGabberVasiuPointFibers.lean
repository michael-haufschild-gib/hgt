import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuEtale
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Point fibers of etale characteristic-power maps

The degree-changing triangular family from Borisov--Gabber--Vasiu separates
etale infinitesimal lifting from global injectivity. Its characteristic-two
fibers have one or two points according to the vanishing leading coefficient.
The coordinate identities identify the point map with the certified polynomial
pullback; algebraically closed field-valued surjectivity is proved separately.
-/

open Polynomial
open scoped Classical

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- Characteristic-power maps are surjective on algebraically closed field-valued points. -/
theorem bgv_powerPoint_surjective [IsAlgClosed K] (p : ℕ) [CharP K p] (b : K) :
    Function.Surjective (fun x : K => x + b * x ^ p) := by
  let f : Polynomial K := bgvEtaleEquation p 0 b
  have hd : f.derivative = 1 := bgvEtaleEquation_derivative p 0 b
  have hn : f.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.derivative_C] at hd
    exact zero_ne_one hd
  simpa [f, bgvEtaleEquation] using IsAlgClosed.eval_surjective hn

/-- An exact quadratic fiber law, retaining the degree-drop case `b = 0`. -/
theorem bgv_quadratic_zeroFiber (b : K) :
    {x : K | x + b * x ^ 2 = 0} = {0, -b⁻¹} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hb : b = 0
  · simp [hb]
  · rw [show x + b * x ^ 2 = x * (1 + b * x) by ring, mul_eq_zero]
    apply or_congr_right
    constructor
    · intro h
      apply (mul_left_cancel₀ hb)
      rw [mul_neg, mul_inv_cancel₀ hb]
      linear_combination h
    · rintro rfl
      rw [mul_neg, mul_inv_cancel₀ hb, add_neg_cancel]

/-- In characteristic two every fiber is a translate of the exact kernel pair. -/
theorem bgv_quadratic_imageFiber [CharP K 2] (b x : K) :
    {y : K | y + b * y ^ 2 = x + b * x ^ 2} = {x, x - b⁻¹} := by
  ext y
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hdiff : (y - x) + b * (y - x) ^ 2 =
      (y + b * y ^ 2) - (x + b * x ^ 2) := by
    linear_combination b * x * (x - y) * htwo
  have h := Set.ext_iff.mp (bgv_quadratic_zeroFiber b) (y - x)
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rw [hdiff, sub_eq_zero, sub_eq_zero] at h
  rw [h]
  apply or_congr_right
  constructor <;> intro h <;> linear_combination h

/-- Fiber size jumps from two to one exactly at the vanishing leading coefficient. -/
theorem bgv_quadratic_imageFiber_ncard [CharP K 2] (b x : K) :
    Set.ncard {y : K | y + b * y ^ 2 = x + b * x ^ 2} = if b = 0 then 1 else 2 := by
  classical
  rw [bgv_quadratic_imageFiber]
  by_cases hb : b = 0
  · simp [hb]
  · rw [if_neg hb]
    apply Set.ncard_pair
    intro h
    have hi : b⁻¹ = 0 := by linear_combination h
    exact hb (inv_eq_zero.mp hi)

/-- The exact fiber cardinality holds over every target point, not only a chosen image. -/
theorem bgv_quadratic_fiber_ncard [IsAlgClosed K] [CharP K 2] (b a : K) :
    Set.ncard {y : K | y + b * y ^ 2 = a} = if b = 0 then 1 else 2 := by
  obtain ⟨x, hx⟩ := bgv_powerPoint_surjective 2 b a
  rw [← hx]
  exact bgv_quadratic_imageFiber_ncard b x

/-- The affine-plane polynomial pullback has the proved formal-etale certificate. -/
theorem bgv_quadraticPlane_formallyEtale [CharP K 2] :
    (bgvPowerMap (R := Polynomial K) 2 X).toRingHom.FormallyEtale :=
  bgvPowerMap_formallyEtale 2 X

/-- On the two coordinate generators the algebra map gives the stated plane map. -/
theorem bgv_quadraticPlane_coordinates (x y : K) :
    (Polynomial.evalEval y x (bgvPowerMap (R := Polynomial K) 2 X X),
      Polynomial.evalEval y x (bgvPowerMap (R := Polynomial K) 2 X (C X))) =
        (x + y * x ^ 2, y) := by
  simp [bgvPowerMap, Polynomial.evalEval]

/-- The degree-changing affine-plane point map is nevertheless surjective. -/
theorem bgv_quadraticPlane_surjective [IsAlgClosed K] [CharP K 2] :
    Function.Surjective (fun z : K × K => (z.1 + z.2 * z.1 ^ 2, z.2)) := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := bgv_powerPoint_surjective 2 b a
  exact ⟨(x, b), Prod.ext hx rfl⟩

/-- The same map identifies distinct points despite its etale local lifting property. -/
theorem bgv_quadraticPlane_not_injective [CharP K 2] :
    ¬ Function.Injective (fun z : K × K => (z.1 + z.2 * z.1 ^ 2, z.2)) := by
  intro h
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have he : (fun z : K × K => (z.1 + z.2 * z.1 ^ 2, z.2)) (0, 1) =
      (fun z : K × K => (z.1 + z.2 * z.1 ^ 2, z.2)) (1, 1) := by
    apply Prod.ext <;> simp [one_add_one_eq_two, htwo]
  exact zero_ne_one (congrArg Prod.fst (h he))

end GaloisForLFunctions.HTGeometry
