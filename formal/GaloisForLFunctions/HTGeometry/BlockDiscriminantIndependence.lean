import GaloisForLFunctions.HTGeometry.SumOfTwoSquaresNotSquare

/-!
# Independence of the block discriminants of a transverse coupling

With one transverse coupling turned on, the block attached to a hypercube edge has discriminant
`δ² + 4u²`, where `δ` is the detuning of the edge and `u` the coupling.  Over a field containing a
square root of `−1` this factors into two distinct linear polynomials in `u`, so a product over any
nonempty set of edges is squarefree and cannot be a square in the rational function field.  That is
the Kummer independence the multiquadratic splitting field needs.

## Main results

* `not_isSquare_prod_sq_add_four_sq` — the independence statement in the form the block quadratics
  produce it.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- **Independence of the block discriminants.**  If the detunings are pairwise distinct and never
opposite, no nonempty product of `δ² + 4u²` is a square in `K(u)`. -/
theorem not_isSquare_prod_sq_add_four_sq {ι : Type*} [Fintype ι] [Nonempty ι] {I : K}
    (hI : I * I = -1) (h2 : (2 : K) ≠ 0) {δ : ι → K}
    (hinj : Function.Injective δ) (hne : ∀ z z', δ z ≠ -δ z') :
    ¬ IsSquare (algebraMap K[X] (RatFunc K)
      (∏ z, (C (δ z) ^ 2 + 4 * X ^ 2))) := by
  classical
  have hI0 : I ≠ 0 := by
    intro h
    rw [h, mul_zero] at hI
    exact (by norm_num : (0 : K) ≠ -1) hI
  set root : ι × Bool → K :=
    fun p => if p.2 then I * δ p.1 / 2 else -(I * δ p.1 / 2) with hroot
  have hrootinj : Function.Injective root := by
    rintro ⟨z, a⟩ ⟨z', a'⟩ h
    have hcancel : ∀ s t : K, I * s / 2 = I * t / 2 → s = t := by
      intro s t hst
      have h2' : I * s = I * t := by
        field_simp at hst
        linear_combination I * hst
      exact mul_left_cancel₀ hI0 h2'
    have hopp : ∀ s t : K, I * s / 2 = -(I * t / 2) → s = -t := by
      intro s t hst
      have h2' : I * s = I * (-t) := by
        field_simp at hst
        linear_combination I * hst
      exact mul_left_cancel₀ hI0 h2'
    rcases a with _ | _ <;> rcases a' with _ | _ <;>
      simp only [hroot, Bool.false_eq_true, if_false, if_true] at h
    · exact congrArg (fun w => (w, false)) (hinj (hcancel _ _ (neg_injective h)))
    · exact absurd (hopp (δ z') (δ z) h.symm) (hne z' z)
    · exact absurd (hopp (δ z) (δ z') h) (hne z z')
    · exact congrArg (fun w => (w, true)) (hinj (hcancel _ _ h))
  have hfactor : ∀ z : ι, (C (δ z) ^ 2 + 4 * X ^ 2 : K[X])
      = 4 * ((X - C (root (z, true))) * (X - C (root (z, false)))) := by
    intro z
    have hrt : root (z, true) = I * δ z / 2 := by
      rw [hroot]
      simp
    have hrf : root (z, false) = -(I * δ z / 2) := by
      rw [hroot]
      simp
    have hsq : 4 * ((I * δ z / 2) * (I * δ z / 2)) = -(δ z * δ z) := by
      field_simp
      linear_combination (4 * δ z * δ z) * hI
    have hsqC : (4 : K[X]) * ((C (I * δ z / 2)) * (C (I * δ z / 2)))
        = -((C (δ z)) * (C (δ z))) := by
      have := congrArg (fun a : K => (C a : K[X])) hsq
      simpa [map_mul, map_neg, map_ofNat] using this
    rw [hrt, hrf, map_neg]
    linear_combination hsqC
  have hprod : (∏ z, (C (δ z) ^ 2 + 4 * X ^ 2) : K[X])
      = ((2 : K[X]) ^ Fintype.card ι) ^ 2 * ∏ p : ι × Bool, (X - C (root p)) := by
    rw [Finset.prod_congr rfl fun z (_ : z ∈ Finset.univ) => hfactor z]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    rw [Fintype.prod_prod_type]
    rw [Finset.prod_congr rfl fun z (_ : z ∈ Finset.univ) =>
      (Fintype.prod_bool (fun b => (X - C (root (z, b))))).symm]
    congr 1
    rw [show (4 : K[X]) = (2 : K[X]) ^ 2 by ring, ← pow_mul, mul_comm 2 (Fintype.card ι), pow_mul]
  intro hsq
  refine not_isSquare_ratFunc_prod_X_sub_C hrootinj ?_
  rw [hprod, map_mul, map_pow] at hsq
  obtain ⟨r, hr⟩ := hsq
  have h2poly : (2 : K[X]) ≠ 0 := by
    intro hcon
    exact h2 (by simpa using congrArg (fun p : K[X] => p.coeff 0) hcon)
  have hne0 : algebraMap K[X] (RatFunc K) ((2 : K[X]) ^ Fintype.card ι) ≠ 0 := by
    intro hcon
    refine pow_ne_zero (Fintype.card ι) h2poly ?_
    refine IsFractionRing.injective K[X] (RatFunc K) ?_
    rw [hcon, map_zero]
  refine ⟨r / (algebraMap K[X] (RatFunc K) ((2 : K[X]) ^ Fintype.card ι)), ?_⟩
  field_simp
  linear_combination hr

end GaloisForLFunctions.HTGeometry
