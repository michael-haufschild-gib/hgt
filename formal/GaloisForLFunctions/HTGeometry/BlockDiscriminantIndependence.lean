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


/-! ### The independence without a square root of `−1`

The factorization into linear polynomials is not needed: each block discriminant is separable
because its only critical point is the origin, where it takes the nonzero value `δ²`, and two block
discriminants are coprime because they differ by a nonzero constant.  A product of pairwise coprime
separable polynomials is separable, hence squarefree, hence not a square in the rational function
field.  This removes the hypothesis that the base field contains `√(−1)`.
-/

namespace BlockDiscriminant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem four_ne_zero (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have h : (4 : K) = 2 * 2 := by norm_num
  rw [h]
  exact mul_ne_zero h2 h2

theorem eight_ne_zero (h2 : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  have h : (8 : K) = 2 * 2 * 2 := by norm_num
  rw [h]
  exact mul_ne_zero (mul_ne_zero h2 h2) h2

theorem derivative_block (c : K) :
    Polynomial.derivative (C c ^ 2 + 4 * X ^ 2 : K[X]) = C (8 : K) * X := by
  rw [map_ofNat, sq (C c), ← map_mul]
  simp
  ring

theorem separable_block (h2 : (2 : K) ≠ 0) {c : K} (hc : c ≠ 0) :
    (C c ^ 2 + 4 * X ^ 2 : K[X]).Separable := by
  have hcc : c * c ≠ 0 := mul_ne_zero hc hc
  have hsq : (C c : K[X]) ^ 2 = C (c * c) := by rw [sq, ← map_mul]
  have hcoX : IsCoprime (C c ^ 2 + 4 * X ^ 2 : K[X]) X := by
    refine ⟨C (c * c)⁻¹, -(C (c * c)⁻¹ * 4 * X), ?_⟩
    have h1 : (C (c * c)⁻¹ : K[X]) * C (c * c) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hcc, map_one]
    rw [hsq]
    linear_combination h1
  have hco8 : IsCoprime (C c ^ 2 + 4 * X ^ 2 : K[X]) (C (8 : K)) := by
    refine ⟨0, C ((8 : K)⁻¹), ?_⟩
    rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ (eight_ne_zero h2), map_one]
  show IsCoprime _ (Polynomial.derivative _)
  rw [derivative_block]
  exact hco8.mul_right hcoX

theorem isCoprime_block {c c' : K} (hcc : c * c - c' * c' ≠ 0) :
    IsCoprime (C c ^ 2 + 4 * X ^ 2 : K[X]) (C c' ^ 2 + 4 * X ^ 2 : K[X]) := by
  refine ⟨C (c * c - c' * c')⁻¹, -C (c * c - c' * c')⁻¹, ?_⟩
  have h1 : (C (c * c - c' * c')⁻¹ : K[X]) * C (c * c - c' * c') = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hcc, map_one]
  rw [map_sub] at h1
  rw [show (C c : K[X]) ^ 2 = C (c * c) from by rw [sq, ← map_mul],
    show (C c' : K[X]) ^ 2 = C (c' * c') from by rw [sq, ← map_mul]]
  linear_combination h1

theorem natDegree_block (h2 : (2 : K) ≠ 0) (c : K) :
    (C c ^ 2 + 4 * X ^ 2 : K[X]).natDegree = 2 := by
  have hsq : (C c : K[X]) ^ 2 = C (c * c) := by rw [sq, ← map_mul]
  have h4 : (4 : K[X]) ≠ 0 := by
    intro hcon
    exact four_ne_zero h2 (by simpa using congrArg (fun p : K[X] => p.coeff 0) hcon)
  have hX : (X : K[X]) ^ 2 ≠ 0 := pow_ne_zero 2 Polynomial.X_ne_zero
  rw [hsq, add_comm, Polynomial.natDegree_add_C, Polynomial.natDegree_mul h4 hX,
    Polynomial.natDegree_X_pow]
  simp

theorem block_ne_zero (h2 : (2 : K) ≠ 0) (c : K) : (C c ^ 2 + 4 * X ^ 2 : K[X]) ≠ 0 := by
  intro hcon
  have := congrArg Polynomial.natDegree hcon
  rw [natDegree_block h2 c] at this
  simp at this

end BlockDiscriminant

/-- **Independence of the block discriminants, over any field of characteristic `≠ 2`.**  If the
detunings are pairwise distinct and never opposite, no nonempty product of `δ² + 4u²` is a square in
`K(u)`.  No square root of `−1` is needed. -/
theorem not_isSquare_prod_sq_add_four_sq' {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) {δ : ι → K}
    (hinj : Function.Injective δ) (hne : ∀ z z', δ z ≠ -δ z') :
    ¬ IsSquare (algebraMap K[X] (RatFunc K)
      (∏ z, (C (δ z) ^ 2 + 4 * X ^ 2))) := by
  classical
  have hδ0 : ∀ z, δ z ≠ 0 := fun z hz => hne z z (by rw [hz, neg_zero])
  have hdiff : ∀ z z' : ι, z ≠ z' → δ z * δ z - δ z' * δ z' ≠ 0 := by
    intro z z' hzz hcon
    have hfac : (δ z - δ z') * (δ z + δ z') = 0 := by linear_combination hcon
    rcases mul_eq_zero.mp hfac with h | h
    · exact hzz (hinj (sub_eq_zero.mp h))
    · exact hne z z' (by linear_combination h)
  refine not_isSquare_algebraMap_of_squarefree ?_ ?_
  · refine (Polynomial.separable_prod' ?_ ?_).squarefree
    · intro z _ z' _ hzz
      exact BlockDiscriminant.isCoprime_block (hdiff z z' hzz)
    · intro z _
      exact BlockDiscriminant.separable_block h2 (hδ0 z)
  · intro hu
    have hz := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_prod _ _ (fun z _ => BlockDiscriminant.block_ne_zero h2 (δ z))] at hz
    have hz0 := (Finset.sum_eq_zero_iff.mp hz) (Classical.arbitrary ι) (Finset.mem_univ _)
    rw [BlockDiscriminant.natDegree_block h2] at hz0
    exact absurd hz0 (by norm_num)

end GaloisForLFunctions.HTGeometry
