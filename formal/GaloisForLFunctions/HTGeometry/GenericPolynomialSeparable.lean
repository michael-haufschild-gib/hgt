import GaloisForLFunctions.HTGeometry.CenteredGenericGalois
import GaloisForLFunctions.HTGeometry.VandermondeSign

/-!
# The generic and centered generic polynomials are separable

Both are products of the linear factors attached to pairwise distinct roots, so both are separable.

Separability of the centered polynomial with a vanishing constant term is what shows the constant
term does not divide the discriminant, which is the divisibility the Kummer step reduces to.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- **The generic monic polynomial is separable.** -/
theorem separable_genericMonicF : (genericMonicF K d).Separable := by
  rw [genericMonicF]
  exact (Polynomial.separable_prod_X_sub_C_iff (f := genericRoot K d)).2
    genericRoot_injective

/-- **The centered generic polynomial is separable.** -/
theorem separable_centeredMonicF [CharZero K] : (centeredMonicF K d).Separable := by
  rw [centeredMonicF]
  exact (Polynomial.separable_prod_X_sub_C_iff (f := centeredRoot K d)).2
    centeredRoot_injective

/-- **The centered generic polynomial is separable over the centered field.** -/
theorem separable_centeredMonicL [CharZero K] : (centeredMonicL K d).Separable := by
  rw [centeredMonicL]
  exact (Polynomial.separable_prod_X_sub_C_iff (f := centeredRootIn K d)).2
    centeredRootIn_injective

/-- **Centering does not change the Vandermonde product.**  So the square root of the discriminant
of the centered polynomial is the one of the uncentered polynomial. -/
theorem vandermondeProd_centeredRoot_eq [CharZero K] :
    vandermondeProd (centeredRoot K d) = vandermondeProd (genericRoot K d) := by
  have hshift : (centeredRoot K d) = fun i => genericRoot K d i - genericAverage K d := by
    funext i
    rw [centeredRoot]
  rw [hshift, vandermondeProd_sub_const]

/-- **The Vandermonde product of the generic roots changes by the sign.** -/
theorem smul_vandermondeProd_genericRoot (e : Equiv.Perm (Fin d)) :
    e • vandermondeProd (genericRoot K d) =
      (Equiv.Perm.sign e : ℤ) • vandermondeProd (genericRoot K d) := by
  have hsmul : e • vandermondeProd (genericRoot K d) =
      vandermondeProd (genericRoot K d ∘ e) := by
    rw [vandermondeProd, vandermondeProd, Finset.smul_prod']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.smul_prod']
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_sub, smul_genericRoot, smul_genericRoot]
    rfl
  rw [hsmul, vandermondeProd_comp]

/-- **The discriminant is symmetric.**  The square of the Vandermonde product of the generic roots
lies in the symmetric part, hence is a rational function of the coefficients. -/
theorem sq_vandermondeProd_genericRoot_mem :
    vandermondeProd (genericRoot K d) * vandermondeProd (genericRoot K d) ∈
      symmetricPart K d := by
  have hfix : ∀ e : Equiv.Perm (Fin d),
      e • (vandermondeProd (genericRoot K d) * vandermondeProd (genericRoot K d)) =
        vandermondeProd (genericRoot K d) * vandermondeProd (genericRoot K d) := by
    intro e
    rw [smul_mul', smul_vandermondeProd_genericRoot]
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      simp only [Units.coe_neg_one, neg_smul, one_smul, neg_mul_neg]
  exact hfix

/-! ## The discriminant square root is not a coefficient -/

theorem smul_centeredRootIn [CharZero K] (e : Equiv.Perm (Fin d)) (i : Fin d) :
    e • centeredRootIn K d i = centeredRootIn K d (e i) :=
  Subtype.ext (smul_centeredRoot e i)

/-- **The Vandermonde product of the centered roots changes by the sign.** -/
theorem smul_vandermondeProd_centeredRootIn [CharZero K] (e : Equiv.Perm (Fin d)) :
    e • vandermondeProd (centeredRootIn K d) =
      (Equiv.Perm.sign e : ℤ) • vandermondeProd (centeredRootIn K d) := by
  have hsmul : e • vandermondeProd (centeredRootIn K d) =
      vandermondeProd (centeredRootIn K d ∘ e) := by
    rw [vandermondeProd, vandermondeProd, Finset.smul_prod']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.smul_prod']
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_sub, smul_centeredRootIn, smul_centeredRootIn]
    rfl
  rw [hsmul, vandermondeProd_comp]

theorem vandermondeProd_centeredRootIn_ne_zero [CharZero K] :
    vandermondeProd (centeredRootIn K d) ≠ 0 := by
  rw [vandermondeProd]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero.2 fun hcon => ?_
  exact absurd (centeredRootIn_injective hcon) (by omega)

/-- **The square root of the discriminant is not a centered coefficient.**  An odd permutation
negates it, while it fixes every centered coefficient. -/
theorem vandermondeProd_notMem_centeredCoeffField [CharZero K] {e : Equiv.Perm (Fin d)}
    (he : Equiv.Perm.sign e = -1) :
    vandermondeProd (centeredRootIn K d) ∉ centeredCoeffField K d := by
  intro hmem
  have hfix := smul_eq_of_mem_centeredCoeffField hmem e
  rw [smul_vandermondeProd_centeredRootIn, he] at hfix
  simp only [Units.coe_neg_one, neg_smul, one_smul] at hfix
  have h2 : (2 : centeredField K d) * vandermondeProd (centeredRootIn K d) = 0 := by
    linear_combination -hfix
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact vandermondeProd_centeredRootIn_ne_zero h3

end GaloisForLFunctions.HTGeometry
