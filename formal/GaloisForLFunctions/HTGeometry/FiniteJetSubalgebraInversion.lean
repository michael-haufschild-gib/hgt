import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem

/-!
# The finite jet transforms are invertible over the base ring

The reciprocal and unit-square transforms of a finite positive jet already generate the same
*field* as the jet itself.  This file upgrades both statements from `IntermediateField.adjoin` to
`Algebra.adjoin`: the transforms are invertible over the base *ring*, with no denominators beyond
the constant `2` supplied by characteristic zero.

That upgrade is what allows the Schur coordinate ring of the critical source to be compared with
the raw coordinate ring as a localization rather than merely as a birational model.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- Every coefficient of a polynomial belongs to a fixed subalgebra. -/
def PolynomialCoefficientsInSubalgebra
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    (J : Subalgebra F E) (P : Polynomial E) : Prop :=
  ∀ k, P.coeff k ∈ J

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem polynomialCoefficientsInSubalgebra_one (J : Subalgebra F E) :
    PolynomialCoefficientsInSubalgebra J 1 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact J.one_mem
  · exact J.zero_mem

theorem PolynomialCoefficientsInSubalgebra.sub {J : Subalgebra F E} {P Q : Polynomial E}
    (hP : PolynomialCoefficientsInSubalgebra J P)
    (hQ : PolynomialCoefficientsInSubalgebra J Q) :
    PolynomialCoefficientsInSubalgebra J (P - Q) := by
  intro k
  rw [Polynomial.coeff_sub]
  exact J.sub_mem (hP k) (hQ k)

theorem PolynomialCoefficientsInSubalgebra.neg {J : Subalgebra F E} {P : Polynomial E}
    (hP : PolynomialCoefficientsInSubalgebra J P) :
    PolynomialCoefficientsInSubalgebra J (-P) := by
  intro k
  rw [Polynomial.coeff_neg]
  exact J.neg_mem (hP k)

theorem PolynomialCoefficientsInSubalgebra.mul {J : Subalgebra F E} {P Q : Polynomial E}
    (hP : PolynomialCoefficientsInSubalgebra J P)
    (hQ : PolynomialCoefficientsInSubalgebra J Q) :
    PolynomialCoefficientsInSubalgebra J (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact J.sum_mem fun ij _ => J.mul_mem (hP ij.1) (hQ ij.2)

theorem PolynomialCoefficientsInSubalgebra.pow {J : Subalgebra F E} {P : Polynomial E}
    (hP : PolynomialCoefficientsInSubalgebra J P) (r : ℕ) :
    PolynomialCoefficientsInSubalgebra J (P ^ r) := by
  induction r with
  | zero => simpa using polynomialCoefficientsInSubalgebra_one J
  | succ r ihr => simpa [pow_succ] using ihr.mul hP

theorem PolynomialCoefficientsInSubalgebra.sum {I : Type*} {J : Subalgebra F E}
    {s : Finset I} {P : I → Polynomial E}
    (hP : ∀ i ∈ s, PolynomialCoefficientsInSubalgebra J (P i)) :
    PolynomialCoefficientsInSubalgebra J (∑ i ∈ s, P i) := by
  intro k
  change (Polynomial.lcoeff E k) (∑ i ∈ s, P i) ∈ J
  rw [map_sum]
  exact J.sum_mem fun i hi => hP i hi k

theorem finiteUnitPolynomial_coefficientsIn_adjoinSubalgebra {L : ℕ} (u : Fin L → E) :
    PolynomialCoefficientsInSubalgebra (Algebra.adjoin F (Set.range u))
      (finiteUnitPolynomial u) := by
  intro k
  rw [finiteUnitPolynomial, Polynomial.coeff_add, Polynomial.coeff_one]
  apply Subalgebra.add_mem
  · split_ifs
    · exact (Algebra.adjoin F (Set.range u)).one_mem
    · exact (Algebra.adjoin F (Set.range u)).zero_mem
  · change (Polynomial.lcoeff E k)
      (∑ i : Fin L, Polynomial.monomial ((i : ℕ) + 1) (u i)) ∈ _
    rw [map_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    change (Polynomial.monomial ((i : ℕ) + 1) (u i)).coeff k ∈ _
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact Algebra.subset_adjoin (Set.mem_range_self i)
    · exact (Algebra.adjoin F (Set.range u)).zero_mem

theorem truncatedReciprocalKernel_coefficientsInSubalgebra [CharZero E]
    {J : Subalgebra F E} (N : ℕ) (U : Polynomial E)
    (hU : PolynomialCoefficientsInSubalgebra J U) :
    PolynomialCoefficientsInSubalgebra J (truncatedReciprocalKernel N U) := by
  rw [truncatedReciprocalKernel]
  refine PolynomialCoefficientsInSubalgebra.sum fun j _ => ?_
  exact (hU.sub (polynomialCoefficientsInSubalgebra_one J)).neg.pow j

theorem adjoinSubalgebra_finiteReciprocalPositive_le [CharZero E] {L : ℕ} (u : Fin L → E) :
    Algebra.adjoin F (Set.range (finiteReciprocalPositive u))
      ≤ Algebra.adjoin F (Set.range u) := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact truncatedReciprocalKernel_coefficientsInSubalgebra (L + 1) (finiteUnitPolynomial u)
    (finiteUnitPolynomial_coefficientsIn_adjoinSubalgebra u) ((i : ℕ) + 1)

/-- **The finite reciprocal transform is invertible over the base ring.** -/
theorem adjoinSubalgebra_finiteReciprocalPositive_eq [CharZero E] {L : ℕ} (u : Fin L → E) :
    Algebra.adjoin F (Set.range (finiteReciprocalPositive u))
      = Algebra.adjoin F (Set.range u) := by
  refine le_antisymm (adjoinSubalgebra_finiteReciprocalPositive_le u) ?_
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  let U := finiteUnitPolynomial u
  let Y := truncatedReciprocalKernel (L + 1) U
  let V := finiteUnitPolynomial (finiteReciprocalPositive u)
  let W := truncatedReciprocalKernel (L + 1) V
  have hU0 : U.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero u
  have hV0 : V.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero _
  have hUY : Polynomial.X ^ (L + 1) ∣ U * Y - 1 :=
    truncatedReciprocalKernel_isInverseMod (L + 1) U hU0
  have hUV : Polynomial.X ^ (L + 1) ∣ U * V - 1 :=
    X_pow_dvd_mul_sub_of_coeff_eq (L + 1) U V Y hUY
      (finiteUnitPolynomial_reciprocal_coeff u)
  have hVW : Polynomial.X ^ (L + 1) ∣ V * W - 1 :=
    truncatedReciprocalKernel_isInverseMod (L + 1) V hV0
  have hVU : Polynomial.X ^ (L + 1) ∣ V * U - 1 := by
    simpa [mul_comm] using hUV
  have hcoeff : W.coeff ((i : ℕ) + 1) = U.coeff ((i : ℕ) + 1) :=
    inverse_mod_coeff_unique (L + 1) V W U hV0 hVW hVU (by omega)
  show u i ∈ Algebra.adjoin F (Set.range (finiteReciprocalPositive u))
  rw [← finiteUnitPolynomial_coeff_succ u i, ← hcoeff]
  exact truncatedReciprocalKernel_coefficientsInSubalgebra (L + 1) V
    (finiteUnitPolynomial_coefficientsIn_adjoinSubalgebra (finiteReciprocalPositive u))
    ((i : ℕ) + 1)

theorem adjoinSubalgebra_finiteUnitSquarePositive_le {L : ℕ} (z : Fin L → E) :
    Algebra.adjoin F (Set.range (finiteUnitSquarePositive z))
      ≤ Algebra.adjoin F (Set.range z) := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact (finiteUnitPolynomial_coefficientsIn_adjoinSubalgebra z).pow 2 ((i : ℕ) + 1)

/-- **Halving is available in any subalgebra over a field of characteristic zero.** -/
theorem inv_two_mem_subalgebra [CharZero F] (J : Subalgebra F E) : (2 : E)⁻¹ ∈ J := by
  have h : algebraMap F E ((2 : F)⁻¹) = (2 : E)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [← h]
  exact J.algebraMap_mem _

/-- **The finite unit-square transform is invertible over the base ring.** -/
theorem adjoinSubalgebra_finiteUnitSquarePositive_eq [CharZero F] [CharZero E]
    {L : ℕ} (z : Fin L → E) :
    Algebra.adjoin F (Set.range (finiteUnitSquarePositive z))
      = Algebra.adjoin F (Set.range z) := by
  refine le_antisymm (adjoinSubalgebra_finiteUnitSquarePositive_le z) ?_
  set J := Algebra.adjoin F (Set.range (finiteUnitSquarePositive z)) with hJ
  have htwoinv : (2 : E)⁻¹ ∈ J := inv_two_mem_subalgebra J
  have hzmem : ∀ k (hk : k < L), z ⟨k, hk⟩ ∈ J := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        rcases k with _ | k
        · have hsq : finiteUnitSquarePositive z ⟨0, hk⟩ ∈ J :=
            Algebra.subset_adjoin (Set.mem_range_self (⟨0, hk⟩ : Fin L))
          have hrel := finiteUnitSquarePositive_zero z hk
          have hsolve : z ⟨0, hk⟩ = (2 : E)⁻¹ * finiteUnitSquarePositive z ⟨0, hk⟩ := by
            rw [hrel]; field_simp
          rw [hsolve]
          exact J.mul_mem htwoinv hsq
        · have hsq : finiteUnitSquarePositive z ⟨k + 1, hk⟩ ∈ J :=
            Algebra.subset_adjoin (Set.mem_range_self (⟨k + 1, hk⟩ : Fin L))
          set S : E := ∑ p ∈ Finset.antidiagonal k,
            (finiteUnitPolynomial z).coeff (p.1 + 1) *
              (finiteUnitPolynomial z).coeff (p.2 + 1) with hS0
          have hS : S ∈ J := by
            refine Subalgebra.sum_mem _ fun p hp => ?_
            have hp1 := Finset.mem_antidiagonal.mp hp
            refine J.mul_mem ?_ ?_
            · rw [show (finiteUnitPolynomial z).coeff (p.1 + 1) = z ⟨p.1, by omega⟩ by
                simpa using finiteUnitPolynomial_coeff_succ z ⟨p.1, by omega⟩]
              exact ih p.1 (by omega) (by omega)
            · rw [show (finiteUnitPolynomial z).coeff (p.2 + 1) = z ⟨p.2, by omega⟩ by
                simpa using finiteUnitPolynomial_coeff_succ z ⟨p.2, by omega⟩]
              exact ih p.2 (by omega) (by omega)
          have hrel := finiteUnitSquarePositive_succ z hk
          have hsolve : z ⟨k + 1, hk⟩ = (2 : E)⁻¹ *
              (finiteUnitSquarePositive z ⟨k + 1, hk⟩ - S) := by
            rw [hrel, ← hS0]
            field_simp
            ring
          rw [hsolve]
          exact J.mul_mem htwoinv (J.sub_mem hsq hS)
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact hzmem i i.isLt

/-- **The reciprocal-square jet transform is invertible over the base ring.** -/
theorem adjoinSubalgebra_finiteReciprocalSquarePositive_eq [CharZero F] [CharZero E]
    {L : ℕ} (u : Fin L → E) :
    Algebra.adjoin F (Set.range (finiteReciprocalSquarePositive u))
      = Algebra.adjoin F (Set.range u) := by
  rw [finiteReciprocalSquarePositive,
    adjoinSubalgebra_finiteUnitSquarePositive_eq (finiteReciprocalPositive u),
    adjoinSubalgebra_finiteReciprocalPositive_eq u]

end

end GaloisForLFunctions.HTGeometry
