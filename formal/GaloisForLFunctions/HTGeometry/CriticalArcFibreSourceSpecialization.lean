import GaloisForLFunctions.HTGeometry.CriticalArcFibreRawIndependence

/-!
# Source-field specializations from exact arc-fibre points

Algebraic independence of a fibre point's completed raw jet gives a homomorphism from the actual
rational source field.  Truncated-inverse uniqueness then identifies its reciprocal coordinates
with the reciprocal polynomial carried by the same fibre point.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The rational presentation sends each actual source raw coordinate back to its corresponding
rational-function variable. -/
theorem criticalSourceFieldEquiv_symm_raw
    (K : Type*) [Field K] (m n : ℕ) (j : Fin (m + n)) :
    (criticalSourceFieldEquiv K m n).symm (criticalSourceRaw K m n j) =
      algebraMap (MvPolynomial (Fin (m + n)) K)
        (FractionRing (MvPolynomial (Fin (m + n)) K)) (MvPolynomial.X j) := by
  apply (criticalSourceFieldEquiv K m n).injective
  simp only [AlgEquiv.apply_symm_apply]
  change criticalSourceRaw K m n j = _
  apply Subtype.ext
  have h := AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe
    (algebraicIndependent_criticalAmbientRaw K m n) (MvPolynomial.X j)
  simpa [criticalSourceFieldEquiv, criticalSourceRaw] using
    (congrArg Subtype.val h).symm

/-- `K`-algebra specialization of the actual source field determined by an exact arc-fibre point. -/
noncomputable def criticalArcFibreSourceSpecialization
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n) :
    criticalSourceField K m n →ₐ[K] CriticalArcLaurentField K m n :=
  (IntermediateField.adjoin K (Set.range (criticalArcFibreRawCoordinate p))).val.comp
    ((algebraicIndependent_criticalArcFibreRawCoordinate K hm hn p).aevalEquivField.toAlgHom.comp
      (criticalSourceFieldEquiv K m n).symm.toAlgHom)

/-- The source specialization evaluates actual raw coordinates at the fibre point's completed raw
jet. -/
@[simp] theorem criticalArcFibreSourceSpecialization_raw
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n)
    (j : Fin (m + n)) :
    criticalArcFibreSourceSpecialization K hm hn p (criticalSourceRaw K m n j) =
      criticalArcFibreRawCoordinate p j := by
  change ((IntermediateField.adjoin K
      (Set.range (criticalArcFibreRawCoordinate p))).val
    ((algebraicIndependent_criticalArcFibreRawCoordinate K hm hn p).aevalEquivField
      ((criticalSourceFieldEquiv K m n).symm (criticalSourceRaw K m n j)))) = _
  rw [criticalSourceFieldEquiv_symm_raw K m n j]
  have h := AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe
    (algebraicIndependent_criticalArcFibreRawCoordinate K hm hn p)
    (MvPolynomial.X j)
  simpa using congrArg Subtype.val h

/-- The actual source raw polynomial specializes to the fibre point's completed raw polynomial. -/
theorem criticalSourceRawPolynomial_map_arcFibreSpecialization
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n) :
    (criticalSourceRawPolynomial K m n).map
        (criticalArcFibreSourceSpecialization K hm hn p).toRingHom =
      criticalArcFibreRawPolynomial p := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < m + n
  · rw [Polynomial.coeff_map, criticalSourceRawPolynomial_coeff K m n k hk,
      show (criticalArcFibreSourceSpecialization K hm hn p).toRingHom
          (criticalSourceRaw K m n ⟨k, hk⟩) =
          criticalArcFibreRawCoordinate p ⟨k, hk⟩ by
        exact criticalArcFibreSourceSpecialization_raw K hm hn p ⟨k, hk⟩]
    rfl
  · have hsource : (criticalSourceRawPolynomial K m n).coeff k = 0 := by
      rw [criticalSourceRawPolynomial, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      omega
    rw [Polynomial.coeff_map, hsource, map_zero,
      criticalArcFibreRawPolynomial_coeff_eq_zero_of_add_le hn p
        (Nat.le_of_not_gt hk)]

/-- The actual reciprocal source polynomial, after specialization, is another inverse of the
completed fibre raw polynomial modulo the horizon. -/
theorem criticalSourceReciprocalPolynomial_map_arcFibreSpecialization_inverse
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n) :
    (X : (CriticalArcLaurentField K m n)[X]) ^ (m + n) ∣
      criticalArcFibreRawPolynomial p *
        (criticalSourceReciprocalPolynomial K m n).map
          (criticalArcFibreSourceSpecialization K hm hn p).toRingHom - 1 := by
  have h := Polynomial.map_dvd
    (criticalArcFibreSourceSpecialization K hm hn p).toRingHom
    (X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n)
  simpa only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X,
    criticalSourceRawPolynomial_map_arcFibreSpecialization K hm hn p] using h

/-- The completed raw polynomial has nonzero constant coefficient. -/
theorem criticalArcFibreRawPolynomial_coeff_zero_ne_zero
    {K : Type*} [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : CriticalArcFibre K m n) :
    (criticalArcFibreRawPolynomial p).coeff 0 ≠ 0 := by
  obtain ⟨hzero, _⟩ := coeff_recursion_of_dvd (criticalArcFibre_truncated_inverse p)
  have hprod := hzero (by omega : 0 < m + n)
  intro hz
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

/-- The source specialization evaluates actual reciprocal coordinates at the fibre point's
completed reciprocal jet. -/
@[simp] theorem criticalArcFibreSourceSpecialization_recip
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n)
    (j : Fin (m + n)) :
    criticalArcFibreSourceSpecialization K hm hn p (criticalSourceRecip K m n j) =
      (criticalArcFibreReciprocalPolynomial p).coeff (j : ℕ) := by
  have heq := coeff_eq_of_dvd_truncated_inverse
    (criticalArcFibreRawPolynomial_coeff_zero_ne_zero hm hn p)
    (criticalArcFibre_truncated_inverse p)
    (criticalSourceReciprocalPolynomial_map_arcFibreSpecialization_inverse K hm hn p)
    j.isLt
  rw [Polynomial.coeff_map,
    criticalSourceReciprocalPolynomial_coeff K m n (j : ℕ) j.isLt] at heq
  exact heq.symm

end

end GaloisForLFunctions.HTGeometry
