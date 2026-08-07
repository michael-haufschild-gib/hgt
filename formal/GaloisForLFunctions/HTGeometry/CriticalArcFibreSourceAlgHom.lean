import GaloisForLFunctions.HTGeometry.CriticalArcFibreSourceSpecialization

/-!
# Actual observation-field embeddings from exact arc-fibre points

The source specialization attached to a fibre point agrees with the common-scale embedding on the
entire actual observation field.  It therefore upgrades from a `K`-algebra homomorphism to an
observation-field algebra homomorphism.  Distinct fibre points give distinct homomorphisms.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The actual observation field acts on the arc Laurent field through the common-scale
embedding. -/
@[reducible] noncomputable def criticalObservationArcLaurentFieldAlgebra
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Algebra (criticalObservationField K m n) (CriticalArcLaurentField K m n) :=
  (criticalObservationArcEmbedding K hm hn).toRingHom.toAlgebra

/-- Source specialization agrees with the arc embedding on a raw observation generator. -/
theorem criticalArcFibreSourceSpecialization_observationRaw
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n)
    (i : Fin n) :
    criticalArcFibreSourceSpecialization K hm hn p
        (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
          (criticalObservationRaw K m n i)) =
      criticalObservationArcEmbedding K hm hn (criticalObservationRaw K m n i) := by
  let j : Fin (m + n) := ⟨m + (i : ℕ), by omega⟩
  have hcoord :
      algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
          (criticalObservationRaw K m n i) = criticalSourceRaw K m n j := by
    apply Subtype.ext
    rfl
  rw [hcoord, criticalArcFibreSourceSpecialization_raw]
  have hA : p.1.1.coeff (m + (i : ℕ)) = 0 :=
    (Polynomial.degree_lt_iff_coeff_zero p.1.1 m).mp p.2.1 _ (by omega)
  change (criticalArcFibreRawPolynomial p).coeff (m + (i : ℕ)) = _
  rw [criticalArcFibreRawPolynomial, Polynomial.coeff_add, hA, zero_add,
    criticalArcRawTail_coeff K hm hn]

/-- Source specialization agrees with the arc embedding on a reciprocal observation generator. -/
theorem criticalArcFibreSourceSpecialization_observationRecip
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n)
    (j : Fin m) :
    criticalArcFibreSourceSpecialization K hm hn p
        (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
          (criticalObservationRecip K m n j)) =
      criticalObservationArcEmbedding K hm hn (criticalObservationRecip K m n j) := by
  let k : Fin (m + n) := ⟨n + (j : ℕ), by omega⟩
  have hcoord :
      algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
          (criticalObservationRecip K m n j) = criticalSourceRecip K m n k := by
    apply Subtype.ext
    rfl
  rw [hcoord, criticalArcFibreSourceSpecialization_recip]
  have hB : p.1.2.coeff (n + (j : ℕ)) = 0 :=
    (Polynomial.degree_lt_iff_coeff_zero p.1.2 n).mp p.2.2.1 _ (by omega)
  change (criticalArcFibreReciprocalPolynomial p).coeff (n + (j : ℕ)) = _
  rw [criticalArcFibreReciprocalPolynomial, Polynomial.coeff_add, hB, zero_add,
    criticalArcReciprocalTail_coeff K hm hn]

/-- Source specialization agrees with the common-scale embedding on every element of the actual
observation field. -/
theorem criticalArcFibreSourceSpecialization_commutes
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (p : CriticalArcFibre K m n)
    (z : criticalObservationField K m n) :
    criticalArcFibreSourceSpecialization K hm hn p
        (algebraMap (criticalObservationField K m n) (criticalSourceField K m n) z) =
      criticalObservationArcEmbedding K hm hn z := by
  let S := criticalArcFibreSourceSpecialization K hm hn p
  let e := criticalObservationArcEmbedding K hm hn
  let P : ∀ x, x ∈ criticalObservationField K m n → Prop := fun x hx ↦
    S (algebraMap (criticalObservationField K m n) (criticalSourceField K m n) ⟨x, hx⟩) =
      e ⟨x, hx⟩
  change P (z : genericJetField K (m + n)) z.property
  refine IntermediateField.adjoin_induction K (p := P) ?_ ?_ ?_ ?_ ?_ z.property
  · intro x hx
    obtain ⟨s, rfl⟩ := hx
    rcases s with i | j
    · simpa [P, S, e, criticalObservationField, criticalFieldObservation,
        criticalObservationRaw] using
        criticalArcFibreSourceSpecialization_observationRaw K hm hn p i
    · simpa [P, S, e, criticalObservationField, criticalFieldObservation,
        criticalObservationRecip] using
        criticalArcFibreSourceSpecialization_observationRecip K hm hn p j
  · intro x
    change S (algebraMap K (criticalSourceField K m n) x) =
      e (algebraMap K (criticalObservationField K m n) x)
    rw [S.commutes, e.commutes]
  · intro x y hx hy hxP hyP
    change S (algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n) (⟨x + y, _⟩ : criticalObservationField K m n)) =
      e (⟨x + y, _⟩ : criticalObservationField K m n)
    rw [show (⟨x + y, _⟩ : criticalObservationField K m n) =
        ⟨x, hx⟩ + ⟨y, hy⟩ by rfl, map_add, map_add, map_add, hxP, hyP]
  · intro x hx hxP
    change S (algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n) (⟨x⁻¹, _⟩ : criticalObservationField K m n)) =
      e (⟨x⁻¹, _⟩ : criticalObservationField K m n)
    rw [show (⟨x⁻¹, _⟩ : criticalObservationField K m n) =
        (⟨x, hx⟩ : criticalObservationField K m n)⁻¹ by rfl,
      map_inv₀, map_inv₀, map_inv₀, hxP]
  · intro x y hx hy hxP hyP
    change S (algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n) (⟨x * y, _⟩ : criticalObservationField K m n)) =
      e (⟨x * y, _⟩ : criticalObservationField K m n)
    rw [show (⟨x * y, _⟩ : criticalObservationField K m n) =
        ⟨x, hx⟩ * ⟨y, hy⟩ by rfl, map_mul, map_mul, map_mul, hxP, hyP]

/-- Actual observation-field homomorphism supplied by an exact arc-fibre point. -/
noncomputable def criticalArcFibreToSourceAlgHom
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    letI : Algebra (criticalObservationField K m n) (CriticalArcLaurentField K m n) :=
      criticalObservationArcLaurentFieldAlgebra K hm hn
    CriticalArcFibre K m n →
      (criticalSourceField K m n →ₐ[criticalObservationField K m n]
        CriticalArcLaurentField K m n) := by
  letI : Algebra (criticalObservationField K m n) (CriticalArcLaurentField K m n) :=
    criticalObservationArcLaurentFieldAlgebra K hm hn
  exact fun p ↦
    { toRingHom := (criticalArcFibreSourceSpecialization K hm hn p).toRingHom
      commutes' := criticalArcFibreSourceSpecialization_commutes K hm hn p }

/-- Distinct exact arc-fibre points give distinct actual source-field homomorphisms. -/
theorem criticalArcFibreToSourceAlgHom_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    letI : Algebra (criticalObservationField K m n) (CriticalArcLaurentField K m n) :=
      criticalObservationArcLaurentFieldAlgebra K hm hn
    Function.Injective (criticalArcFibreToSourceAlgHom K hm hn) := by
  letI : Algebra (criticalObservationField K m n) (CriticalArcLaurentField K m n) :=
    criticalObservationArcLaurentFieldAlgebra K hm hn
  intro p q hpq
  apply criticalFibre_fst_injective hm hn
    (coeff_eq_zero_of_dvd_X_pow (X_pow_dvd_criticalArcRawTail K m n) hm)
    (coeff_eq_zero_of_dvd_X_pow (X_pow_dvd_criticalArcReciprocalTail K m n) hn)
  apply Polynomial.ext
  intro k
  by_cases hk : k < m
  · let j : Fin (m + n) := ⟨k, by omega⟩
    have heq := DFunLike.congr_fun hpq (criticalSourceRaw K m n j)
    change criticalArcFibreSourceSpecialization K hm hn p
        (criticalSourceRaw K m n j) =
      criticalArcFibreSourceSpecialization K hm hn q
        (criticalSourceRaw K m n j) at heq
    rw [criticalArcFibreSourceSpecialization_raw,
      criticalArcFibreSourceSpecialization_raw] at heq
    have htail : (criticalArcRawTail K m n).coeff k = 0 :=
      coeff_eq_zero_of_dvd_X_pow (X_pow_dvd_criticalArcRawTail K m n) hk
    simpa [criticalArcFibreRawCoordinate, criticalArcFibreRawPolynomial, j, htail]
      using heq
  · have hpzero : p.1.1.coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero p.1.1 m).mp p.2.1 k
        (Nat.le_of_not_gt hk)
    have hqzero : q.1.1.coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero q.1.1 m).mp q.2.1 k
        (Nat.le_of_not_gt hk)
    rw [hpzero, hqzero]

end

end GaloisForLFunctions.HTGeometry
