import GaloisForLFunctions.HTGeometry.Critical.Schur.JacobianDivisor

/-!
# Reciprocal coordinates on the actual critical source field

The first `m+n` reciprocal coefficients are a second rational coordinate system on the actual
critical source field.  This is the field-theoretic form of the truncated-inversion involution and
will be used to construct the divisor `y_n = 0` symmetrically to the raw divisor `x_m = 0`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section


/-- Reindex the actual reciprocal source coordinates by the same finite type as the raw source
coordinates. -/
noncomputable def criticalSourceRecipReindexed
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n - 1 + 1) → criticalSourceField K m n :=
  fun i => criticalSourceRecip K m n (Fin.cast (by omega) i)

/-- Normalizing the actual reciprocal family retains `y₀=x₀⁻¹` and gives the canonical
reciprocal of the normalized positive raw family in all positive coordinates. -/
theorem criticalSourceNormalizedRecip_eq
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    normalizedFiniteJet (criticalSourceRecipReindexed K hm hn) =
      Fin.cons (criticalSourceScale K hm hn)⁻¹
        (finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change criticalSourceRecip K m n ⟨0, by omega⟩ =
      (criticalSourceScale K hm hn)⁻¹
    have hmul := congrArg (genericJetFieldMap K (m + n))
      (genericRaw_zero_mul_inv K (m + n))
    rw [map_mul, map_one] at hmul
    apply Subtype.ext
    apply eq_inv_of_mul_eq_one_right
    simpa [criticalSourceRecip, criticalSourceScale, criticalSourceRaw,
      criticalAmbientRaw, criticalAmbientRecip, genericRecip] using hmul
  · have hj : (j : ℕ) + 1 < m + n := by omega
    have hs : criticalSourceScale K hm hn ≠ 0 :=
      criticalSourceScale_ne_zero K hm hn
    change criticalSourceRecip K m n ⟨(j : ℕ) + 1, by omega⟩ /
        criticalSourceRecip K m n ⟨0, by omega⟩ =
      finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn) j
    have hq0 : criticalSourceRecip K m n ⟨0, by omega⟩ =
        (criticalSourceScale K hm hn)⁻¹ := by
      have hmul := congrArg (genericJetFieldMap K (m + n))
        (genericRaw_zero_mul_inv K (m + n))
      rw [map_mul, map_one] at hmul
      apply Subtype.ext
      apply eq_inv_of_mul_eq_one_right
      simpa [criticalSourceRecip, criticalSourceScale, criticalSourceRaw,
        criticalAmbientRaw, criticalAmbientRecip, genericRecip] using hmul
    have hcoeff := criticalSourceNormalizedReciprocalPolynomial_coeff K hm hn hj
    rw [criticalSourceReciprocalPolynomial_coeff K m n ((j : ℕ) + 1) hj] at hcoeff
    have hvcoeff :
        (criticalSourceNormalizedReciprocalPolynomial K hm hn).coeff ((j : ℕ) + 1) =
          finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn) j := by
      simpa [criticalSourceNormalizedReciprocalPolynomial] using
        (finiteUnitPolynomial_coeff_succ
          (finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn)) j)
    rw [hq0]
    simp only [div_eq_mul_inv, inv_inv]
    calc
      criticalSourceRecip K m n ⟨(j : ℕ) + 1, by omega⟩ *
          criticalSourceScale K hm hn =
          criticalSourceScale K hm hn *
            criticalSourceRecip K m n ⟨(j : ℕ) + 1, hj⟩ := mul_comm _ _
      _ = (criticalSourceNormalizedReciprocalPolynomial K hm hn).coeff
          ((j : ℕ) + 1) := hcoeff.symm
      _ = finiteReciprocalPositive
          (criticalSourceNormalizedPositive K hm hn) j := hvcoeff

/-- Adjoining an invertible element or its inverse gives the same intermediate field. -/
theorem adjoin_singleton_inv_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (hx : x ≠ 0) :
    IntermediateField.adjoin F ({x⁻¹} : Set E) =
      IntermediateField.adjoin F ({x} : Set E) := by
  apply le_antisymm <;> rw [IntermediateField.adjoin_le_iff]
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (IntermediateField.adjoin F ({x} : Set E)).inv_mem
      (IntermediateField.subset_adjoin F ({x} : Set E) (Set.mem_singleton x))
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h := (IntermediateField.adjoin F ({x⁻¹} : Set E)).inv_mem
      (IntermediateField.subset_adjoin F ({x⁻¹} : Set E) (Set.mem_singleton x⁻¹))
    convert h using 1
    · simp only [inv_inv]
      constructor <;> intro hmem <;> exact hmem

/-- The normalized reciprocal family and normalized raw family generate the same field. -/
theorem adjoin_normalizedCriticalSourceRecip_eq_normalizedRaw
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IntermediateField.adjoin K
        (Set.range (normalizedFiniteJet (criticalSourceRecipReindexed K hm hn))) =
      IntermediateField.adjoin K
        (Set.range (criticalSourceNormalizedRaw K hm hn)) := by
  rw [criticalSourceNormalizedRecip_eq K hm hn]
  have hraw : criticalSourceNormalizedRaw K hm hn =
      Fin.cons (criticalSourceScale K hm hn)
        (criticalSourceNormalizedPositive K hm hn) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  rw [hraw]
  simp only [Fin.range_cons, Set.insert_eq, IntermediateField.adjoin_union,
    Fin.cons_zero]
  rw [adjoin_singleton_inv_eq (criticalSourceScale_ne_zero K hm hn),
    adjoin_finiteReciprocalPositive_eq]

/-- The normalized actual reciprocal coordinates are algebraically independent. -/
theorem algebraicIndependent_normalizedCriticalSourceRecip
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent K
      (normalizedFiniteJet (criticalSourceRecipReindexed K hm hn)) :=
  algebraicIndependent_of_adjoin_eq_of_finite
    (criticalSourceNormalizedRaw K hm hn)
    (normalizedFiniteJet (criticalSourceRecipReindexed K hm hn))
    (algebraicIndependent_criticalSourceNormalizedRaw K hm hn)
    (adjoin_normalizedCriticalSourceRecip_eq_normalizedRaw K hm hn).symm

/-- The reciprocal constant coordinate is nonzero. -/
theorem criticalSourceRecipReindexed_zero_ne
    (K : Type*) [Field K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceRecipReindexed K hm hn 0 ≠ 0 := by
  have hraw : criticalSourceRaw K m n ⟨0, by omega⟩ ≠ 0 := by
    intro hx
    exact ((algebraicIndependent_criticalSourceRaw K m n).transcendental
      ⟨0, by omega⟩) (hx ▸ isAlgebraic_zero)
  have hmul := congrArg (genericJetFieldMap K (m + n))
    (genericRaw_zero_mul_inv K (m + n))
  rw [map_mul, map_one] at hmul
  have hq0 : criticalSourceRecipReindexed K hm hn 0 =
      (criticalSourceRaw K m n ⟨0, by omega⟩)⁻¹ := by
    apply Subtype.ext
    apply eq_inv_of_mul_eq_one_right
    simpa [criticalSourceRecipReindexed, criticalSourceRecip, criticalSourceRaw,
      criticalAmbientRaw, criticalAmbientRecip, genericRecip] using hmul
  rw [hq0]
  exact inv_ne_zero hraw

/-- The actual reciprocal source coordinates are algebraically independent. -/
theorem algebraicIndependent_criticalSourceRecip
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent K (criticalSourceRecipReindexed K hm hn) := by
  apply algebraicIndependent_of_adjoin_eq_of_finite
    (normalizedFiniteJet (criticalSourceRecipReindexed K hm hn))
    (criticalSourceRecipReindexed K hm hn)
    (algebraicIndependent_normalizedCriticalSourceRecip K hm hn)
  exact (adjoin_normalizedFiniteJet_eq
    (F := K) (E := criticalSourceField K m n)
    (criticalSourceRecipReindexed K hm hn)
    (criticalSourceRecipReindexed_zero_ne K hm hn)).symm

/-- The actual reciprocal coordinates generate the whole source field. -/
theorem criticalSourceRecip_adjoin_ground_eq_top
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IntermediateField.adjoin K (Set.range (criticalSourceRecipReindexed K hm hn)) = ⊤ := by
  rw [adjoin_normalizedFiniteJet_eq
      (criticalSourceRecipReindexed K hm hn)
      (criticalSourceRecipReindexed_zero_ne K hm hn),
    adjoin_normalizedCriticalSourceRecip_eq_normalizedRaw K hm hn]
  rw [criticalSourceNormalizedRaw,
    ← adjoin_normalizedFiniteJet_eq (criticalSourceRawReindexed K hm hn)
      (criticalSourceRawReindexed_zero_ne K hm hn)]
  have hrange : Set.range (criticalSourceRawReindexed K hm hn) =
      Set.range (criticalSourceRaw K m n) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨Fin.cast (by omega) i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨Fin.cast (by omega) i, by simp [criticalSourceRawReindexed]⟩
  rw [hrange, criticalSourceRaw_adjoin_ground_eq_top]

/-- Rational presentation of the actual source field by its reciprocal coordinates. -/
noncomputable def criticalSourceRecipFieldEquiv
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    FractionRing (MvPolynomial (Fin (m + n - 1 + 1)) K) ≃ₐ[K]
      criticalSourceField K m n := by
  exact (algebraicIndependent_criticalSourceRecip K hm hn).aevalEquivField.trans
    ((IntermediateField.equivOfEq
      (criticalSourceRecip_adjoin_ground_eq_top K hm hn)).trans
        (IntermediateField.topEquiv :
          (⊤ : IntermediateField K (criticalSourceField K m n)) ≃ₐ[K]
            criticalSourceField K m n))

end

end GaloisForLFunctions.HTGeometry
