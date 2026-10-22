import GaloisForLFunctions.HTGeometry.Critical.Observation.Field
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem
import GaloisForLFunctions.HTGeometry.SchurCofactorLocus

/-!
# Schur coordinates on the actual critical source field

Normalize the actual raw jet by its nonzero constant coefficient, invert the resulting unit jet,
and square it.  The positive coefficients of that reciprocal square are triangular coordinates.
Together with the original constant coefficient they form a transcendence basis of the actual
critical source field.  In these coordinates the ramification determinant is the irreducible
rectangular-Schur polynomial, with one unused scale coordinate in front.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000

/-- The actual raw source generators are algebraically independent inside the source field. -/
theorem algebraicIndependent_criticalSourceRaw
    (K : Type*) [Field K] (m n : ℕ) :
    AlgebraicIndependent K (criticalSourceRaw K m n) := by
  apply AlgebraicIndependent.of_comp
    ((criticalSourceField K m n).val : criticalSourceField K m n →ₐ[K]
      genericJetField K (m + n))
  convert algebraicIndependent_criticalAmbientRaw K m n using 1
  funext j
  rfl

/-- The actual raw source generators generate the whole source field over the ground field. -/
theorem criticalSourceRaw_adjoin_ground_eq_top
    (K : Type*) [Field K] (m n : ℕ) :
    IntermediateField.adjoin K (Set.range (criticalSourceRaw K m n)) = ⊤ := by
  let J := IntermediateField.adjoin K (Set.range (criticalSourceRaw K m n))
  apply top_unique
  intro b _
  have hb : (b : genericJetField K (m + n)) ∈
      IntermediateField.adjoin K
        (Set.range (fun j : Fin (m + n) => criticalAmbientRaw K m n (j : ℕ))) := by
    simpa [criticalSourceField] using b.property
  let p : ∀ z, z ∈ IntermediateField.adjoin K
      (Set.range (fun j : Fin (m + n) => criticalAmbientRaw K m n (j : ℕ))) → Prop :=
    fun z hz => (⟨z, by simpa [criticalSourceField] using hz⟩ :
      criticalSourceField K m n) ∈ J
  change p (b : genericJetField K (m + n)) hb
  refine IntermediateField.adjoin_induction K (p := p) ?_ ?_ ?_ ?_ ?_ hb
  · intro z hz
    obtain ⟨j, rfl⟩ := hz
    simpa [p, J, criticalSourceRaw] using
      (IntermediateField.subset_adjoin K (Set.range (criticalSourceRaw K m n))
        (Set.mem_range_self j))
  · intro z
    simp [p, J]
  · intro z w hz hw hzJ hwJ
    simpa only [p, Subtype.coe_eta] using! J.add_mem hzJ hwJ
  · intro z hz hzJ
    simpa only [p, Subtype.coe_eta] using! J.inv_mem hzJ
  · intro z w hz hw hzJ hwJ
    simpa only [p, Subtype.coe_eta] using! J.mul_mem hzJ hwJ

/-- Reindex the raw family as one scale coordinate followed by `m+n-1` positive coordinates. -/
noncomputable def criticalSourceRawReindexed
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n - 1 + 1) → criticalSourceField K m n :=
  fun i => criticalSourceRaw K m n (Fin.cast (by omega) i)

theorem algebraicIndependent_criticalSourceRawReindexed
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent K (criticalSourceRawReindexed K hm hn) := by
  exact (algebraicIndependent_criticalSourceRaw K m n).comp
    (Fin.cast (by omega)) (Fin.cast_injective (by omega))

theorem criticalSourceRawReindexed_zero_ne
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceRawReindexed K hm hn 0 ≠ 0 := by
  intro hzero
  exact ((algebraicIndependent_criticalSourceRawReindexed K hm hn).transcendental 0)
    (hzero ▸ isAlgebraic_zero)

/-- Scale-normalized raw coordinates, retaining the original scale in coordinate zero. -/
noncomputable def criticalSourceNormalizedRaw
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n - 1 + 1) → criticalSourceField K m n :=
  normalizedFiniteJet (criticalSourceRawReindexed K hm hn)

/-- Positive normalized raw coordinates. -/
noncomputable def criticalSourceNormalizedPositive
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n - 1) → criticalSourceField K m n :=
  normalizedPositiveFiniteJet (criticalSourceRawReindexed K hm hn)

theorem algebraicIndependent_criticalSourceNormalizedRaw
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent K (criticalSourceNormalizedRaw K hm hn) :=
  normalizedFiniteJet_algebraicIndependent
    (criticalSourceRawReindexed K hm hn)
    (algebraicIndependent_criticalSourceRawReindexed K hm hn)
    (criticalSourceRawReindexed_zero_ne K hm hn)

/-- Positive reciprocal-square coordinates of the normalized actual raw jet. -/
noncomputable def criticalSourceReciprocalSquarePositive
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n - 1) → criticalSourceField K m n :=
  finiteReciprocalSquarePositive (criticalSourceNormalizedPositive K hm hn)

/-- The reciprocal-square coordinates in the reversed order used by `schurVar`. -/
noncomputable def criticalSourceReciprocalSquareReversed
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n - 1) → criticalSourceField K m n :=
  fun i => criticalSourceReciprocalSquarePositive K hm hn i.rev

/-- Full Schur coordinate family: source scale followed by normalized reciprocal-square data. -/
noncomputable def criticalSourceSchurCoordinates
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
  Fin (m + n - 1 + 1) → criticalSourceField K m n :=
  Fin.cons (criticalSourceNormalizedRaw K hm hn 0)
    (criticalSourceReciprocalSquareReversed K hm hn)

theorem adjoin_criticalSourceSchurCoordinates_eq_normalizedRaw
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IntermediateField.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) =
      IntermediateField.adjoin K (Set.range (criticalSourceNormalizedRaw K hm hn)) := by
  let u := criticalSourceNormalizedPositive K hm hn
  let v := finiteReciprocalPositive u
  let z := finiteUnitSquarePositive v
  let zr : Fin (m + n - 1) → criticalSourceField K m n := fun i => z i.rev
  have hzv : IntermediateField.adjoin K (Set.range z) =
      IntermediateField.adjoin K (Set.range v) :=
    adjoin_finiteUnitSquarePositive_eq v
  have hvu : IntermediateField.adjoin K (Set.range v) =
      IntermediateField.adjoin K (Set.range u) :=
    adjoin_finiteReciprocalPositive_eq u
  have hzu : IntermediateField.adjoin K (Set.range z) =
      IntermediateField.adjoin K (Set.range u) := hzv.trans hvu
  have hrange : Set.range zr = Set.range z := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, by simp [zr]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, by simp [zr]⟩
  have hzru : IntermediateField.adjoin K (Set.range zr) =
      IntermediateField.adjoin K (Set.range u) := by rw [hrange, hzu]
  have hnorm : criticalSourceNormalizedRaw K hm hn =
      Fin.cons (criticalSourceNormalizedRaw K hm hn 0) u := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  change IntermediateField.adjoin K
      (Set.range (Fin.cons (criticalSourceNormalizedRaw K hm hn 0) zr)) =
    IntermediateField.adjoin K (Set.range (criticalSourceNormalizedRaw K hm hn))
  rw [hnorm]
  simp only [Fin.range_cons, Set.insert_eq, IntermediateField.adjoin_union, Fin.cons_zero]
  exact congrArg
    (fun J : IntermediateField K (criticalSourceField K m n) =>
      IntermediateField.adjoin K {criticalSourceNormalizedRaw K hm hn 0} ⊔ J) hzru

theorem algebraicIndependent_criticalSourceSchurCoordinates
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent K (criticalSourceSchurCoordinates K hm hn) :=
  algebraicIndependent_of_adjoin_eq_of_finite
    (criticalSourceNormalizedRaw K hm hn)
    (criticalSourceSchurCoordinates K hm hn)
    (algebraicIndependent_criticalSourceNormalizedRaw K hm hn)
    (adjoin_criticalSourceSchurCoordinates_eq_normalizedRaw K hm hn).symm

theorem criticalSourceSchurCoordinates_adjoin_eq_top
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IntermediateField.adjoin K (Set.range (criticalSourceSchurCoordinates K hm hn)) = ⊤ := by
  rw [adjoin_criticalSourceSchurCoordinates_eq_normalizedRaw K hm hn,
    criticalSourceNormalizedRaw,
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

/-- Rational presentation of the actual source field by scale plus Schur coordinates. -/
noncomputable def criticalSourceSchurFieldEquiv
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    FractionRing (MvPolynomial (Fin (m + n - 1 + 1)) K) ≃ₐ[K]
      criticalSourceField K m n := by
  exact (algebraicIndependent_criticalSourceSchurCoordinates K hm hn).aevalEquivField.trans
    ((IntermediateField.equivOfEq
      (criticalSourceSchurCoordinates_adjoin_eq_top K hm hn)).trans
        (IntermediateField.topEquiv :
          (⊤ : IntermediateField K (criticalSourceField K m n)) ≃ₐ[K]
            criticalSourceField K m n))

/-- Rectangular-Schur ramification polynomial with the scale coordinate inserted in front. -/
noncomputable def criticalSourceSchurRamificationPolynomial
    (K : Type*) [Field K] (m n : ℕ) :
    MvPolynomial (Fin (m + n - 1 + 1)) K :=
  MvPolynomial.rename Fin.succ
    ((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).det)

/-- The actual source ramification polynomial is irreducible in Schur coordinates. -/
theorem irreducible_criticalSourceSchurRamificationPolynomial
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Irreducible (criticalSourceSchurRamificationPolynomial K m n) := by
  classical
  apply irreducible_rename_succ
  have hL : n + m - 1 = m + n - 1 := by omega
  rw [← rename_finCongr_det_rectangularSchurToeplitz (K := K) hL n m]
  exact (irreducible_rename_finCongr hL _).2
    (irreducible_det_rectangularSchurToeplitz (K := K) hn hm)

/-- Evaluating the source ramification polynomial discards the scale coordinate and gives the
rectangular-Schur determinant of the actual normalized reciprocal square. -/
theorem aeval_criticalSourceSchurRamificationPolynomial
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn)
        (criticalSourceSchurRamificationPolynomial K m n) =
      (rectangularSchurToeplitz
        (unitConstantSeries (criticalSourceReciprocalSquarePositive K hm hn)) n m).det := by
  let z := criticalSourceReciprocalSquarePositive K hm hn
  let zr := criticalSourceReciprocalSquareReversed K hm hn
  have htail : criticalSourceSchurCoordinates K hm hn ∘ Fin.succ = zr := by
    funext i
    simp [criticalSourceSchurCoordinates, zr]
  rw [criticalSourceSchurRamificationPolynomial, MvPolynomial.aeval_rename, htail]
  let φ : MvPolynomial (Fin (m + n - 1)) K →ₐ[K]
      criticalSourceField K m n := MvPolynomial.aeval zr
  have hmatrix :
      (rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).map φ =
        rectangularSchurToeplitz (unitConstantSeries z) n m := by
    apply Matrix.ext
    intro i j
    rw [Matrix.map_apply]
    change φ (rectangularSchurToeplitz (schurVar K (m + n - 1)) n m i j) =
      rectangularSchurToeplitz (unitConstantSeries z) n m i j
    simp only [rectangularSchurToeplitz]
    by_cases hij : (j : ℕ) ≤ n + (i : ℕ)
    · rw [if_pos hij, if_pos hij]
      rcases hindex : n + (i : ℕ) - (j : ℕ) with _ | k
      · simp [φ, schurVar, unitConstantSeries]
      · have hk : k < m + n - 1 := by
          have hi := i.isLt
          omega
        rw [schurVar, if_neg (by omega : k + 1 ≠ 0), dif_pos (by omega)]
        rw [unitConstantSeries_succ z hk]
        simp only [φ, MvPolynomial.aeval_X, zr,
          criticalSourceReciprocalSquareReversed, z]
        congr 1
        apply Fin.ext
        simp
        omega
    · rw [if_neg hij, if_neg hij, map_zero]
  calc
    φ ((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).det) =
        ((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).map φ).det :=
      φ.map_det _
    _ = (rectangularSchurToeplitz (unitConstantSeries z) n m).det := by rw [hmatrix]

end

end GaloisForLFunctions.HTGeometry
