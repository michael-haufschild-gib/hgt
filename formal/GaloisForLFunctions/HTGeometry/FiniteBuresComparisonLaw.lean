import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw

/-!
# Bures trace comparison laws

Trace Cauchy--Schwarz bounds and the exact total-source-mass comparison for
the occupied-target Bures incidence invariant.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Trace and occupied-body comparison laws -/

/-- Global trace Cauchy--Schwarz bound for singular positive channels. -/
theorem finiteBuresRootFidelity_sq_le_trace_mul_trace
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity C M ^ 2 ≤ C.trace.re * M.trace.re := by
  have h := finiteBuresRootFidelity_sq_le_reporter_product
    hC hM Matrix.PosDef.one
  simpa [finiteBuresReporterProduct] using h

/-- Identity-reporter leverage is the squared finite Hilbert norm. -/
theorem finiteBuresTargetLeverage_one_eq_inner_self
    {n : ℕ} (v : Fin n → ℂ) :
    finiteBuresTargetLeverage (1 : Matrix (Fin n) (Fin n) ℂ) v =
      (finiteComplexInner v v).re := by
  unfold finiteBuresTargetLeverage finiteComplexInner
  rw [inv_one, Matrix.one_mulVec]
  rfl

/-- A nonempty bounded occupied family of Hilbert-unit vectors has
identity-reporter maximum at most one. -/
theorem finiteBuresOccupiedTargetMaximum_one_le_one
    {n : ℕ} {V : Set (Fin n → ℂ)} (hVne : V.Nonempty)
    (hVunit : ∀ v ∈ V, (finiteComplexInner v v).re ≤ 1) :
    finiteBuresOccupiedTargetMaximum
      (1 : Matrix (Fin n) (Fin n) ℂ) V ≤ 1 := by
  unfold finiteBuresOccupiedTargetMaximum
  apply csSup_le (finiteBuresOccupiedLeverageValueSet_nonempty 1 hVne)
  rintro q ⟨v, hv, rfl⟩
  rw [finiteBuresTargetLeverage_one_eq_inner_self]
  exact hVunit v hv

/-- Product minimax is below the value of every chosen reporter. -/
theorem compactBuresProductCapacity_le_reporter
    {n : ℕ} {source A : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (hA : A.PosDef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    compactBuresProductCapacity source K ≤
      finiteBuresSourcePairing source A * compactBuresTargetMaximum A K := by
  unfold compactBuresProductCapacity
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro q ⟨B, hB, rfl⟩
    exact mul_nonneg
      (finiteBuresSourcePairing_nonneg hsource hB)
      (compactBuresTargetMaximum_nonneg hB hKne hKcompact hKpsd)
  · exact ⟨A, hA, rfl⟩

/-- The Bures complete-incidence invariant never exceeds total source mass
when all occupied targets have Hilbert norm at most one. -/
theorem occupiedTargetBures_dualCapacity_sq_le_trace
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {V : Set (Fin n → ℂ)} (hVne : V.Nonempty)
    (hVbounded : Bornology.IsBounded V)
    (hVunit : ∀ v ∈ V, (finiteComplexInner v v).re ≤ 1) :
    compactBuresDualCapacity source (finiteBuresOccupiedTargetBody V) ^ 2 ≤
      source.trace.re := by
  let K := finiteBuresOccupiedTargetBody V
  have hKne : K.Nonempty := finiteBuresOccupiedTargetBody_nonempty hVne
  have hKcompact : IsCompact K :=
    finiteBuresOccupiedTargetBody_isCompact_of_isBounded hVbounded
  have hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} :=
    finiteBuresOccupiedTargetBody_posSemidef V
  rw [← compactBuresProductCapacity_eq_dualCapacity_sq
    hsource hKne hKcompact (finiteBuresOccupiedTargetBody_convex V) hKpsd]
  calc
    compactBuresProductCapacity source K ≤
        finiteBuresSourcePairing source 1 *
          compactBuresTargetMaximum 1 K :=
      compactBuresProductCapacity_le_reporter
        hsource Matrix.PosDef.one hKne hKcompact hKpsd
    _ = source.trace.re *
        finiteBuresOccupiedTargetMaximum 1 V := by
      rw [compactBuresTargetMaximum_occupiedBody_eq_of_isBounded
        1 hVne hVbounded]
      simp [finiteBuresSourcePairing]
    _ ≤ source.trace.re * 1 := by
      exact mul_le_mul_of_nonneg_left
        (finiteBuresOccupiedTargetMaximum_one_le_one
          hVne hVunit)
        (by
          simpa using
            (finiteMatrix_re_trace_mul_nonneg_of_posSemidef
              hsource Matrix.PosSemidef.one))
    _ = source.trace.re := mul_one _

end

end GaloisForLFunctions.HTGeometry
