import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw

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

/-- Finite Bures root fidelity is symmetric on positive semidefinite
matrices. -/
theorem finiteBuresRootFidelity_comm
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity C M = finiteBuresRootFidelity M C := by
  exact finiteBuresTrace_comm hC hM

/-- Root fidelity is homogeneous of degree one half in its source. -/
theorem finiteBuresRootFidelity_smul_left
    {n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity (r • C) M =
      Real.sqrt r * finiteBuresRootFidelity C M := by
  exact finiteBuresTrace_smul_left r hr hC hM

/-- Squared fidelity is linear in nonnegative source mass. -/
theorem finiteBuresRootFidelity_sq_smul_left
    {n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity (r • C) M ^ 2 =
      r * finiteBuresRootFidelity C M ^ 2 := by
  exact finiteBuresTrace_sq_smul_left r hr hC hM

/-- Self-fidelity of a positive covariance is its trace. -/
theorem finiteBuresRootFidelity_self_eq_trace
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) :
    finiteBuresRootFidelity C C = C.trace.re := by
  exact finiteBuresTrace_self_eq_trace hC

/-! ## Compact Bures distance -/

/-- Bures distance between finite positive operators, in the normalization
used by the paper.  On density operators its radicand lies in `[0,2]`. -/
def finiteBuresDistance {n : ℕ}
    (C M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (2 * (1 - finiteBuresRootFidelity C M))

/-- Distance values attained on a target body. -/
def compactBuresDistanceValueSet {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {d | ∃ M ∈ K, d = finiteBuresDistance source M}

/-- Minimum Bures distance from a finite source to a target body. -/
def compactBuresDistance {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sInf (compactBuresDistanceValueSet source K)

theorem continuousOn_finiteBuresDistance_right
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ) :
    ContinuousOn (finiteBuresDistance source)
      {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} := by
  unfold finiteBuresDistance
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul
      (continuousOn_const.sub
        (continuousOn_finiteBuresRootFidelity_right source)))

/-- Root fidelity attains its compact-target supremum. -/
theorem exists_compactBuresRootFidelity_eq_dualCapacity
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    ∃ M ∈ K, compactBuresDualCapacity source K =
      finiteBuresRootFidelity source M := by
  have hcont := (continuousOn_finiteBuresRootFidelity_right source).mono hKpsd
  obtain ⟨M, hM, hmax⟩ := hKcompact.exists_isMaxOn hKne hcont
  refine ⟨M, hM, ?_⟩
  have hlub : IsLUB (compactBuresDualValueSet source K)
      (finiteBuresRootFidelity source M) := by
    have hraw := hmax.isLUB hM
    simpa [compactBuresDualValueSet, eq_comm] using hraw
  unfold compactBuresDualCapacity
  exact (isLUB_csSup (compactBuresDualValueSet_nonempty source hKne)
    (compactBuresDualValueSet_bddAbove source hKcompact hKpsd)).unique hlub

theorem compactBuresDistanceValueSet_nonempty
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hKne : K.Nonempty) :
    (compactBuresDistanceValueSet source K).Nonempty := by
  obtain ⟨M, hM⟩ := hKne
  exact ⟨finiteBuresDistance source M, M, hM, rfl⟩

theorem compactBuresDistanceValueSet_bddBelow
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) :
    BddBelow (compactBuresDistanceValueSet source K) := by
  refine ⟨0, ?_⟩
  rintro d ⟨M, hM, rfl⟩
  exact Real.sqrt_nonneg _

/-- Compact Bures distance is a genuine minimum. -/
theorem exists_compactBuresDistance_eq_distance
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    ∃ M ∈ K, compactBuresDistance source K =
      finiteBuresDistance source M := by
  have hcont := (continuousOn_finiteBuresDistance_right source).mono hKpsd
  obtain ⟨M, hM, hmin⟩ := hKcompact.exists_isMinOn hKne hcont
  refine ⟨M, hM, ?_⟩
  have hglb : IsGLB (compactBuresDistanceValueSet source K)
      (finiteBuresDistance source M) := by
    have hraw := hmin.isGLB hM
    simpa [compactBuresDistanceValueSet, eq_comm] using hraw
  unfold compactBuresDistance
  exact (isGLB_csInf
    (compactBuresDistanceValueSet_nonempty source hKne)
    (compactBuresDistanceValueSet_bddBelow source K)).unique hglb

/-- The same target simultaneously maximizes fidelity and minimizes Bures
distance.  This identifies the paper's minimum distance with its dual
capacity without making distance definitional. -/
theorem compactBuresDistance_eq_sqrt_one_sub_dualCapacity
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    compactBuresDistance source K =
      Real.sqrt (2 * (1 - compactBuresDualCapacity source K)) := by
  have hcont := (continuousOn_finiteBuresRootFidelity_right source).mono hKpsd
  obtain ⟨M, hM, hmax⟩ := hKcompact.exists_isMaxOn hKne hcont
  have hcap : compactBuresDualCapacity source K =
      finiteBuresRootFidelity source M := by
    have hlub : IsLUB (compactBuresDualValueSet source K)
        (finiteBuresRootFidelity source M) := by
      simpa [compactBuresDualValueSet, eq_comm] using hmax.isLUB hM
    exact (isLUB_csSup (compactBuresDualValueSet_nonempty source hKne)
      (compactBuresDualValueSet_bddAbove source hKcompact hKpsd)).unique hlub
  have hmin : IsMinOn (finiteBuresDistance source) K M := by
    intro N hN
    unfold finiteBuresDistance
    apply Real.sqrt_le_sqrt
    have hle := hmax hN
    change finiteBuresRootFidelity source N ≤
      finiteBuresRootFidelity source M at hle
    linarith
  have hdist : compactBuresDistance source K =
      finiteBuresDistance source M := by
    have hglb : IsGLB (compactBuresDistanceValueSet source K)
        (finiteBuresDistance source M) := by
      simpa [compactBuresDistanceValueSet, eq_comm] using hmin.isGLB hM
    exact (isGLB_csInf
      (compactBuresDistanceValueSet_nonempty source hKne)
      (compactBuresDistanceValueSet_bddBelow source K)).unique hglb
  rw [hdist, hcap]
  rfl

/-- Compact-target root capacity inherits exact square-root homogeneity from
pointwise fidelity. -/
theorem compactBuresDualCapacity_smul_left
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (r : ℝ) (hr : 0 ≤ r)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    compactBuresDualCapacity (r • source) K =
      Real.sqrt r * compactBuresDualCapacity source K := by
  obtain ⟨Mr, hMr, hcapr⟩ :=
    exists_compactBuresRootFidelity_eq_dualCapacity
      (r • source) hKne hKcompact hKpsd
  obtain ⟨M, hM, hcap⟩ :=
    exists_compactBuresRootFidelity_eq_dualCapacity
      source hKne hKcompact hKpsd
  have hMrle : finiteBuresRootFidelity source Mr ≤
      compactBuresDualCapacity source K := by
    unfold compactBuresDualCapacity
    exact le_csSup
      (compactBuresDualValueSet_bddAbove source hKcompact hKpsd)
      ⟨Mr, hMr, rfl⟩
  have hMle : finiteBuresRootFidelity (r • source) M ≤
      compactBuresDualCapacity (r • source) K := by
    unfold compactBuresDualCapacity
    exact le_csSup
      (compactBuresDualValueSet_bddAbove (r • source) hKcompact hKpsd)
      ⟨M, hM, rfl⟩
  apply le_antisymm
  · rw [hcapr,
      finiteBuresRootFidelity_smul_left r hr hsource (hKpsd hMr)]
    exact mul_le_mul_of_nonneg_left hMrle (Real.sqrt_nonneg r)
  · rw [hcap,
      ← finiteBuresRootFidelity_smul_left r hr hsource (hKpsd hM)]
    exact hMle

/-- Fidelity capacity between density operators is at most one. -/
theorem compactBuresDualCapacity_le_one
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (hsourceTrace : source.trace.re = 1)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef})
    (hKtrace : ∀ M ∈ K, M.trace.re = 1) :
    compactBuresDualCapacity source K ≤ 1 := by
  obtain ⟨M, hM, hcap⟩ :=
    exists_compactBuresRootFidelity_eq_dualCapacity
      source hKne hKcompact hKpsd
  rw [hcap]
  have hsq := finiteBuresRootFidelity_sq_le_trace_mul_trace
    hsource (hKpsd hM)
  rw [hsourceTrace, hKtrace M hM, one_mul] at hsq
  have hnonneg :=
    finiteBuresRootFidelity_nonneg (C := source) (hKpsd hM)
  nlinarith

/-- Squared minimum Bures distance is exactly twice the missing compact
fidelity capacity. -/
theorem compactBuresDistance_sq_eq_two_mul_one_sub_capacity
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (hsourceTrace : source.trace.re = 1)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef})
    (hKtrace : ∀ M ∈ K, M.trace.re = 1) :
    compactBuresDistance source K ^ 2 =
      2 * (1 - compactBuresDualCapacity source K) := by
  rw [compactBuresDistance_eq_sqrt_one_sub_dualCapacity
    source hKne hKcompact hKpsd]
  apply Real.sq_sqrt
  have hcap := compactBuresDualCapacity_le_one hsource hsourceTrace
    hKne hKcompact hKpsd hKtrace
  linarith

/-- Trace of an occupied rank-one ray is its Hilbert mass. -/
theorem finiteBuresTargetRay_trace_re_eq_inner_self
    {n : ℕ} (v : Fin n → ℂ) :
    (finiteBuresTargetRay v).trace.re = (finiteComplexInner v v).re := by
  rw [finiteBuresTargetRay, Matrix.trace_vecMulVec, dotProduct_comm]
  rfl

theorem convex_finiteBuresTraceReal_eq_one {n : ℕ} :
    Convex ℝ {M : Matrix (Fin n) (Fin n) ℂ | M.trace.re = 1} := by
  intro M hM N hN a b ha hb hab
  simp only [Set.mem_setOf_eq] at hM hN ⊢
  simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.smul_re, smul_eq_mul]
  rw [hM, hN]
  linarith

theorem isClosed_finiteBuresTraceReal_eq_one {n : ℕ} :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.trace.re = 1} := by
  have hcont : Continuous
      (fun M : Matrix (Fin n) (Fin n) ℂ => M.trace.re) := by
    unfold Matrix.trace
    fun_prop
  exact isClosed_eq hcont continuous_const

/-- Closed convex hull of Hilbert-unit occupied rays consists entirely of
density operators. -/
theorem finiteBuresOccupiedTargetBody_trace_eq_one
    {n : ℕ} {V : Set (Fin n → ℂ)}
    (hVunit : ∀ v ∈ V, (finiteComplexInner v v).re = 1) :
    ∀ M ∈ finiteBuresOccupiedTargetBody V, M.trace.re = 1 := by
  have hrays : finiteBuresTargetRay '' V ⊆
      {M : Matrix (Fin n) (Fin n) ℂ | M.trace.re = 1} := by
    rintro M ⟨v, hv, rfl⟩
    change (finiteBuresTargetRay v).trace.re = 1
    rw [finiteBuresTargetRay_trace_re_eq_inner_self, hVunit v hv]
  exact closedConvexHull_min hrays convex_finiteBuresTraceReal_eq_one
    isClosed_finiteBuresTraceReal_eq_one

/-- Unit-trace normalization of a nonzero positive source. -/
def finiteBuresNormalizedSource {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (source.trace.re)⁻¹ • source

theorem finiteBuresNormalizedSource_posSemidef
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (htrace : 0 < source.trace.re) :
    (finiteBuresNormalizedSource source).PosSemidef := by
  exact hsource.smul (inv_nonneg.mpr htrace.le)

theorem finiteBuresNormalizedSource_trace_eq_one
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (htrace : 0 < source.trace.re) :
    (finiteBuresNormalizedSource source).trace.re = 1 := by
  simp [finiteBuresNormalizedSource, Matrix.trace_smul,
    inv_mul_cancel₀ htrace.ne']

theorem finiteBuresTrace_smul_normalizedSource
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (htrace : 0 < source.trace.re) :
    source.trace.re • finiteBuresNormalizedSource source = source := by
  simp [finiteBuresNormalizedSource, smul_smul,
    mul_inv_cancel₀ htrace.ne']

/-- **Exact occupied-body Bures distance identity `(12)`.**  For every
nonzero positive source and every nonempty bounded family of Hilbert-unit
occupied targets, maximum squared incidence equals total source mass times
the squared Bures-distance deficit from the complete closed convex target
body. -/
theorem occupiedTargetBures_distance_identity
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (htrace : 0 < source.trace.re)
    {V : Set (Fin n → ℂ)} (hVne : V.Nonempty)
    (hVbounded : Bornology.IsBounded V)
    (hVunit : ∀ v ∈ V, (finiteComplexInner v v).re = 1) :
    compactBuresDualCapacity source (finiteBuresOccupiedTargetBody V) ^ 2 =
      source.trace.re *
        (1 - compactBuresDistance
          (finiteBuresNormalizedSource source)
          (finiteBuresOccupiedTargetBody V) ^ 2 / 2) ^ 2 := by
  let rho := finiteBuresNormalizedSource source
  let K := finiteBuresOccupiedTargetBody V
  have hrho : rho.PosSemidef :=
    finiteBuresNormalizedSource_posSemidef hsource htrace
  have hrhotrace : rho.trace.re = 1 :=
    finiteBuresNormalizedSource_trace_eq_one htrace
  have hKne : K.Nonempty := finiteBuresOccupiedTargetBody_nonempty hVne
  have hKcompact : IsCompact K :=
    finiteBuresOccupiedTargetBody_isCompact_of_isBounded hVbounded
  have hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} :=
    finiteBuresOccupiedTargetBody_posSemidef V
  have hKtrace : ∀ M ∈ K, M.trace.re = 1 :=
    finiteBuresOccupiedTargetBody_trace_eq_one hVunit
  have hdist := compactBuresDistance_sq_eq_two_mul_one_sub_capacity
    hrho hrhotrace hKne hKcompact hKpsd hKtrace
  have hcap : compactBuresDualCapacity rho K =
      1 - compactBuresDistance rho K ^ 2 / 2 := by
    linarith
  have hscale : compactBuresDualCapacity source K =
      Real.sqrt source.trace.re * compactBuresDualCapacity rho K := by
    rw [← finiteBuresTrace_smul_normalizedSource htrace]
    exact compactBuresDualCapacity_smul_left hrho source.trace.re
      htrace.le hKne hKcompact hKpsd
  change compactBuresDualCapacity source K ^ 2 =
    source.trace.re * (1 - compactBuresDistance rho K ^ 2 / 2) ^ 2
  rw [hscale, hcap, mul_pow, Real.sq_sqrt htrace.le]

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
