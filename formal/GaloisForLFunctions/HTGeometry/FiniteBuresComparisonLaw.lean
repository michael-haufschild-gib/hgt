import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Bures trace comparison laws

Trace Cauchy--Schwarz bounds and the exact total-source-mass comparison for
the occupied-target Bures incidence invariant.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Trace and occupied-body comparison laws -/

/-- Global trace Cauchy--Schwarz bound for singular positive channels. -/
theorem finiteBuresRootFidelity_sq_le_trace_mul_trace
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity C M ^ (2 : ℕ) ≤ C.trace.re * M.trace.re := by
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
    finiteBuresRootFidelity (r • C) M ^ (2 : ℕ) =
      r * finiteBuresRootFidelity C M ^ (2 : ℕ) := by
  exact finiteBuresTrace_sq_smul_left r hr hC hM

/-- Self-fidelity of a positive covariance is its trace. -/
theorem finiteBuresRootFidelity_self_eq_trace
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) :
    finiteBuresRootFidelity C C = C.trace.re := by
  exact finiteBuresTrace_self_eq_trace hC

/-! ## Density-operator saturation rigidity -/

/-- Real trace is a continuous real-linear functional on finite matrices. -/
noncomputable def finiteMatrixTraceRealCLM {n : ℕ} :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.trace.re
      map_add' := by
        intro A B
        simp
      map_smul' := by
        intro r A
        simp [Matrix.trace_smul] }

/-- Derivative of the opposite exponential-tilt Alberti objective at the
unperturbed reporter. -/
theorem hasDerivAt_finiteBuresExpHalfSum
    {n : ℕ} [Nonempty (Fin n)]
    (C M D : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt
      (fun t : ℝ ↦ (1 / 2 : ℝ) *
        ((C * NormedSpace.exp (t • D)).trace.re +
          (M * NormedSpace.exp (t • (-D))).trace.re))
      ((1 / 2 : ℝ) * ((C * D).trace.re + (M * (-D)).trace.re)) 0 := by
  have hexp : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • D)) D 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) D (0 : ℝ)
  have hneg : HasDerivAt
      (fun t : ℝ ↦ NormedSpace.exp (t • (-D))) (-D) 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-D) (0 : ℝ)
  have hCmat : HasDerivAt
      (fun t : ℝ ↦ C * NormedSpace.exp (t • D)) (C * D) 0 :=
    hexp.const_mul C
  have hMmat : HasDerivAt
      (fun t : ℝ ↦ M * NormedSpace.exp (t • (-D))) (M * (-D)) 0 :=
    hneg.const_mul M
  have hCtrace : HasDerivAt
      (fun t : ℝ ↦ (C * NormedSpace.exp (t • D)).trace.re)
      (C * D).trace.re 0 :=
    (finiteMatrixTraceRealCLM (n := n)).hasFDerivAt.comp_hasDerivAt 0 hCmat
  have hMtrace : HasDerivAt
      (fun t : ℝ ↦ (M * NormedSpace.exp (t • (-D))).trace.re)
      (M * (-D)).trace.re 0 :=
    (finiteMatrixTraceRealCLM (n := n)).hasFDerivAt.comp_hasDerivAt 0 hMmat
  exact (hCtrace.add hMtrace).const_mul (1 / 2 : ℝ)

/-- Along the source-to-target Hermitian direction, the Alberti derivative
is minus the squared Hilbert--Schmidt separation. -/
theorem finiteBuresExpHalfSum_derivative_eq_neg_hilbertSchmidtSq
    {n : ℕ} (C M : Matrix (Fin n) (Fin n) ℂ)
    (hC : C.IsHermitian) (hM : M.IsHermitian) :
    (C * (M - C)).trace.re + (M * (-(M - C))).trace.re =
      -finiteMatrixHilbertSchmidtSq (M - C) := by
  let D : Matrix (Fin n) (Fin n) ℂ := M - C
  have hD : D.IsHermitian := hM.sub hC
  have hmat : C * D + M * (-D) = -(D * D) := by
    dsimp [D]
    noncomm_ring
  calc
    (C * (M - C)).trace.re + (M * (-(M - C))).trace.re =
        (C * D).trace.re + (M * (-D)).trace.re := by rfl
    _ = ((C * D + M * (-D)).trace).re := by simp
    _ = ((-(D * D)).trace).re := by rw [hmat]
    _ = -((D * D).trace).re := by simp
    _ = -finiteMatrixHilbertSchmidtSq D := by
      unfold finiteMatrixHilbertSchmidtSq
      rw [hD.eq]
    _ = -finiteMatrixHilbertSchmidtSq (M - C) := by rfl

/-- Hilbert--Schmidt mass is strictly positive off the zero matrix. -/
theorem finiteMatrixHilbertSchmidtSq_pos_of_ne_zero
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) (hK : K ≠ 0) :
    0 < finiteMatrixHilbertSchmidtSq K := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  have hentry : ∃ i j, K i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hK
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hentry
  apply Finset.sum_pos'
  · intro i' _
    exact Finset.sum_nonneg fun j' _ ↦ sq_nonneg ‖K i' j'‖
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.sum_pos'
    · intro j' _
      exact sq_nonneg ‖K i j'‖
    · exact ⟨j, Finset.mem_univ j, sq_pos_of_pos (norm_pos_iff.mpr hij)⟩

/-- A negative derivative gives strict descent at a positive nearby time. -/
theorem exists_right_lt_of_hasDerivAt_neg
    {f : ℝ → ℝ} {f' : ℝ} (h : HasDerivAt f f' 0) (hf' : f' < 0) :
    ∃ t : ℝ, 0 < t ∧ f t < f 0 := by
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (f t - f 0) < 0 := by
    simpa [smul_eq_mul] using
      h.tendsto_slope_zero_right.eventually (eventually_lt_nhds hf')
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htSlope, ht⟩ := (hslope.and hpos).exists
  refine ⟨t, ht, ?_⟩
  rcases (mul_neg_iff.mp htSlope) with hgood | hbad
  · linarith
  · exact False.elim ((not_lt_of_ge (inv_nonneg.mpr ht.le)) hbad.1)

/-- **Strict fidelity rigidity.**  Unit-trace positive matrices have root
fidelity one only when they are the same state.  The proof constructs a
strictly improving positive reporter whenever the states differ. -/
theorem finiteBuresRootFidelity_eq_one_implies_eq
    {n : ℕ} [Nonempty (Fin n)]
    {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef)
    (hCtrace : C.trace.re = 1) (hMtrace : M.trace.re = 1)
    (hfid : finiteBuresRootFidelity C M = 1) :
    C = M := by
  by_contra hne
  let D : Matrix (Fin n) (Fin n) ℂ := M - C
  have hD : D.IsHermitian := hM.isHermitian.sub hC.isHermitian
  have hDne : D ≠ 0 := by
    intro hD0
    apply hne
    dsimp [D] at hD0
    exact sub_eq_zero.mp hD0 |>.symm
  let g : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) *
    ((C * NormedSpace.exp (t • D)).trace.re +
      (M * NormedSpace.exp (t • (-D))).trace.re)
  have hderivRaw := hasDerivAt_finiteBuresExpHalfSum C M D
  have hderivSum :
      (C * D).trace.re + (M * (-D)).trace.re =
        -finiteMatrixHilbertSchmidtSq D := by
    simpa [D] using
      finiteBuresExpHalfSum_derivative_eq_neg_hilbertSchmidtSq
        C M hC.isHermitian hM.isHermitian
  have hderiv : HasDerivAt g
      (-(1 / 2 : ℝ) * finiteMatrixHilbertSchmidtSq D) 0 := by
    convert hderivRaw using 1
    rw [hderivSum]
    ring
  have hhsPos : 0 < finiteMatrixHilbertSchmidtSq D :=
    finiteMatrixHilbertSchmidtSq_pos_of_ne_zero D hDne
  have hderivNeg : -(1 / 2 : ℝ) * finiteMatrixHilbertSchmidtSq D < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hhsPos
  obtain ⟨t, _ht, hdrop⟩ :=
    exists_right_lt_of_hasDerivAt_neg hderiv hderivNeg
  have hg0 : g 0 = 1 := by
    simp [g, hCtrace, hMtrace]
    norm_num
  have hW : (t • D).IsHermitian := hD.smul (by simp [isSelfAdjoint_iff])
  have hA : (NormedSpace.exp (t • D)).PosDef := by
    have hnonneg : 0 ≤ NormedSpace.exp (t • D) :=
      hW.isSelfAdjoint.exp_nonneg
    have hpsd : (NormedSpace.exp (t • D)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp hnonneg
    exact hpsd.posDef_iff_isUnit.mpr (Matrix.isUnit_exp (t • D))
  have hbound := finiteBuresRootFidelity_le_reporterHalfSum hC hM hA
  have hreporter :
      finiteBuresReporterHalfSum C M (NormedSpace.exp (t • D)) = g t := by
    simp [finiteBuresReporterHalfSum, g, Matrix.exp_neg]
    ring
  rw [hfid, hreporter] at hbound
  rw [hg0] at hdrop
  exact (not_lt_of_ge hbound) hdrop

/-- Root fidelity one exactly characterizes equality of density matrices. -/
theorem finiteBuresRootFidelity_eq_one_iff
    {n : ℕ} [Nonempty (Fin n)]
    {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef)
    (hCtrace : C.trace.re = 1) (hMtrace : M.trace.re = 1) :
    finiteBuresRootFidelity C M = 1 ↔ C = M := by
  constructor
  · exact finiteBuresRootFidelity_eq_one_implies_eq
      hC hM hCtrace hMtrace
  · intro h
    subst M
    rw [finiteBuresRootFidelity_self_eq_trace hC, hCtrace]

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

/-- A compact convex target body saturates unit fidelity exactly when it
contains the source density matrix. -/
theorem compactBuresDualCapacity_sq_eq_one_iff_mem
    {n : ℕ} [Nonempty (Fin n)]
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (hsourceTrace : source.trace.re = 1)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef})
    (hKtrace : ∀ M ∈ K, M.trace.re = 1) :
    compactBuresDualCapacity source K ^ (2 : ℕ) = 1 ↔ source ∈ K := by
  obtain ⟨M, hM, hcap⟩ :=
    exists_compactBuresRootFidelity_eq_dualCapacity
      source hKne hKcompact hKpsd
  have hcapNonneg : 0 ≤ compactBuresDualCapacity source K := by
    rw [hcap]
    exact finiteBuresRootFidelity_nonneg (hKpsd hM)
  constructor
  · intro hsquare
    have hcapOne : compactBuresDualCapacity source K = 1 := by
      nlinarith
    have hfid : finiteBuresRootFidelity source M = 1 := by
      rw [hcap] at hcapOne
      exact hcapOne
    have heq : source = M := finiteBuresRootFidelity_eq_one_implies_eq
      hsource (hKpsd hM) hsourceTrace (hKtrace M hM) hfid
    exact heq.symm ▸ hM
  · intro hsourceMem
    have hle : finiteBuresRootFidelity source source ≤
        compactBuresDualCapacity source K := by
      unfold compactBuresDualCapacity
      exact le_csSup
        (compactBuresDualValueSet_bddAbove source hKcompact hKpsd)
        ⟨source, hsourceMem, rfl⟩
    have hlower : 1 ≤ compactBuresDualCapacity source K := by
      rw [finiteBuresRootFidelity_self_eq_trace hsource, hsourceTrace] at hle
      exact hle
    have hupper : compactBuresDualCapacity source K ≤ 1 :=
      compactBuresDualCapacity_le_one hsource hsourceTrace
        hKne hKcompact hKpsd hKtrace
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
    compactBuresDistance source K ^ (2 : ℕ) =
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
    compactBuresDualCapacity source (finiteBuresOccupiedTargetBody V) ^ (2 : ℕ) =
      source.trace.re *
        (1 - compactBuresDistance
          (finiteBuresNormalizedSource source)
          (finiteBuresOccupiedTargetBody V) ^ (2 : ℕ) / 2) ^ (2 : ℕ) := by
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
      1 - compactBuresDistance rho K ^ (2 : ℕ) / 2 := by
    linarith
  have hscale : compactBuresDualCapacity source K =
      Real.sqrt source.trace.re * compactBuresDualCapacity rho K := by
    calc
      compactBuresDualCapacity source K =
          compactBuresDualCapacity (source.trace.re • rho) K := by
        rw [finiteBuresTrace_smul_normalizedSource htrace]
      _ = Real.sqrt source.trace.re * compactBuresDualCapacity rho K :=
        compactBuresDualCapacity_smul_left hrho source.trace.re
          htrace.le hKne hKcompact hKpsd
  change compactBuresDualCapacity source K ^ (2 : ℕ) =
    source.trace.re * (1 - compactBuresDistance rho K ^ (2 : ℕ) / 2) ^ (2 : ℕ)
  rw [hscale, hcap, mul_pow, Real.sq_sqrt htrace.le]

/-- **Exact occupied-body saturation rigidity `(13)`.**  Complete Bures
incidence reaches total source mass exactly when the normalized source is
already a convex mixture of occupied target rays. -/
theorem occupiedTargetBures_saturation_iff_normalizedSource_mem
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (htrace : 0 < source.trace.re)
    {V : Set (Fin n → ℂ)} (hVne : V.Nonempty)
    (hVbounded : Bornology.IsBounded V)
    (hVunit : ∀ v ∈ V, (finiteComplexInner v v).re = 1) :
    compactBuresDualCapacity source (finiteBuresOccupiedTargetBody V) ^ (2 : ℕ) =
        source.trace.re ↔
      finiteBuresNormalizedSource source ∈ finiteBuresOccupiedTargetBody V := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp [Matrix.trace] at htrace
  letI : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
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
  have hsat : compactBuresDualCapacity rho K ^ (2 : ℕ) = 1 ↔ rho ∈ K :=
    compactBuresDualCapacity_sq_eq_one_iff_mem
      hrho hrhotrace hKne hKcompact hKpsd hKtrace
  have hscale : compactBuresDualCapacity source K =
      Real.sqrt source.trace.re * compactBuresDualCapacity rho K := by
    calc
      compactBuresDualCapacity source K =
          compactBuresDualCapacity (source.trace.re • rho) K := by
        rw [finiteBuresTrace_smul_normalizedSource htrace]
      _ = Real.sqrt source.trace.re * compactBuresDualCapacity rho K :=
        compactBuresDualCapacity_smul_left hrho source.trace.re
          htrace.le hKne hKcompact hKpsd
  have hscaleSq : compactBuresDualCapacity source K ^ (2 : ℕ) =
      source.trace.re * compactBuresDualCapacity rho K ^ (2 : ℕ) := by
    rw [hscale, mul_pow, Real.sq_sqrt htrace.le]
  change compactBuresDualCapacity source K ^ (2 : ℕ) = source.trace.re ↔ rho ∈ K
  rw [hscaleSq]
  constructor
  · intro h
    apply hsat.mp
    nlinarith
  · intro hmem
    have hone := hsat.mpr hmem
    nlinarith

/-- Matrices annihilated on the left by a fixed source form a convex set. -/
theorem convex_finiteMatrix_leftAnnihilator
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ {M : Matrix (Fin n) (Fin n) ℂ | C * M = 0} := by
  intro M hM N hN a b ha hb hab
  simp only [Set.mem_setOf_eq] at hM hN ⊢
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hM, hN,
    smul_zero, smul_zero, add_zero]

/-- The left annihilator of a fixed finite matrix is closed. -/
theorem isClosed_finiteMatrix_leftAnnihilator
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | C * M = 0} := by
  have hcont : Continuous
      (fun M : Matrix (Fin n) (Fin n) ℂ ↦ C * M) := by fun_prop
  exact isClosed_eq hcont continuous_const

/-- Annihilating every occupied vector annihilates its complete closed
convex target body. -/
theorem finiteBuresOccupiedTargetBody_mul_eq_zero
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    {V : Set (Fin n → ℂ)}
    (hkill : ∀ v ∈ V, Matrix.mulVec C v = 0) :
    ∀ M ∈ finiteBuresOccupiedTargetBody V, C * M = 0 := by
  have hrays : finiteBuresTargetRay '' V ⊆
      {M : Matrix (Fin n) (Fin n) ℂ | C * M = 0} := by
    rintro M ⟨v, hv, rfl⟩
    change C * Matrix.vecMulVec v (star v) = 0
    have hv0 := hkill v hv
    ext i j
    have hvi : (∑ x, C i x * v x) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv0 i
    change (∑ x, C i x * (v x * star (v j))) = 0
    calc
      (∑ x, C i x * (v x * star (v j))) =
          (∑ x, C i x * v x) * star (v j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hvi, zero_mul]
  exact closedConvexHull_min hrays
    (convex_finiteMatrix_leftAnnihilator C)
    (isClosed_finiteMatrix_leftAnnihilator C)

/-- **Complete occupied-support law `(14)`.**  Complete Bures incidence
vanishes exactly when source covariance annihilates every occupied target.
The result covers the full closed convex target body, not only a chosen
finite mixture. -/
theorem occupiedTargetBures_dualCapacity_sq_eq_zero_iff
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {V : Set (Fin n → ℂ)} (hVne : V.Nonempty)
    (hVbounded : Bornology.IsBounded V) :
    compactBuresDualCapacity source (finiteBuresOccupiedTargetBody V) ^ (2 : ℕ) = 0 ↔
      ∀ v ∈ V, Matrix.mulVec source v = 0 := by
  let K := finiteBuresOccupiedTargetBody V
  have hKne : K.Nonempty := finiteBuresOccupiedTargetBody_nonempty hVne
  have hKcompact : IsCompact K :=
    finiteBuresOccupiedTargetBody_isCompact_of_isBounded hVbounded
  have hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} :=
    finiteBuresOccupiedTargetBody_posSemidef V
  constructor
  · intro hsquare v hv
    have hcapzero : compactBuresDualCapacity source K = 0 := by
      nlinarith
    have hRay : finiteBuresTargetRay v ∈ K :=
      (subset_closedConvexHull (𝕜 := ℝ)) ⟨v, hv, rfl⟩
    have hle : finiteBuresRootFidelity source (finiteBuresTargetRay v) ≤
        compactBuresDualCapacity source K := by
      unfold compactBuresDualCapacity
      exact le_csSup
        (compactBuresDualValueSet_bddAbove source hKcompact hKpsd)
        ⟨finiteBuresTargetRay v, hRay, rfl⟩
    have hnonneg := finiteBuresRootFidelity_nonneg
      (C := source) (finiteBuresTargetRay_posSemidef v)
    have hfidzero : finiteBuresRootFidelity source
        (finiteBuresTargetRay v) = 0 := by
      rw [hcapzero] at hle
      exact le_antisymm hle hnonneg
    have hsqzero := congrArg (fun x : ℝ ↦ x ^ (2 : ℕ)) hfidzero
    exact (finiteBuresTrace_sq_rankOne_right_eq_zero_iff hsource v).mp (by
      simpa [finiteBuresRootFidelity, finiteBuresTargetRay] using hsqzero)
  · intro hkill
    obtain ⟨M, hM, hcap⟩ :=
      exists_compactBuresRootFidelity_eq_dualCapacity
        source hKne hKcompact hKpsd
    have hCM : source * M = 0 :=
      finiteBuresOccupiedTargetBody_mul_eq_zero hkill M hM
    have hsq := finiteBuresTrace_sq_le_rank_mul_traceProduct
      hsource (hKpsd hM)
    rw [hCM] at hsq
    simp only [Matrix.trace_zero, Complex.zero_re, mul_zero] at hsq
    have hnonneg := finiteBuresRootFidelity_nonneg (C := source) (hKpsd hM)
    have hfidzero : finiteBuresRootFidelity source M = 0 := by
      change finiteBuresRootFidelity source M ^ (2 : ℕ) ≤ 0 at hsq
      nlinarith
    rw [hcap, hfidzero, zero_pow (by norm_num : 2 ≠ 0)]

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
    compactBuresDualCapacity source (finiteBuresOccupiedTargetBody V) ^ (2 : ℕ) ≤
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
