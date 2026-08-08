import GaloisForLFunctions.HTGeometry.FiniteBuresReporterVariationalLaw
import GaloisForLFunctions.HTGeometry.FiniteBuresTargetMinimaxCore
import GaloisForLFunctions.HTGeometry.BuresPositiveReporterIncidenceLaw

/-!
# Compact-target Bures minimax law

This module removes finite target enumeration.  Every nonempty compact convex
body of positive semidefinite target operators obeys the exact additive and
product Bures minimax laws while the positive-reporter cone remains noncompact.
-/

open Filter MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Compact-convex target bodies -/

def compactBuresSaddleValue {n : ℕ}
    (source M A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  finiteBuresReporterHalfSum source M A

def compactBuresDualValueSet {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ M ∈ K, q = finiteBuresRootFidelity source M}

def compactBuresDualCapacity {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sSup (compactBuresDualValueSet source K)

def compactBuresReporterTargetValueSet {n : ℕ}
    (source A : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ M ∈ K, q = compactBuresSaddleValue source M A}

def compactBuresReporterWorstValue {n : ℕ}
    (source A : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sSup (compactBuresReporterTargetValueSet source A K)

def compactBuresPrimalValueSet {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = compactBuresReporterWorstValue source A K}

def compactBuresPrimalCapacity {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sInf (compactBuresPrimalValueSet source K)

theorem continuous_compactBuresSaddleValue_left
    {n : ℕ} (source A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun M => compactBuresSaddleValue source M A) := by
  unfold compactBuresSaddleValue finiteBuresReporterHalfSum
  fun_prop

theorem continuousOn_compactBuresSaddleValue_right
    {n : ℕ} (source M : Matrix (Fin n) (Fin n) ℂ) :
    ContinuousOn (compactBuresSaddleValue source M)
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
  unfold compactBuresSaddleValue finiteBuresReporterHalfSum
  exact ((finiteBuresContinuous_sourcePairing source).continuousOn.add
    (finiteBuresContinuousOn_targetPairing M)).div_const 2

theorem affine_compactBuresSaddleValue_left
    {n : ℕ} (source A : Matrix (Fin n) (Fin n) ℂ) :
    ∀ M N : Matrix (Fin n) (Fin n) ℂ, ∀ a b : ℝ, a + b = 1 →
      compactBuresSaddleValue source (a • M + b • N) A =
        a * compactBuresSaddleValue source M A +
          b * compactBuresSaddleValue source N A := by
  intro M N a b hab
  unfold compactBuresSaddleValue finiteBuresReporterHalfSum
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hsource : ((source * A).trace).re =
      a * ((source * A).trace).re + b * ((source * A).trace).re := by
    calc
      ((source * A).trace).re = (a + b) * ((source * A).trace).re := by
        rw [hab, one_mul]
      _ = _ := by ring
  linear_combination hsource / 2

theorem convexOn_compactBuresSaddleValue_left
    {n : ℕ} {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKconvex : Convex ℝ K)
    (source A : Matrix (Fin n) (Fin n) ℂ) :
    ConvexOn ℝ K (fun M => compactBuresSaddleValue source M A) := by
  refine ⟨hKconvex, ?_⟩
  intro M hM N hN a b ha hb hab
  simpa [smul_eq_mul] using
    (affine_compactBuresSaddleValue_left source A M N a b hab).le

theorem concaveOn_compactBuresSaddleValue_left
    {n : ℕ} {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKconvex : Convex ℝ K)
    (source A : Matrix (Fin n) (Fin n) ℂ) :
    ConcaveOn ℝ K (fun M => compactBuresSaddleValue source M A) := by
  refine ⟨hKconvex, ?_⟩
  intro M hM N hN a b ha hb hab
  simpa [smul_eq_mul] using
    (affine_compactBuresSaddleValue_left source A M N a b hab).ge

theorem convexOn_compactBuresSaddleValue_right
    {n : ℕ} {source M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) :
    ConvexOn ℝ {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef}
      (compactBuresSaddleValue source M) := by
  have hs := finiteBuresConvexOn_sourcePairing source
  have ht := finiteBuresConvexOn_targetPairing hM
  refine ⟨finiteBuresConvex_posDefMatrices, ?_⟩
  intro A hA B hB a b ha hb hab
  have hs' := hs.2 hA hB ha hb hab
  have ht' := ht.2 hA hB ha hb hab
  simp only [compactBuresSaddleValue, finiteBuresReporterHalfSum,
    finiteBuresSourcePairing, finiteBuresTargetPairing, smul_eq_mul] at hs' ht' ⊢
  linarith

theorem compactBuresSaddleValue_nonneg
    {n : ℕ} {source M A : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (hM : M.PosSemidef) (hA : A.PosDef) :
    0 ≤ compactBuresSaddleValue source M A := by
  have hx := finiteBuresSourcePairing_nonneg hsource hA
  have hy : 0 ≤ finiteBuresTargetPairing M A := by
    exact finiteBuresSourcePairing_nonneg hM hA.inv
  change 0 ≤ (finiteBuresSourcePairing source A +
    finiteBuresTargetPairing M A) / 2
  linarith

theorem compactBuresDualValueSet_nonempty
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hKne : K.Nonempty) :
    (compactBuresDualValueSet source K).Nonempty := by
  obtain ⟨M, hM⟩ := hKne
  exact ⟨finiteBuresRootFidelity source M, M, hM, rfl⟩

theorem compactBuresDualValueSet_bddAbove
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    BddAbove (compactBuresDualValueSet source K) := by
  have hcont := (continuousOn_finiteBuresRootFidelity_right source).mono hKpsd
  have himage : IsCompact ((fun M => finiteBuresRootFidelity source M) '' K) :=
    hKcompact.image_of_continuousOn hcont
  obtain ⟨B, hB⟩ := himage.bddAbove
  refine ⟨B, ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact hB ⟨M, hM, rfl⟩

theorem compactBuresReporterTargetValueSet_nonempty
    {n : ℕ} (source A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hKne : K.Nonempty) :
    (compactBuresReporterTargetValueSet source A K).Nonempty := by
  obtain ⟨M, hM⟩ := hKne
  exact ⟨compactBuresSaddleValue source M A, M, hM, rfl⟩

theorem compactBuresReporterTargetValueSet_bddAbove
    {n : ℕ} (source A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKcompact : IsCompact K) :
    BddAbove (compactBuresReporterTargetValueSet source A K) := by
  have himage : IsCompact ((fun M => compactBuresSaddleValue source M A) '' K) :=
    hKcompact.image (continuous_compactBuresSaddleValue_left source A)
  obtain ⟨B, hB⟩ := himage.bddAbove
  refine ⟨B, ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact hB ⟨M, hM, rfl⟩

theorem compactBuresReporterWorstValue_nonneg
    {n : ℕ} {source A : Matrix (Fin n) (Fin n) ℂ}
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hsource : source.PosSemidef) (hA : A.PosDef)
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    0 ≤ compactBuresReporterWorstValue source A K := by
  obtain ⟨M, hM⟩ := hKne
  apply (compactBuresSaddleValue_nonneg hsource (hKpsd hM) hA).trans
  unfold compactBuresReporterWorstValue
  apply le_csSup
  · exact compactBuresReporterTargetValueSet_bddAbove source A hKcompact
  · exact ⟨M, hM, rfl⟩

theorem compactBuresPrimalValueSet_nonempty
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) :
    (compactBuresPrimalValueSet source K).Nonempty := by
  exact ⟨compactBuresReporterWorstValue source 1 K,
    1, Matrix.PosDef.one, rfl⟩

theorem compactBuresPrimalValueSet_bddBelow
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hsource : source.PosSemidef) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    BddBelow (compactBuresPrimalValueSet source K) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact compactBuresReporterWorstValue_nonneg hsource hA hKne hKcompact hKpsd

/-- Sion exchange for an arbitrary nonempty compact convex body of positive
semidefinite targets.  Reporter cone remains noncompact. -/
theorem compactBuresPrimalCapacity_eq_dualCapacity
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    compactBuresPrimalCapacity source K =
      compactBuresDualCapacity source K := by
  classical
  let X : Set (Matrix (Fin n) (Fin n) ℂ) := K
  let Y : Set (Matrix (Fin n) (Fin n) ℂ) := {A | A.PosDef}
  let f : Matrix (Fin n) (Fin n) ℂ →
      Matrix (Fin n) (Fin n) ℂ → ℝ :=
    fun M A => -compactBuresSaddleValue source M A
  have hYconvex : Convex ℝ Y := finiteBuresConvex_posDefMatrices
  have hfy : ∀ A ∈ Y,
      LowerSemicontinuousOn (fun M => f M A) X := by
    intro A hA
    exact (continuous_compactBuresSaddleValue_left source A).neg.continuousOn
      |>.lowerSemicontinuousOn
  have hfy' : ∀ A ∈ Y,
      QuasiconvexOn ℝ X (fun M => f M A) := by
    intro A hA
    exact (concaveOn_compactBuresSaddleValue_left hKconvex source A).neg.quasiconvexOn
  have hfx : ∀ M ∈ X,
      UpperSemicontinuousOn (fun A => f M A) Y := by
    intro M hM
    exact (continuousOn_compactBuresSaddleValue_right source M).neg.upperSemicontinuousOn
  have hfx' : ∀ M ∈ X,
      QuasiconcaveOn ℝ Y (fun A => f M A) := by
    intro M hM
    exact (convexOn_compactBuresSaddleValue_right (hKpsd hM)).neg.quasiconcaveOn
  have hsup_y : ∀ M ∈ X,
      IsLUB {q : ℝ | ∃ A ∈ Y, f M A = q}
        (-finiteBuresRootFidelity source M) := by
    intro M hM
    have hMpsd := hKpsd hM
    let values : Set ℝ := {q | ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧ q = finiteBuresReporterHalfSum source M A}
    have hne : values.Nonempty :=
      finiteBuresReporterHalfSumCapacity_values_nonempty source M
    have hb : BddBelow values := by
      refine ⟨finiteBuresRootFidelity source M, ?_⟩
      rintro q ⟨A, hA, rfl⟩
      exact finiteBuresRootFidelity_le_reporterHalfSum hsource hMpsd hA
    have hglb : IsGLB values (finiteBuresRootFidelity source M) := by
      rw [← finiteBuresReporterHalfSumCapacity_eq_rootFidelity hsource hMpsd]
      exact isGLB_csInf hne hb
    have hglb' : IsGLB
        {q : ℝ | ∃ A ∈ Y, compactBuresSaddleValue source M A = q}
        (finiteBuresRootFidelity source M) := by
      simpa [values, Y, compactBuresSaddleValue, eq_comm] using hglb
    have hneg := finiteBuresIsLUB_neg_functionValues_of_isGLB hglb'
    simpa [f] using hneg
  have hinf_sup : IsGLB
      {q : ℝ | ∃ M ∈ X, -finiteBuresRootFidelity source M = q}
      (-compactBuresDualCapacity source K) := by
    have hlub : IsLUB (compactBuresDualValueSet source K)
        (compactBuresDualCapacity source K) := by
      exact isLUB_csSup (compactBuresDualValueSet_nonempty source hKne)
        (compactBuresDualValueSet_bddAbove source hKcompact hKpsd)
    have hlub' : IsLUB
        {q : ℝ | ∃ M ∈ X, finiteBuresRootFidelity source M = q}
        (compactBuresDualCapacity source K) := by
      simpa [compactBuresDualValueSet, X, eq_comm] using hlub
    have hneg := finiteBuresIsGLB_neg_functionValues_of_isLUB hlub'
    simpa [X, compactBuresDualCapacity, compactBuresDualValueSet] using hneg
  have hinf_x : ∀ A ∈ Y,
      IsGLB {q : ℝ | ∃ M ∈ X, f M A = q}
        (-compactBuresReporterWorstValue source A K) := by
    intro A hA
    have hlub : IsLUB (compactBuresReporterTargetValueSet source A K)
        (compactBuresReporterWorstValue source A K) := by
      exact isLUB_csSup
        (compactBuresReporterTargetValueSet_nonempty source A hKne)
        (compactBuresReporterTargetValueSet_bddAbove source A hKcompact)
    have hlub' : IsLUB
        {q : ℝ | ∃ M ∈ X, compactBuresSaddleValue source M A = q}
        (compactBuresReporterWorstValue source A K) := by
      simpa [compactBuresReporterTargetValueSet, X, eq_comm] using hlub
    have hneg := finiteBuresIsGLB_neg_functionValues_of_isLUB hlub'
    simpa [f, X, compactBuresReporterTargetValueSet] using hneg
  have hsup_inf : IsLUB
      {q : ℝ | ∃ A ∈ Y, -compactBuresReporterWorstValue source A K = q}
      (-compactBuresPrimalCapacity source K) := by
    have hglb : IsGLB (compactBuresPrimalValueSet source K)
        (compactBuresPrimalCapacity source K) := by
      exact isGLB_csInf (compactBuresPrimalValueSet_nonempty source K)
        (compactBuresPrimalValueSet_bddBelow hsource hKne hKcompact hKpsd)
    have hglb' : IsGLB
        {q : ℝ | ∃ A ∈ Y,
          compactBuresReporterWorstValue source A K = q}
        (compactBuresPrimalCapacity source K) := by
      simpa [compactBuresPrimalValueSet, Y, eq_comm] using hglb
    have hneg := finiteBuresIsLUB_neg_functionValues_of_isGLB hglb'
    simpa [Y, compactBuresPrimalCapacity, compactBuresPrimalValueSet] using hneg
  have hminimax : -compactBuresDualCapacity source K =
      -compactBuresPrimalCapacity source K := by
    exact Sion.minimax hKne hKcompact hfy hfy' hYconvex hfx hfx'
      hKconvex
      (fun M => -finiteBuresRootFidelity source M) hsup_y
      (-compactBuresDualCapacity source K) hinf_sup
      (fun A => -compactBuresReporterWorstValue source A K) hinf_x
      (-compactBuresPrimalCapacity source K) hsup_inf
  linarith

def compactBuresTargetPairingValueSet {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ M ∈ K, q = finiteBuresTargetPairing M A}

def compactBuresTargetMaximum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sSup (compactBuresTargetPairingValueSet A K)

theorem compactBuresTargetPairingValueSet_nonempty
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hKne : K.Nonempty) :
    (compactBuresTargetPairingValueSet A K).Nonempty := by
  obtain ⟨M, hM⟩ := hKne
  exact ⟨finiteBuresTargetPairing M A, M, hM, rfl⟩

theorem compactBuresTargetPairingValueSet_bddAbove
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hKcompact : IsCompact K) :
    BddAbove (compactBuresTargetPairingValueSet A K) := by
  have hcont : Continuous (fun M => finiteBuresTargetPairing M A) := by
    unfold finiteBuresTargetPairing
    fun_prop
  have himage := hKcompact.image hcont
  obtain ⟨B, hB⟩ := himage.bddAbove
  refine ⟨B, ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact hB ⟨M, hM, rfl⟩

theorem exists_compactBuresTargetPairing_eq_targetMaximum
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    ∃ M ∈ K,
      compactBuresTargetMaximum A K = finiteBuresTargetPairing M A := by
  have hcont : ContinuousOn (fun M => finiteBuresTargetPairing M A) K := by
    unfold finiteBuresTargetPairing
    fun_prop
  obtain ⟨M, hM, hmax⟩ := hKcompact.exists_isMaxOn hKne hcont
  refine ⟨M, hM, ?_⟩
  have hlub : IsLUB (compactBuresTargetPairingValueSet A K)
      (finiteBuresTargetPairing M A) := by
    have hraw := hmax.isLUB hM
    simpa [compactBuresTargetPairingValueSet, eq_comm] using hraw
  unfold compactBuresTargetMaximum
  exact (isLUB_csSup (compactBuresTargetPairingValueSet_nonempty A hKne)
    (compactBuresTargetPairingValueSet_bddAbove A hKcompact)).unique hlub

theorem compactBuresTargetMaximum_nonneg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    0 ≤ compactBuresTargetMaximum A K := by
  obtain ⟨M, hM, hmax⟩ :=
    exists_compactBuresTargetPairing_eq_targetMaximum A hKne hKcompact
  rw [hmax]
  exact finiteBuresSourcePairing_nonneg (hKpsd hM) hA.inv

theorem compactBuresReporterWorstValue_eq_halfSumMaximum
    {n : ℕ} (source A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    compactBuresReporterWorstValue source A K =
      (finiteBuresSourcePairing source A + compactBuresTargetMaximum A K) / 2 := by
  obtain ⟨Mmax, hMmax, hmax⟩ :=
    exists_compactBuresTargetPairing_eq_targetMaximum A hKne hKcompact
  unfold compactBuresReporterWorstValue
  apply le_antisymm
  · apply csSup_le (compactBuresReporterTargetValueSet_nonempty source A hKne)
    rintro q ⟨M, hM, rfl⟩
    have hle : finiteBuresTargetPairing M A ≤ compactBuresTargetMaximum A K :=
      le_csSup (compactBuresTargetPairingValueSet_bddAbove A hKcompact)
        ⟨M, hM, rfl⟩
    have hle' : ((M * A⁻¹).trace).re ≤ compactBuresTargetMaximum A K := by
      simpa [finiteBuresTargetPairing] using hle
    unfold compactBuresSaddleValue finiteBuresReporterHalfSum
    unfold finiteBuresSourcePairing
    linarith
  · apply le_csSup (compactBuresReporterTargetValueSet_bddAbove source A hKcompact)
    refine ⟨Mmax, hMmax, ?_⟩
    have hmax' : compactBuresTargetMaximum A K =
        ((Mmax * A⁻¹).trace).re := by
      simpa [finiteBuresTargetPairing] using hmax
    unfold compactBuresSaddleValue finiteBuresReporterHalfSum
    rw [hmax']
    rfl

theorem compactBuresTargetPairing_real_smul
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    finiteBuresTargetPairing M (c • A) =
      c⁻¹ * finiteBuresTargetPairing M A := by
  unfold finiteBuresTargetPairing
  rw [finiteBuresMatrix_inv_real_smul hA hc,
    Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  rfl

theorem compactBuresTargetMaximum_real_smul
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    compactBuresTargetMaximum (c • A) K =
      c⁻¹ * compactBuresTargetMaximum A K := by
  unfold compactBuresTargetMaximum
  apply le_antisymm
  · apply csSup_le (compactBuresTargetPairingValueSet_nonempty (c • A) hKne)
    rintro q ⟨M, hM, rfl⟩
    rw [compactBuresTargetPairing_real_smul hA hc]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (compactBuresTargetPairingValueSet_bddAbove A hKcompact)
        ⟨M, hM, rfl⟩)
      (inv_nonneg.mpr hc.le)
  · obtain ⟨M, hM, hmax⟩ :=
      exists_compactBuresTargetPairing_eq_targetMaximum A hKne hKcompact
    rw [show sSup (compactBuresTargetPairingValueSet A K) =
      finiteBuresTargetPairing M A from hmax,
      ← compactBuresTargetPairing_real_smul hA hc]
    exact le_csSup
      (compactBuresTargetPairingValueSet_bddAbove (c • A) hKcompact)
      ⟨M, hM, rfl⟩

theorem compactBuresHalfSumMaximum_real_smul
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    (finiteBuresSourcePairing source (c • A) +
        compactBuresTargetMaximum (c • A) K) / 2 =
      (c * finiteBuresSourcePairing source A +
        c⁻¹ * compactBuresTargetMaximum A K) / 2 := by
  rw [finiteBuresSourcePairing_real_smul,
    compactBuresTargetMaximum_real_smul hA hc hKne hKcompact]

def compactBuresHalfSumMaximumValueSet {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = (finiteBuresSourcePairing source A +
      compactBuresTargetMaximum A K) / 2}

def compactBuresRootProductValueSet {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = Real.sqrt (finiteBuresSourcePairing source A *
      compactBuresTargetMaximum A K)}

def compactBuresProductValueSet {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = finiteBuresSourcePairing source A * compactBuresTargetMaximum A K}

def compactBuresProductCapacity {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sInf (compactBuresProductValueSet source K)

theorem compactBuresPrimalCapacity_eq_halfSumMaximumInfimum
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    compactBuresPrimalCapacity source K =
      sInf (compactBuresHalfSumMaximumValueSet source K) := by
  unfold compactBuresPrimalCapacity compactBuresPrimalValueSet
  congr 2
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA,
      compactBuresReporterWorstValue_eq_halfSumMaximum source A hKne hKcompact⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA,
      (compactBuresReporterWorstValue_eq_halfSumMaximum source A hKne hKcompact).symm⟩

theorem compactBuresHalfSumMaximumValueSet_nonempty
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) :
    (compactBuresHalfSumMaximumValueSet source K).Nonempty := by
  exact ⟨(finiteBuresSourcePairing source 1 + compactBuresTargetMaximum 1 K) / 2,
    1, Matrix.PosDef.one, rfl⟩

theorem compactBuresHalfSumMaximumValueSet_bddBelow
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hsource : source.PosSemidef) (hKne : K.Nonempty)
    (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    BddBelow (compactBuresHalfSumMaximumValueSet source K) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  have hx := finiteBuresSourcePairing_nonneg hsource hA
  have hy := compactBuresTargetMaximum_nonneg hA hKne hKcompact hKpsd
  linarith

theorem compactBuresRootProductValueSet_nonempty
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) :
    (compactBuresRootProductValueSet source K).Nonempty := by
  exact ⟨Real.sqrt (finiteBuresSourcePairing source 1 *
    compactBuresTargetMaximum 1 K), 1, Matrix.PosDef.one, rfl⟩

theorem compactBuresRootProductValueSet_bddBelow
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ)
    (K : Set (Matrix (Fin n) (Fin n) ℂ)) :
    BddBelow (compactBuresRootProductValueSet source K) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact Real.sqrt_nonneg _

theorem compactBuresSInf_halfSum_eq_sInf_rootProduct
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    sInf (compactBuresHalfSumMaximumValueSet source K) =
      sInf (compactBuresRootProductValueSet source K) := by
  let H := compactBuresHalfSumMaximumValueSet source K
  let R := compactBuresRootProductValueSet source K
  have hHne : H.Nonempty := compactBuresHalfSumMaximumValueSet_nonempty source K
  have hHb : BddBelow H := compactBuresHalfSumMaximumValueSet_bddBelow
    hsource hKne hKcompact hKpsd
  have hRne : R.Nonempty := compactBuresRootProductValueSet_nonempty source K
  have hRb : BddBelow R := compactBuresRootProductValueSet_bddBelow source K
  apply le_antisymm
  · apply le_csInf hRne
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    let x := finiteBuresSourcePairing source A
    let y := compactBuresTargetMaximum A K
    have hx : 0 ≤ x := finiteBuresSourcePairing_nonneg hsource hA
    have hy : 0 ≤ y := compactBuresTargetMaximum_nonneg hA hKne hKcompact hKpsd
    have hsubset : finiteBuresScaleHalfSet x y ⊆ H := by
      rintro q ⟨c, hc, rfl⟩
      refine ⟨c • A, hA.smul hc, ?_⟩
      exact (compactBuresHalfSumMaximum_real_smul source hA hc hKne hKcompact).symm
    calc
      sInf H ≤ sInf (finiteBuresScaleHalfSet x y) := by
        apply le_csInf (finiteBuresScaleHalfSet_nonempty x y)
        intro q hq
        exact csInf_le hHb (hsubset hq)
      _ = Real.sqrt (x * y) := finiteBuresSInf_scaleHalfSet_eq_sqrt_mul hx hy
  · apply le_csInf hHne
    intro q hq
    rcases hq with ⟨A, hA, rfl⟩
    have hx := finiteBuresSourcePairing_nonneg hsource hA
    have hy := compactBuresTargetMaximum_nonneg hA hKne hKcompact hKpsd
    have hroot : Real.sqrt (finiteBuresSourcePairing source A *
        compactBuresTargetMaximum A K) ∈ R := ⟨A, hA, rfl⟩
    exact (csInf_le hRb hroot).trans
      (by simpa using (finiteBuresSqrt_mul_le_scaled_half hx hy
        (show (0 : ℝ) < 1 by norm_num)))

theorem compactBuresProductValueSet_eq_sq_image_rootProductValueSet
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    compactBuresProductValueSet source K =
      (fun r : ℝ => r ^ 2) '' compactBuresRootProductValueSet source K := by
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Real.sqrt (finiteBuresSourcePairing source A *
      compactBuresTargetMaximum A K), ⟨A, hA, rfl⟩, ?_⟩
    exact Real.sq_sqrt (mul_nonneg (finiteBuresSourcePairing_nonneg hsource hA)
      (compactBuresTargetMaximum_nonneg hA hKne hKcompact hKpsd))
  · rintro ⟨r, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨A, hA, ?_⟩
    exact Real.sq_sqrt (mul_nonneg (finiteBuresSourcePairing_nonneg hsource hA)
      (compactBuresTargetMaximum_nonneg hA hKne hKcompact hKpsd))

theorem compactBuresSInf_product_eq_sq_sInf_rootProduct
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    sInf (compactBuresProductValueSet source K) =
      sInf (compactBuresRootProductValueSet source K) ^ 2 := by
  let R := compactBuresRootProductValueSet source K
  have hRne : R.Nonempty := compactBuresRootProductValueSet_nonempty source K
  have hRb : BddBelow R := compactBuresRootProductValueSet_bddBelow source K
  have hmono : MonotoneOn (fun r : ℝ => r ^ 2) R := by
    intro a ha b hb hab
    have ha0 : 0 ≤ a := by
      rcases ha with ⟨A, hA, rfl⟩
      exact Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := by
      rcases hb with ⟨A, hA, rfl⟩
      exact Real.sqrt_nonneg _
    exact (sq_le_sq₀ ha0 hb0).2 hab
  have hmap : sInf R ^ 2 = sInf ((fun r : ℝ => r ^ 2) '' R) :=
    MonotoneOn.map_csInf_of_continuousWithinAt
      ((continuous_pow 2).continuousAt.continuousWithinAt) hmono hRne hRb
  rw [compactBuresProductValueSet_eq_sq_image_rootProductValueSet
    hsource hKne hKcompact hKpsd]
  exact hmap.symm

/-- **Exact compact-target Bures product minimax law.** -/
theorem compactBuresProductCapacity_eq_dualCapacity_sq
    {n : ℕ} {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}) :
    compactBuresProductCapacity source K =
      compactBuresDualCapacity source K ^ 2 := by
  unfold compactBuresProductCapacity
  rw [compactBuresSInf_product_eq_sq_sInf_rootProduct
    hsource hKne hKcompact hKpsd]
  rw [← compactBuresSInf_halfSum_eq_sInf_rootProduct
    hsource hKne hKcompact hKpsd]
  rw [← compactBuresPrimalCapacity_eq_halfSumMaximumInfimum
    source hKne hKcompact]
  rw [compactBuresPrimalCapacity_eq_dualCapacity
    hsource hKne hKcompact hKconvex hKpsd]


theorem finiteBuresTargetLeverage_le_compactTargetMaximum
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKcompact : IsCompact K) {v : Fin n → ℂ}
    (hv : finiteBuresTargetRay v ∈ K) :
    finiteBuresTargetLeverage A v ≤ compactBuresTargetMaximum A K := by
  rw [← finiteBuresTargetRay_pairing_eq_leverage]
  unfold compactBuresTargetMaximum
  exact le_csSup (compactBuresTargetPairingValueSet_bddAbove A hKcompact)
    ⟨finiteBuresTargetRay v, hv, rfl⟩

/-- Complete-incidence capacity bound for an arbitrary target index type.
Targets need only land in one compact positive target body; no enumeration or
cardinality enters the estimate. -/
theorem compactBures_completeIncidence_capacity_bound
    {X C : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef})
    (htarget : ∀ c, finiteBuresTargetRay (target c) ∈ K)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      compactBuresProductCapacity
        (finitePositiveReporterSourceCovariance mu state) K := by
  unfold compactBuresProductCapacity
  apply le_csInf
  · exact ⟨finiteBuresSourcePairing
      (finitePositiveReporterSourceCovariance mu state) 1 *
        compactBuresTargetMaximum 1 K,
      1, Matrix.PosDef.one, rfl⟩
  intro q hq
  rcases hq with ⟨A, hA, rfl⟩
  have hbound := finitePositiveReporter_completeIncidence_covariance_bound
    mu A hA target state threshold hthreshold
      (compactBuresTargetMaximum A K)
      (compactBuresTargetMaximum_nonneg hA hKne hKcompact hKpsd)
      (fun c => by
        simpa [finitePositiveReporterTargetLeverage,
          finiteBuresTargetLeverage] using
          finiteBuresTargetLeverage_le_compactTargetMaximum
            A hKcompact (htarget c))
      (finitePositiveReporterSourceEnergy_integrable mu state A hprod)
      hprod
  simpa [finiteBuresSourcePairing, mul_comm] using hbound

/-- **Arbitrary-target compact Bures incidence minimax law.** -/
theorem compactBures_completeIncidence_minimax_bound
    {X C : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef})
    (htarget : ∀ c, finiteBuresTargetRay (target c) ∈ K)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance mu state) K ^ 2 := by
  have hsource := finitePositiveReporterSourceCovariance_posSemidef
    mu state hprod
  calc
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
        compactBuresProductCapacity
          (finitePositiveReporterSourceCovariance mu state) K :=
      compactBures_completeIncidence_capacity_bound
        mu target state threshold hthreshold hKne hKcompact hKpsd htarget hprod
    _ = _ := compactBuresProductCapacity_eq_dualCapacity_sq
      hsource hKne hKcompact hKconvex hKpsd

/-- Return mass is paid once for an arbitrary compact-target body. -/
theorem compactBures_returnExcisedIncidence_minimax_bound
    {X C : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K)
    (hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef})
    (htarget : ∀ c, finiteBuresTargetRay (target c) ∈ K)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j))
        (mu.restrict returnSetᶜ)) :
    mu.real (finitePositiveReporterCaptureEvent target state threshold) ≤
      mu.real returnSet +
        compactBuresDualCapacity
          (finitePositiveReporterSourceCovariance
            (mu.restrict returnSetᶜ) state) K ^ 2 / threshold := by
  let nu : Measure X := mu.restrict returnSetᶜ
  let E : Set X := finitePositiveReporterCaptureEvent target state threshold
  have hscaled := compactBures_completeIncidence_minimax_bound
    nu target state threshold hthreshold hKne hKcompact hKconvex hKpsd
      htarget hprod
  have hresidual :
      nu.real E ≤ compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance nu state) K ^ 2 / threshold := by
    apply (le_div_iff₀' hthreshold).2
    simpa [E, mul_comm] using hscaled
  have hcut := measureReal_le_return_add_restrict_compl
    mu E returnSet hreturn
  exact hcut.trans (by
    simpa [E, nu] using add_le_add_left hresidual (mu.real returnSet))

end

end GaloisForLFunctions.HTGeometry
