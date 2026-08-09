import GaloisForLFunctions.HTGeometry.SeparableBuresAlbertiApproximationLaw
import GaloisForLFunctions.HTGeometry.CompactBuresTargetMinimaxLaw

/-!
# Separable compact-target Bures minimax law

Exact compact-target Sion duality, reporter scaling, AM–GM infimum, and
product-capacity square identity in separable Hilbert space.
-/

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder InnerProductSpace

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def separableBuresDualValueSet
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ M ∈ K, q = operatorBuresRootFidelity
    (C : H →L[ℂ] H) (M : H →L[ℂ] H)}

def separableBuresDualCapacity
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : ℝ :=
  sSup (separableBuresDualValueSet C K)

def separableBuresReporterTargetValueSet
    (C : SchattenOneOperator H) (A : H →L[ℂ] H)
    (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ M ∈ K, q = separableBuresReporterHalfSum C M A}

def separableBuresReporterWorstValue
    (C : SchattenOneOperator H) (A : H →L[ℂ] H)
    (K : Set (SchattenOneOperator H)) : ℝ :=
  sSup (separableBuresReporterTargetValueSet C A K)

def separableBuresPrimalValueSet
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ A : H →L[ℂ] H, IsStrictlyPositive A ∧
    q = separableBuresReporterWorstValue C A K}

def separableBuresPrimalCapacity
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : ℝ :=
  sInf (separableBuresPrimalValueSet C K)

theorem separableBuresDualValueSet_nonempty
    (C : SchattenOneOperator H) {K : Set (SchattenOneOperator H)}
    (hK : K.Nonempty) :
    (separableBuresDualValueSet C K).Nonempty := by
  obtain ⟨M, hM⟩ := hK
  exact ⟨operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H),
    M, hM, rfl⟩

theorem separableBuresReporterTargetValueSet_nonempty
    (C : SchattenOneOperator H) (A : H →L[ℂ] H)
    {K : Set (SchattenOneOperator H)} (hK : K.Nonempty) :
    (separableBuresReporterTargetValueSet C A K).Nonempty := by
  obtain ⟨M, hM⟩ := hK
  exact ⟨separableBuresReporterHalfSum C M A, M, hM, rfl⟩

theorem separableBuresReporterTargetValueSet_bddAbove
    (C : SchattenOneOperator H) (A : H →L[ℂ] H)
    {K : Set (SchattenOneOperator H)} (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    BddAbove (separableBuresReporterTargetValueSet C A K) := by
  obtain ⟨Mmax, hMmax, hmax⟩ := hKcompact.exists_isMaxOn hKne
    (continuous_separableBuresReporterHalfSum_left C A).continuousOn
  refine ⟨separableBuresReporterHalfSum C Mmax A, ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact hmax hM

theorem separableBuresReporterWorstValue_nonneg
    (C : SchattenOneOperator H) (hC : (C : H →L[ℂ] H).IsPositive)
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    {K : Set (SchattenOneOperator H)} (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    0 ≤ separableBuresReporterWorstValue C A K := by
  have hb := separableBuresReporterTargetValueSet_bddAbove
    (K := K) C A hKne hKcompact
  obtain ⟨M, hM⟩ := hKne
  apply le_trans (b := separableBuresReporterHalfSum C M A)
  · unfold separableBuresReporterHalfSum
    have hsource := separableBuresTracePairing_nonneg C hC A hA.nonneg
    have htarget := separableBuresTracePairing_nonneg M (hKpositive M hM)
      (Ring.inverse A) hA.ringInverse.nonneg
    linarith
  · exact le_csSup hb ⟨M, hM, rfl⟩

theorem separableBuresDualValueSet_bddAbove
    (C : SchattenOneOperator H) {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hcont : ContinuousOn (fun M : SchattenOneOperator H =>
      operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H)) K) :
    BddAbove (separableBuresDualValueSet C K) := by
  obtain ⟨Mmax, hMmax, hmax⟩ := hKcompact.exists_isMaxOn hKne hcont
  refine ⟨operatorBuresRootFidelity (C : H →L[ℂ] H) (Mmax : H →L[ℂ] H), ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact hmax hM

theorem separableBuresPrimalValueSet_nonempty
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) :
    (separableBuresPrimalValueSet C K).Nonempty := by
  exact ⟨separableBuresReporterWorstValue C 1 K,
    1, isStrictlyPositive_one, rfl⟩

theorem separableBuresPrimalValueSet_bddBelow
    (C : SchattenOneOperator H) (hC : (C : H →L[ℂ] H).IsPositive)
    {K : Set (SchattenOneOperator H)} (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    BddBelow (separableBuresPrimalValueSet C K) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact separableBuresReporterWorstValue_nonneg C hC A hA hKne hKcompact hKpositive

theorem separableBuresPrimalCapacity_eq_dualCapacity
    [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    (C : SchattenOneOperator H) (hC : (C : H →L[ℂ] H).IsPositive)
    {V : Set H} (hVcompact : IsCompact V) (hVnonempty : V.Nonempty)
    (hVnorm : ∀ v ∈ V, ‖v‖ ≤ 1) :
    separableBuresPrimalCapacity C (separableBuresCompactTargetBody V) =
      separableBuresDualCapacity C (separableBuresCompactTargetBody V) := by
  classical
  let X : Set (SchattenOneOperator H) := separableBuresCompactTargetBody V
  let Y : Set (H →L[ℂ] H) := {A | IsStrictlyPositive A}
  let f : SchattenOneOperator H → (H →L[ℂ] H) → ℝ :=
    fun M A => -separableBuresReporterHalfSum C M A
  have hXne : X.Nonempty := separableBuresCompactTargetBody_nonempty hVnonempty
  have hXcompact : IsCompact X := separableBuresCompactTargetBody_isCompact hVcompact
  have hXconvex : Convex ℝ X := separableBuresCompactTargetBody_convex V
  have hXpositive : ∀ M ∈ X, (M : H →L[ℂ] H).IsPositive :=
    fun M hM => separableBuresCompactTargetBody_isPositive V hM
  have hYconvex : Convex ℝ Y := convex_strictlyPositiveReporters
  have hfy : ∀ A ∈ Y, LowerSemicontinuousOn (fun M => f M A) X := by
    intro A hA
    exact (continuous_separableBuresReporterHalfSum_left C A).neg.continuousOn
      |>.lowerSemicontinuousOn
  have hfy' : ∀ A ∈ Y, QuasiconvexOn ℝ X (fun M => f M A) := by
    intro A hA
    exact (concaveOn_separableBuresReporterHalfSum_left hXconvex C A).neg.quasiconvexOn
  have hfx : ∀ M ∈ X, UpperSemicontinuousOn (fun A => f M A) Y := by
    intro M hM
    exact (continuousOn_separableBuresReporterHalfSum_right C M).neg.upperSemicontinuousOn
  have hfx' : ∀ M ∈ X, QuasiconcaveOn ℝ Y (fun A => f M A) := by
    intro M hM
    exact (convexOn_separableBuresReporterHalfSum_right C M
      (hXpositive M hM)).neg.quasiconcaveOn
  have hsup_y : ∀ M ∈ X,
      IsLUB {q : ℝ | ∃ A ∈ Y, f M A = q}
        (-operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H)) := by
    intro M hM
    have hMpos := hXpositive M hM
    have hne := separableReporterValueSet_nonempty C M
    have hb := separableReporterValueSet_bddBelow C M hC hMpos
    have hglb : IsGLB (separableReporterValueSet C M)
        (operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H)) := by
      rw [← separableReporter_sInf_eq_operatorBuresRootFidelity C M hC hMpos]
      exact isGLB_csInf hne hb
    have hglb' : IsGLB
        {q : ℝ | ∃ A ∈ Y, separableBuresReporterHalfSum C M A = q}
        (operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H)) := by
      simpa [separableReporterValueSet, Y, eq_comm] using hglb
    have hneg := GaloisForLFunctions.HTGeometry.finiteBuresIsLUB_neg_functionValues_of_isGLB hglb'
    simpa [f] using hneg
  have hCroot : (CFC.sqrt (C : H →L[ℂ] H)).IsHilbertSchmidt :=
    positiveSchattenOne_sqrt_isHilbertSchmidt C hC
  have hdualCont := continuousOn_operatorBuresRootFidelity_compactTargetBody
    hVnorm (C : H →L[ℂ] H) hCroot
  have hdualBdd := separableBuresDualValueSet_bddAbove
    (K := X) C hXne hXcompact (by simpa only [X] using hdualCont)
  have hinf_sup : IsGLB
      {q : ℝ | ∃ M ∈ X,
        -operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H) = q}
      (-separableBuresDualCapacity C X) := by
    have hlub : IsLUB (separableBuresDualValueSet C X)
        (separableBuresDualCapacity C X) := by
      exact isLUB_csSup (separableBuresDualValueSet_nonempty C hXne) hdualBdd
    have hlub' : IsLUB
        {q : ℝ | ∃ M ∈ X,
          operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H) = q}
        (separableBuresDualCapacity C X) := by
      simpa [separableBuresDualValueSet, eq_comm] using hlub
    have hneg := GaloisForLFunctions.HTGeometry.finiteBuresIsGLB_neg_functionValues_of_isLUB hlub'
    simpa [separableBuresDualCapacity, separableBuresDualValueSet] using hneg
  have hinf_x : ∀ A ∈ Y,
      IsGLB {q : ℝ | ∃ M ∈ X, f M A = q}
        (-separableBuresReporterWorstValue C A X) := by
    intro A hA
    have hlub : IsLUB (separableBuresReporterTargetValueSet C A X)
        (separableBuresReporterWorstValue C A X) := by
      exact isLUB_csSup
        (separableBuresReporterTargetValueSet_nonempty C A hXne)
        (separableBuresReporterTargetValueSet_bddAbove C A hXne hXcompact)
    have hlub' : IsLUB
        {q : ℝ | ∃ M ∈ X, separableBuresReporterHalfSum C M A = q}
        (separableBuresReporterWorstValue C A X) := by
      simpa [separableBuresReporterTargetValueSet, eq_comm] using hlub
    have hneg := GaloisForLFunctions.HTGeometry.finiteBuresIsGLB_neg_functionValues_of_isLUB hlub'
    simpa [f, separableBuresReporterTargetValueSet] using hneg
  have hprimalBdd := separableBuresPrimalValueSet_bddBelow
    (K := X) C hC hXne hXcompact hXpositive
  have hsup_inf : IsLUB
      {q : ℝ | ∃ A ∈ Y, -separableBuresReporterWorstValue C A X = q}
      (-separableBuresPrimalCapacity C X) := by
    have hglb : IsGLB (separableBuresPrimalValueSet C X)
        (separableBuresPrimalCapacity C X) := by
      exact isGLB_csInf (separableBuresPrimalValueSet_nonempty C X) hprimalBdd
    have hglb' : IsGLB
        {q : ℝ | ∃ A ∈ Y, separableBuresReporterWorstValue C A X = q}
        (separableBuresPrimalCapacity C X) := by
      simpa [separableBuresPrimalValueSet, Y, eq_comm] using hglb
    have hneg := GaloisForLFunctions.HTGeometry.finiteBuresIsLUB_neg_functionValues_of_isGLB hglb'
    simpa [separableBuresPrimalCapacity, separableBuresPrimalValueSet] using hneg
  have hminimax : -separableBuresDualCapacity C X =
      -separableBuresPrimalCapacity C X := by
    exact Sion.minimax hXne hXcompact hfy hfy' hYconvex hfx hfx'
      hXconvex
      (fun M => -operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H))
      hsup_y (-separableBuresDualCapacity C X) hinf_sup
      (fun A => -separableBuresReporterWorstValue C A X) hinf_x
      (-separableBuresPrimalCapacity C X) hsup_inf
  change separableBuresPrimalCapacity C X = separableBuresDualCapacity C X
  linarith

def separableBuresTargetPairingValueSet
    (A : H →L[ℂ] H) (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ M ∈ K, q = separableBuresTracePairing M (Ring.inverse A)}

def separableBuresTargetMaximum
    (A : H →L[ℂ] H) (K : Set (SchattenOneOperator H)) : ℝ :=
  sSup (separableBuresTargetPairingValueSet A K)

theorem separableBuresTargetPairingValueSet_nonempty
    (A : H →L[ℂ] H) {K : Set (SchattenOneOperator H)} (hKne : K.Nonempty) :
    (separableBuresTargetPairingValueSet A K).Nonempty := by
  obtain ⟨M, hM⟩ := hKne
  exact ⟨separableBuresTracePairing M (Ring.inverse A), M, hM, rfl⟩

theorem separableBuresTargetPairingValueSet_bddAbove
    (A : H →L[ℂ] H) {K : Set (SchattenOneOperator H)} (hKcompact : IsCompact K) :
    BddAbove (separableBuresTargetPairingValueSet A K) := by
  have hcont := continuous_separableBuresTracePairing_left (Ring.inverse A)
  have himage := hKcompact.image hcont
  obtain ⟨B, hB⟩ := himage.bddAbove
  refine ⟨B, ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact hB ⟨M, hM, rfl⟩

theorem exists_separableBuresTargetPairing_eq_maximum
    (A : H →L[ℂ] H) {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    ∃ M ∈ K, separableBuresTargetMaximum A K =
      separableBuresTracePairing M (Ring.inverse A) := by
  obtain ⟨M, hM, hmax⟩ := hKcompact.exists_isMaxOn hKne
    (continuous_separableBuresTracePairing_left (Ring.inverse A)).continuousOn
  refine ⟨M, hM, ?_⟩
  have hlub : IsLUB (separableBuresTargetPairingValueSet A K)
      (separableBuresTracePairing M (Ring.inverse A)) := by
    have hraw := hmax.isLUB hM
    simpa [separableBuresTargetPairingValueSet, eq_comm] using hraw
  unfold separableBuresTargetMaximum
  exact (isLUB_csSup (separableBuresTargetPairingValueSet_nonempty A hKne)
    (separableBuresTargetPairingValueSet_bddAbove A hKcompact)).unique hlub

theorem separableBuresTargetMaximum_nonneg
    {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    {K : Set (SchattenOneOperator H)} (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    0 ≤ separableBuresTargetMaximum A K := by
  obtain ⟨M, hM, hmax⟩ :=
    exists_separableBuresTargetPairing_eq_maximum A hKne hKcompact
  rw [hmax]
  exact separableBuresTracePairing_nonneg M (hKpositive M hM)
    (Ring.inverse A) hA.ringInverse.nonneg

theorem separableBuresReporterWorstValue_eq_halfSumMaximum
    (C : SchattenOneOperator H) (A : H →L[ℂ] H)
    {K : Set (SchattenOneOperator H)} (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    separableBuresReporterWorstValue C A K =
      (separableBuresTracePairing C A + separableBuresTargetMaximum A K) / 2 := by
  obtain ⟨Mmax, hMmax, hmax⟩ :=
    exists_separableBuresTargetPairing_eq_maximum A hKne hKcompact
  unfold separableBuresReporterWorstValue
  apply le_antisymm
  · apply csSup_le (separableBuresReporterTargetValueSet_nonempty C A hKne)
    rintro q ⟨M, hM, rfl⟩
    have hle : separableBuresTracePairing M (Ring.inverse A) ≤
        separableBuresTargetMaximum A K :=
      le_csSup (separableBuresTargetPairingValueSet_bddAbove A hKcompact)
        ⟨M, hM, rfl⟩
    unfold separableBuresReporterHalfSum
    linarith
  · apply le_csSup
      (separableBuresReporterTargetValueSet_bddAbove C A hKne hKcompact)
    refine ⟨Mmax, hMmax, ?_⟩
    unfold separableBuresReporterHalfSum
    rw [hmax]

theorem ringInverse_real_smul
    {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    {c : ℝ} (hc : 0 < c) :
    Ring.inverse (c • A) = c⁻¹ • Ring.inverse A := by
  have hca : IsUnit (c • A) := (hA.smul hc).isUnit
  apply hca.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ hca]
  symm
  change (c • A) * (c⁻¹ • Ring.inverse A) = 1
  rw [smul_mul_smul, Ring.mul_inverse_cancel A hA.isUnit]
  rw [mul_inv_cancel₀ hc.ne', one_smul]

theorem separableBuresTargetMaximum_real_smul
    {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    {c : ℝ} (hc : 0 < c) {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    separableBuresTargetMaximum (c • A) K =
      c⁻¹ * separableBuresTargetMaximum A K := by
  unfold separableBuresTargetMaximum
  apply le_antisymm
  · apply csSup_le (separableBuresTargetPairingValueSet_nonempty (c • A) hKne)
    rintro q ⟨M, hM, rfl⟩
    rw [ringInverse_real_smul hA hc,
      separableBuresTracePairing_real_smul_right]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (separableBuresTargetPairingValueSet_bddAbove A hKcompact)
        ⟨M, hM, rfl⟩) (inv_nonneg.mpr hc.le)
  · obtain ⟨M, hM, hmax⟩ :=
      exists_separableBuresTargetPairing_eq_maximum A hKne hKcompact
    rw [show sSup (separableBuresTargetPairingValueSet A K) =
      separableBuresTracePairing M (Ring.inverse A) from hmax]
    rw [← separableBuresTracePairing_real_smul_right c⁻¹ M (Ring.inverse A),
      ← ringInverse_real_smul hA hc]
    exact le_csSup
      (separableBuresTargetPairingValueSet_bddAbove (c • A) hKcompact)
      ⟨M, hM, rfl⟩

theorem separableBuresHalfSumMaximum_real_smul
    (C : SchattenOneOperator H) {A : H →L[ℂ] H}
    (hA : IsStrictlyPositive A) {c : ℝ} (hc : 0 < c)
    {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    (separableBuresTracePairing C (c • A) +
        separableBuresTargetMaximum (c • A) K) / 2 =
      (c * separableBuresTracePairing C A +
        c⁻¹ * separableBuresTargetMaximum A K) / 2 := by
  rw [separableBuresTracePairing_real_smul_right,
    separableBuresTargetMaximum_real_smul hA hc hKne hKcompact]

def separableBuresHalfSumMaximumValueSet
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ A : H →L[ℂ] H, IsStrictlyPositive A ∧
    q = (separableBuresTracePairing C A +
      separableBuresTargetMaximum A K) / 2}

def separableBuresRootProductValueSet
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ A : H →L[ℂ] H, IsStrictlyPositive A ∧
    q = Real.sqrt (separableBuresTracePairing C A *
      separableBuresTargetMaximum A K)}

def separableBuresProductValueSet
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : Set ℝ :=
  {q | ∃ A : H →L[ℂ] H, IsStrictlyPositive A ∧
    q = separableBuresTracePairing C A * separableBuresTargetMaximum A K}

def separableBuresProductCapacity
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) : ℝ :=
  sInf (separableBuresProductValueSet C K)

theorem separableBuresPrimalCapacity_eq_halfSumMaximumInfimum
    (C : SchattenOneOperator H) {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K) :
    separableBuresPrimalCapacity C K =
      sInf (separableBuresHalfSumMaximumValueSet C K) := by
  unfold separableBuresPrimalCapacity separableBuresPrimalValueSet
  congr 2
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA,
      separableBuresReporterWorstValue_eq_halfSumMaximum C A hKne hKcompact⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA,
      (separableBuresReporterWorstValue_eq_halfSumMaximum C A hKne hKcompact).symm⟩

theorem separableBuresHalfSumMaximumValueSet_nonempty
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) :
    (separableBuresHalfSumMaximumValueSet C K).Nonempty := by
  exact ⟨(separableBuresTracePairing C 1 +
    separableBuresTargetMaximum 1 K) / 2,
    1, isStrictlyPositive_one, rfl⟩

theorem separableBuresHalfSumMaximumValueSet_bddBelow
    {C : SchattenOneOperator H} (hC : (C : H →L[ℂ] H).IsPositive)
    {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    BddBelow (separableBuresHalfSumMaximumValueSet C K) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  have hx := separableBuresTracePairing_nonneg C hC A hA.nonneg
  have hy := separableBuresTargetMaximum_nonneg hA hKne hKcompact hKpositive
  linarith

theorem separableBuresRootProductValueSet_nonempty
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) :
    (separableBuresRootProductValueSet C K).Nonempty := by
  exact ⟨Real.sqrt (separableBuresTracePairing C 1 *
    separableBuresTargetMaximum 1 K), 1, isStrictlyPositive_one, rfl⟩

theorem separableBuresRootProductValueSet_bddBelow
    (C : SchattenOneOperator H) (K : Set (SchattenOneOperator H)) :
    BddBelow (separableBuresRootProductValueSet C K) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact Real.sqrt_nonneg _

theorem separableBuresSInf_halfSum_eq_sInf_rootProduct
    {C : SchattenOneOperator H} (hC : (C : H →L[ℂ] H).IsPositive)
    {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    sInf (separableBuresHalfSumMaximumValueSet C K) =
      sInf (separableBuresRootProductValueSet C K) := by
  let S := separableBuresHalfSumMaximumValueSet C K
  let R := separableBuresRootProductValueSet C K
  have hSne : S.Nonempty := separableBuresHalfSumMaximumValueSet_nonempty C K
  have hSb : BddBelow S := separableBuresHalfSumMaximumValueSet_bddBelow
    hC hKne hKcompact hKpositive
  have hRne : R.Nonempty := separableBuresRootProductValueSet_nonempty C K
  have hRb : BddBelow R := separableBuresRootProductValueSet_bddBelow C K
  apply le_antisymm
  · apply le_csInf hRne
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    let x := separableBuresTracePairing C A
    let y := separableBuresTargetMaximum A K
    have hx : 0 ≤ x := separableBuresTracePairing_nonneg C hC A hA.nonneg
    have hy : 0 ≤ y :=
      separableBuresTargetMaximum_nonneg hA hKne hKcompact hKpositive
    have hsubset : finiteBuresScaleHalfSet x y ⊆ S := by
      rintro q ⟨c, hc, rfl⟩
      refine ⟨c • A, hA.smul hc, ?_⟩
      exact (separableBuresHalfSumMaximum_real_smul C hA hc hKne hKcompact).symm
    calc
      sInf S ≤ sInf (finiteBuresScaleHalfSet x y) := by
        apply le_csInf (finiteBuresScaleHalfSet_nonempty x y)
        intro q hq
        exact csInf_le hSb (hsubset hq)
      _ = Real.sqrt (x * y) := finiteBuresSInf_scaleHalfSet_eq_sqrt_mul hx hy
  · apply le_csInf hSne
    intro q hq
    rcases hq with ⟨A, hA, rfl⟩
    have hx := separableBuresTracePairing_nonneg C hC A hA.nonneg
    have hy := separableBuresTargetMaximum_nonneg hA hKne hKcompact hKpositive
    have hroot : Real.sqrt (separableBuresTracePairing C A *
        separableBuresTargetMaximum A K) ∈ R := ⟨A, hA, rfl⟩
    exact (csInf_le hRb hroot).trans
      (by simpa using (finiteBuresSqrt_mul_le_scaled_half hx hy
        (show (0 : ℝ) < 1 by norm_num)))

theorem separableBuresProductValueSet_eq_sq_image_rootProductValueSet
    {C : SchattenOneOperator H} (hC : (C : H →L[ℂ] H).IsPositive)
    {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    separableBuresProductValueSet C K =
      (fun r : ℝ => r ^ 2) '' separableBuresRootProductValueSet C K := by
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Real.sqrt (separableBuresTracePairing C A *
      separableBuresTargetMaximum A K), ⟨A, hA, rfl⟩, ?_⟩
    exact Real.sq_sqrt (mul_nonneg
      (separableBuresTracePairing_nonneg C hC A hA.nonneg)
      (separableBuresTargetMaximum_nonneg hA hKne hKcompact hKpositive))
  · rintro ⟨r, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨A, hA, ?_⟩
    exact Real.sq_sqrt (mul_nonneg
      (separableBuresTracePairing_nonneg C hC A hA.nonneg)
      (separableBuresTargetMaximum_nonneg hA hKne hKcompact hKpositive))

theorem separableBuresSInf_product_eq_sq_sInf_rootProduct
    {C : SchattenOneOperator H} (hC : (C : H →L[ℂ] H).IsPositive)
    {K : Set (SchattenOneOperator H)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive) :
    sInf (separableBuresProductValueSet C K) =
      sInf (separableBuresRootProductValueSet C K) ^ 2 := by
  let R := separableBuresRootProductValueSet C K
  have hRne : R.Nonempty := separableBuresRootProductValueSet_nonempty C K
  have hRb : BddBelow R := separableBuresRootProductValueSet_bddBelow C K
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
  rw [separableBuresProductValueSet_eq_sq_image_rootProductValueSet
    hC hKne hKcompact hKpositive]
  exact hmap.symm

/-- Exact separable-Hilbert compact-target Bures product minimax law. -/
theorem separableBuresProductCapacity_eq_dualCapacity_sq
    [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    {C : SchattenOneOperator H} (hC : (C : H →L[ℂ] H).IsPositive)
    {V : Set H}
    (hVcompact : IsCompact V) (hVnonempty : V.Nonempty)
    (hVnorm : ∀ v ∈ V, ‖v‖ ≤ 1) :
    separableBuresProductCapacity C (separableBuresCompactTargetBody V) =
      separableBuresDualCapacity C (separableBuresCompactTargetBody V) ^ 2 := by
  let K := separableBuresCompactTargetBody V
  have hKne : K.Nonempty := separableBuresCompactTargetBody_nonempty hVnonempty
  have hKcompact : IsCompact K :=
    separableBuresCompactTargetBody_isCompact hVcompact
  have hKpositive : ∀ M ∈ K, (M : H →L[ℂ] H).IsPositive :=
    fun M hM => separableBuresCompactTargetBody_isPositive V hM
  unfold separableBuresProductCapacity
  rw [separableBuresSInf_product_eq_sq_sInf_rootProduct
    hC hKne hKcompact hKpositive]
  rw [← separableBuresSInf_halfSum_eq_sInf_rootProduct
    hC hKne hKcompact hKpositive]
  rw [← separableBuresPrimalCapacity_eq_halfSumMaximumInfimum
    C hKne hKcompact]
  rw [separableBuresPrimalCapacity_eq_dualCapacity
    C hC hVcompact hVnonempty hVnorm]


end RHTower

