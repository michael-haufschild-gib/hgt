import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanRank

/-!
# Right-translated terminal-hybrid rank witnesses

The Appendix-B terminal phase paths are stable under fixed right
multiplication of every local gate.  This module lifts the terminal-hybrid
analytic contraction and its rank witness to every such translate, which is
the orientation needed for the final Haar averaging argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix.Norms.L2Operator

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- A terminal phase commutes with a fixed right multiplication by associativity. -/
theorem terminalPauliGatePath_mul_right
    (V U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) (t : ℝ) :
    terminalPauliGatePath V t * U = terminalPauliGatePath (V * U) t := by
  apply Subtype.ext
  simp only [terminalPauliGatePath]
  exact Matrix.mul_assoc _ _ _

namespace TwoQubitArchitecture

/-- Terminal-hybrid architecture contraction after a fixed right multiplier at
every local gate. -/
def terminalHybridEuclideanRightContraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    (Fin R → terminalHybridEuclideanCoordinates N) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun z => (List.ofFn fun r => twoQubitLiftMatrix
    (A.sites r).1 (A.sites r).2 (A.distinct r)
    ((terminalHybridEuclideanGate N (z r) * U r :
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
      Matrix (Bool × Bool) (Bool × Bool) ℂ)).reverse.prod

/-- The right-translated terminal-hybrid contraction is analytic everywhere. -/
theorem analyticAt_terminalHybridEuclideanRightContraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (z : Fin R → terminalHybridEuclideanCoordinates N) :
    AnalyticAt ℝ (A.terminalHybridEuclideanRightContraction N U) z := by
  unfold terminalHybridEuclideanRightContraction
  refine analyticAt_reverse_prod_ofFn n R
    (fun r w => twoQubitLiftMatrix (A.sites r).1 (A.sites r).2 (A.distinct r)
      ((terminalHybridEuclideanGate N w * U r :
        Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
        Matrix (Bool × Bool) (Bool × Bool) ℂ)) z ?_
  intro r x
  let M := (twoQubitLiftMatrixCLM (A.sites r).1 (A.sites r).2
    (A.distinct r)).restrictScalars ℝ
  let Q := boolTwoQubitMatrixRightMulCLM (specialUnitaryToUnitary (U r))
  have hQ : AnalyticAt ℝ (fun w : terminalHybridEuclideanCoordinates N =>
      Q (terminalHybridEuclideanGate N w :
        Matrix (Bool × Bool) (Bool × Bool) ℂ)) x :=
    Q.analyticAt _ |>.comp (analyticAt_terminalHybridEuclideanGate_coe N x)
  have hM : AnalyticAt ℝ (fun w : terminalHybridEuclideanCoordinates N =>
      M (Q (terminalHybridEuclideanGate N w :
        Matrix (Bool × Bool) (Bool × Bool) ℂ))) x :=
    M.analyticAt _ |>.comp hQ
  simpa [M, Q, twoQubitLiftMatrixCLM, specialUnitaryToUnitary,
    boolTwoQubitMatrixRightMulCLM_apply] using hM

/-- Along a terminal-coordinate embedding, a right-translated contraction is
the same explicit terminal Pauli word as in Appendix B. -/
theorem terminalHybridEuclideanRightContraction_eq_phaseWord
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ)
    (U gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N)
    (p : Fin R → ℝ)
    (hz : (fun r => boolTwoQubitHybridEuclideanGate N (z r) * U r) = gates) :
    A.terminalHybridEuclideanRightContraction N U
      (A.terminalHybridCoordinateAssignment N z p) =
      (List.ofFn fun r => twoQubitLiftMatrix
        (A.sites r).1 (A.sites r).2 (A.distinct r)
        (terminalPauliGatePath (gates r) (p r))).reverse.prod := by
  unfold terminalHybridEuclideanRightContraction terminalHybridCoordinateAssignment
  congr 1
  apply congrArg List.reverse
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    rw [List.get_ofFn, List.get_ofFn]
    let r : Fin R := ⟨k, by simpa using hk₁⟩
    change twoQubitLiftMatrix (A.sites r).1 (A.sites r).2 (A.distinct r)
      ((terminalHybridEuclideanGate N
        (terminalHybridEuclideanEmbed N (p r) (z r)) * U r :
        Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) = _
    rw [show terminalHybridEuclideanGate N
      (terminalHybridEuclideanEmbed N (p r) (z r)) =
        terminalPauliGatePath (boolTwoQubitHybridEuclideanGate N (z r)) (p r) by rfl,
      terminalPauliGatePath_mul_right,
      show boolTwoQubitHybridEuclideanGate N (z r) * U r = gates r by
        exact congrFun hz r]
    simp [r]

/-- The right-translated terminal contraction agrees with the architecture
contraction of its terminal Pauli gate paths. -/
theorem terminalHybridEuclideanRightContraction_eq_phaseContraction
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ)
    (U gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N)
    (p : Fin R → ℝ)
    (hz : (fun r => boolTwoQubitHybridEuclideanGate N (z r) * U r) = gates) :
    A.terminalHybridEuclideanRightContraction N U
      (A.terminalHybridCoordinateAssignment N z p) =
      (A.contraction (fun r => terminalPauliGatePath (gates r) (p r)) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  rw [A.terminalHybridEuclideanRightContraction_eq_phaseWord N U gates z p hz]
  unfold contraction gateLift
  rw [← List.map_coe_unitary_reverse_prod]
  congr 1
  apply congrArg List.reverse
  rw [List.map_ofFn]
  congr 1

end TwoQubitArchitecture

namespace BackwardsLightCone

/-- The flattened terminal assembly is exactly the terminal phase word after
any fixed right translate of the local gate tuple. -/
theorem TerminalBlockPrefixAssembly.terminalHybridEuclideanRightContraction_eq_terminalPhaseContraction
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (N : ℕ) (U : Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N)
    (hz : (fun r => boolTwoQubitHybridEuclideanGate N (z r) * U r) =
      assembly.flattenedGateParameters)
    (x : Fin labels.length → ℝ) :
    assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U
      (assembly.flattenedArchitecture.terminalHybridCoordinateAssignment N z
        (assembly.terminalPhaseScalarParameters x)) =
      (assembly.terminalPhaseLiftedWord x).reverse.prod := by
  rw [TwoQubitArchitecture.terminalHybridEuclideanRightContraction_eq_phaseContraction
    assembly.flattenedArchitecture N U assembly.flattenedGateParameters z
    (assembly.terminalPhaseScalarParameters x) hz]
  rw [assembly.terminalPhaseGateParameters_eq x]
  unfold flattenedArchitecture
  rw [← edgeListBlockContraction_eq_ofEdgeList_contraction
    assembly.flattenedEdgeWord assembly.flattenedEdgeWord_distinct
    (assembly.terminalPhaseGateWord x)
    (assembly.terminalPhaseGateWord_length_eq_flattenedEdgeWord_length x)]
  unfold edgeListBlockContraction haferkampGateWordReverseProduct
  rw [assembly.terminalPhaseLiftedWord_eq_zipWith_flattenedEdgeWord x]
  exact List.map_coe_unitary_reverse_prod _ |>.symm

/-- The Appendix-B independent terminal tangents remain a derivative-rank
witness after every fixed right translate of all local gates. -/
theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalHybridEuclideanRightContraction_fderiv
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i)))
    (N : ℕ) (U : Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N)
    (hz : (fun r => boolTwoQubitHybridEuclideanGate N (z r) * U r) =
      assembly.flattenedGateParameters) :
    labels.length ≤ Module.finrank ℝ
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
        (assembly.terminalHybridCoordinateEmbedding N z 0)).range := by
  let E := assembly.terminalHybridCoordinateEmbedding N z
  let G := assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U
  let F : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod
  have hE : DifferentiableAt ℝ E 0 :=
    assembly.differentiable_terminalHybridCoordinateEmbedding N z 0
  have hG : DifferentiableAt ℝ G (E 0) :=
    (assembly.flattenedArchitecture.analyticAt_terminalHybridEuclideanRightContraction N U
      (E 0)).differentiableAt
  have hEq : (fun x => G (E x)) = F := by
    funext x
    exact assembly.terminalHybridEuclideanRightContraction_eq_terminalPhaseContraction
      N U z hz x
  have hCompEq : G ∘ E = F := by
    simpa [Function.comp_def] using hEq
  have hComp : HasFDerivAt (G ∘ E)
      ((fderiv ℝ G (E 0)).comp (fderiv ℝ E 0)) 0 :=
    HasFDerivAt.comp (f := E) (g := G) 0 hG.hasFDerivAt hE.hasFDerivAt
  have hderiv : fderiv ℝ F 0 =
      (fderiv ℝ G (E 0)).comp (fderiv ℝ E 0) := by
    have h := hComp.fderiv
    rw [hCompEq] at h
    exact h
  have hF : DifferentiableAt ℝ F 0 := by
    rw [← hCompEq]
    exact hComp.differentiableAt
  let D : (Fin labels.length → ℝ) →L[ℝ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    assembly.terminalPhaseTangentMap.toLinearMap.toContinuousLinearMap
  have hfull : HasFDerivAt F (fderiv ℝ F 0) 0 := hF.hasFDerivAt
  have haxis (i : Fin labels.length) :
      (fderiv ℝ F 0) (Pi.single i (1 : ℝ)) =
        Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    let singleCLM : ℝ →L[ℝ] (Fin labels.length → ℝ) :=
      ContinuousLinearMap.single ℝ (fun _ : Fin labels.length => ℝ) i
    have hsingle : HasFDerivAt (fun t : ℝ => Pi.single i t) singleCLM 0 := by
      change HasFDerivAt (singleCLM : ℝ → (Fin labels.length → ℝ)) singleCLM 0
      exact singleCLM.hasFDerivAt
    have hbase : HasFDerivAt F (fderiv ℝ F 0) (Pi.single i (0 : ℝ)) := by
      simpa using hfull
    have hcomp := HasFDerivAt.comp
      (f := fun t : ℝ => Pi.single i t) (g := F) 0 hbase hsingle
    let tangent : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
      Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))
    have haxisExact : HasFDerivAt
        (fun t : ℝ => F (Pi.single i t))
        (ContinuousLinearMap.toSpanSingleton ℝ tangent) 0 := by
      change HasFDerivAt
        (fun t : ℝ => (assembly.terminalPhaseLiftedWord (Pi.single i t)).reverse.prod)
        _ 0
      exact (assembly.entrywiseHasDerivAt_terminalPhaseContraction_single i).hasFDerivAt
    have hsingleDeriv : (fderiv ℝ F 0).comp singleCLM =
        ContinuousLinearMap.toSpanSingleton ℝ tangent := by
      apply hcomp.unique
      exact haxisExact
    have hvalue := congrArg (fun L : ℝ →L[ℝ]
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L 1) hsingleDeriv
    change (fderiv ℝ F 0) (Pi.single i (1 : ℝ)) = _ at hvalue
    simpa [tangent, ContinuousLinearMap.toSpanSingleton_apply] using hvalue
  have hFD : fderiv ℝ F 0 = D := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      (fderiv ℝ F 0) x = (fderiv ℝ F 0) (∑ i, Pi.single i (x i)) := by
        rw [Finset.univ_sum_single]
      _ = ∑ i, (fderiv ℝ F 0) (Pi.single i (x i)) := by rw [map_sum]
      _ = ∑ i, x i • (Complex.I •
          haferkampUnitaryListCoordinateOutput assembly.liftedWord
            (assembly.terminalIndices i)
            (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) := by
        apply Finset.sum_congr rfl
        intro i _
        have hsingle : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
          ext j
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]
        rw [hsingle, map_smul, haxis i]
      _ = D x := by rfl
  have hDsingle (i : Fin labels.length) : D (Pi.single i 1) =
      Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    simp [D, TerminalBlockPrefixAssembly.terminalPhaseTangentMap]
  have hDindependent : LinearIndependent ℝ (fun i : Fin labels.length =>
      D (Pi.single i 1)) := by
    simpa only [hDsingle] using
      assembly.linearIndependent_terminalPhaseTangents hlabels
  let values : Fin labels.length → D.range :=
    fun i => ⟨D (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩
  have hcompIndependent : LinearIndependent ℝ (D.range.subtype ∘ values) := by
    simpa [values, Function.comp_def] using hDindependent
  have hvalues : LinearIndependent ℝ values :=
    LinearIndependent.of_comp D.range.subtype hcompIndependent
  have hphase : labels.length ≤ Module.finrank ℝ D.range := by
    calc
      labels.length = (Set.range values).finrank ℝ := by
        simpa using (linearIndependent_iff_card_eq_finrank_span.mp hvalues)
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range values)) := rfl
      _ ≤ Module.finrank ℝ D.range := Submodule.finrank_le _
  calc
    labels.length ≤ Module.finrank ℝ D.range := hphase
    _ = Module.finrank ℝ (fderiv ℝ F 0).range := by rw [hFD]
    _ = Module.finrank ℝ ((fderiv ℝ G (E 0)).comp (fderiv ℝ E 0)).range := by
      rw [hderiv]
    _ ≤ Module.finrank ℝ (fderiv ℝ G (E 0)).range :=
      finrank_range_comp_right_le (fderiv ℝ E 0) (fderiv ℝ G (E 0))

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
