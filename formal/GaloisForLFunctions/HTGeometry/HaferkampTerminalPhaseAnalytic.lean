import GaloisForLFunctions.HTGeometry.HaferkampTerminalBlockData
import Mathlib.Analysis.Matrix.Normed

/-!
# Analytic terminal phase paths

The explicit determinant-one `I ⊗ Z` phase path is real analytic in the
finite matrix operator norm. This supplies the analytic input for the
Appendix-B low-rank null-locus argument.
-/

open scoped Matrix.Norms.Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Each diagonal phase eigenvalue is real analytic. -/
theorem analyticAt_terminalPauliPhaseEigenvalue
    (t : ℝ) (x : Bool × Bool) :
    AnalyticAt ℝ (fun s : ℝ => terminalPauliPhaseEigenvalue s x) t := by
  unfold terminalPauliPhaseEigenvalue
  split
  · let mulNegI : ℂ →L[ℂ] ℂ :=
      (ContinuousLinearMap.lsmul ℂ ℂ) (-Complex.I)
    have hcomplex : AnalyticAt ℂ
        (fun z : ℂ => Complex.exp (-Complex.I * z)) (t : ℂ) := by
      have hlin : AnalyticAt ℂ (fun z : ℂ => mulNegI z) (t : ℂ) :=
        mulNegI.analyticAt _
      simpa [Function.comp_def, mulNegI, smul_eq_mul] using hlin.cexp
    have hreal : AnalyticAt ℝ
        (fun z : ℂ => Complex.exp (-Complex.I * z)) (t : ℂ) :=
      hcomplex.restrictScalars
    have hofReal : AnalyticAt ℝ (fun s : ℝ => (s : ℂ)) t := by
      convert Complex.ofRealCLM.analyticAt t using 1
      ext s
      rfl
    simpa [Function.comp_def] using hreal.comp hofReal
  · let mulI : ℂ →L[ℂ] ℂ :=
      (ContinuousLinearMap.lsmul ℂ ℂ) Complex.I
    have hcomplex : AnalyticAt ℂ
        (fun z : ℂ => Complex.exp (Complex.I * z)) (t : ℂ) := by
      have hlin : AnalyticAt ℂ (fun z : ℂ => mulI z) (t : ℂ) :=
        mulI.analyticAt _
      simpa [Function.comp_def, mulI, smul_eq_mul] using hlin.cexp
    have hreal : AnalyticAt ℝ
        (fun z : ℂ => Complex.exp (Complex.I * z)) (t : ℂ) :=
      hcomplex.restrictScalars
    have hofReal : AnalyticAt ℝ (fun s : ℝ => (s : ℂ)) t := by
      convert Complex.ofRealCLM.analyticAt t using 1
      ext s
      rfl
    simpa [Function.comp_def] using hreal.comp hofReal

/-- The literal `I ⊗ Z` phase matrix is real analytic. -/
theorem analyticAt_terminalPauliPhaseMatrix
    (t : ℝ) : AnalyticAt ℝ terminalPauliPhaseMatrix t := by
  let diagonalCLM : (Bool × Bool → ℂ) →L[ℂ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    (Matrix.diagonalLinearMap (Bool × Bool) ℂ ℂ).toContinuousLinearMap
  have hvector : AnalyticAt ℝ
      (fun s : ℝ => fun x : Bool × Bool => terminalPauliPhaseEigenvalue s x) t :=
    AnalyticAt.pi fun x => analyticAt_terminalPauliPhaseEigenvalue t x
  have hdiag : AnalyticAt ℝ (fun v : Bool × Bool → ℂ => diagonalCLM v)
      (fun x : Bool × Bool => terminalPauliPhaseEigenvalue t x) :=
    (diagonalCLM.restrictScalars ℝ).analyticAt _
  have hcomp := hdiag.comp hvector
  convert hcomp using 1
  funext s
  ext x y
  simp [diagonalCLM, terminalPauliPhaseMatrix]

/-- Left multiplication by the analytic terminal phase makes every local
terminal `SU(4)` gate path real analytic. -/
theorem analyticAt_terminalPauliGatePath
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      (terminalPauliGatePath U s : Matrix (Bool × Bool) (Bool × Bool) ℂ)) t := by
  rw [show (fun s : ℝ =>
      (terminalPauliGatePath U s : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      (fun s : ℝ => terminalPauliPhaseMatrix s *
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) by
        funext s
        rfl]
  exact (analyticAt_terminalPauliPhaseMatrix t).mul analyticAt_const

/-- The arbitrary two-qubit matrix lift as a complex continuous linear map. -/
def twoQubitLiftMatrixCLM
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ →L[ℂ]
      Matrix (Q → Bool) (Q → Bool) ℂ :=
  (show Matrix (Bool × Bool) (Bool × Bool) ℂ →ₗ[ℂ]
      Matrix (Q → Bool) (Q → Bool) ℂ from
    { toFun := twoQubitLiftMatrix a b hab
      map_add' := by
        intro M N
        ext x y
        simp [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.kronecker, add_mul]
      map_smul' := by
        intro c M
        ext x y
        simp [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.kronecker,
          Matrix.smul_apply, mul_assoc] }).toContinuousLinearMap

/-- Lifting an analytic terminal local phase to distinct register coordinates
preserves real analyticity. -/
theorem analyticAt_twoQubitLift_terminalPauliGatePath
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      (twoQubitLift a b hab (terminalPauliGatePath U s) :
        Matrix (Q → Bool) (Q → Bool) ℂ)) t := by
  let liftCLM := twoQubitLiftMatrixCLM a b hab
  have hlocal := analyticAt_terminalPauliGatePath U t
  have hlift : AnalyticAt ℝ (fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ =>
      liftCLM M) (terminalPauliGatePath U t :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) :=
    (liftCLM.restrictScalars ℝ).analyticAt _
  have hcomp := AnalyticAt.comp
    (f := fun s : ℝ =>
      (terminalPauliGatePath U s : Matrix (Bool × Bool) (Bool × Bool) ℂ))
    (g := fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ => liftCLM M)
    hlift hlocal
  convert hcomp using 1
  funext s
  rfl

namespace BackwardsLightCone

/-- A terminal-aware block’s lifted matrix word splits at its moving terminal
phase gate. -/
theorem TerminalBlockData.phaseLiftedBlock_decomp
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) (t : ℝ) :
    List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (List.zipWith totalTwoQubitLift edges
        (block.prefixGates ++ terminalPauliGatePath block.terminalGate t ::
          block.suffixGates)) =
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates) ++
      (totalTwoQubitLift (cone.mergePlan.terminal, root)
        (terminalPauliGatePath block.terminalGate t) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift block.suffixEdges block.suffixGates) := by
  rcases block with ⟨gates, terminalGate, prefixEdges, suffixEdges, prefixGates, suffixGates,
    gatesLength, gatesClifford, edgesDecomp, gatesDecomp, prefixLength, suffixLength,
    suffixIdentity, transportCoeff, transportCoeffNonzero, transport, curveLength, curveZero,
    contractionDerivative⟩
  let terminalEdge : Fin n × Fin n := (cone.mergePlan.terminal, root)
  have hedges : edges = prefixEdges ++ terminalEdge :: suffixEdges := by
    simpa only [terminalEdge] using edgesDecomp
  change List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (List.zipWith totalTwoQubitLift edges
        (prefixGates ++ terminalPauliGatePath terminalGate t :: suffixGates)) =
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift prefixEdges prefixGates) ++
      (totalTwoQubitLift terminalEdge (terminalPauliGatePath terminalGate t) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift suffixEdges suffixGates)
  change edges = prefixEdges ++ terminalEdge :: suffixEdges at hedges
  rw [hedges, List.zipWith_append prefixLength.symm]
  simp only [List.map_append, List.zipWith, List.map_cons]

/-- The terminal local phase lift through a BLC root-targeting edge is real
analytic. -/
theorem analyticAt_totalTwoQubitLift_terminalPauliGatePath
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      (totalTwoQubitLift (cone.mergePlan.terminal, root)
        (terminalPauliGatePath U s) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) t := by
  rw [show (fun s : ℝ =>
      (totalTwoQubitLift (cone.mergePlan.terminal, root)
        (terminalPauliGatePath U s) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) =
      (fun s : ℝ =>
        (twoQubitLift cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root
          (terminalPauliGatePath U s) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) by
        funext s
        exact congrArg (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
          (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          (totalTwoQubitLift_eq_twoQubitLift
            (cone.mergePlan.terminal, root) cone.mergePlan.terminal_ne_root
            (terminalPauliGatePath U s))]
  exact analyticAt_twoQubitLift_terminalPauliGatePath
    cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root U t

/-- The full physical contraction of one terminal-aware block is real
analytic in its terminal phase parameter. -/
theorem TerminalBlockData.analyticAt_phaseContraction
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift edges
          (block.prefixGates ++ terminalPauliGatePath block.terminalGate s ::
            block.suffixGates))).reverse.prod) t := by
  let prefixMatrices := List.map
    (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates)
  let suffixMatrices := List.map
    (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (List.zipWith totalTwoQubitLift block.suffixEdges block.suffixGates)
  rw [show (fun s : ℝ =>
      (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift edges
          (block.prefixGates ++ terminalPauliGatePath block.terminalGate s ::
            block.suffixGates))).reverse.prod) =
      (fun s : ℝ => suffixMatrices.reverse.prod *
        (totalTwoQubitLift (cone.mergePlan.terminal, root)
          (terminalPauliGatePath block.terminalGate s) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * prefixMatrices.reverse.prod) by
        funext s
        rw [block.phaseLiftedBlock_decomp s, List.reverse_append, List.prod_append,
          List.reverse_cons, List.prod_append]
        simp [prefixMatrices, suffixMatrices, Matrix.mul_assoc]]
  exact (analyticAt_const.mul
    (analyticAt_totalTwoQubitLift_terminalPauliGatePath block.terminalGate t)).mul
      analyticAt_const

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
