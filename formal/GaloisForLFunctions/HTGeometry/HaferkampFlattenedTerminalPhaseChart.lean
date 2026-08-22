import GaloisForLFunctions.HTGeometry.HaferkampFlattenedPhaseRank
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPhaseAnalytic
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Operator

/-!
# Simultaneous terminal-phase chart of a flattened BLC assembly

Each retained terminal gate receives its own real determinant-one phase
parameter.  This is the literal finite-dimensional chart subfamily used to
witness the Appendix-B rank lower bound.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The full-register matrix word obtained by varying every retained terminal
gate along its own real `SU(4)` phase coordinate. -/
def TerminalBlockPrefixAssembly.terminalPhaseLiftedWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      (Fin labels.length → ℝ) → List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
  | .nil _ => fun _ => []
  | .cons step tail => fun x =>
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift edges
          (step.block.prefixGates ++
            terminalPauliGatePath step.block.terminalGate (x 0) ::
            step.block.suffixGates)) ++
      tail.terminalPhaseLiftedWord (Fin.tail x)

/-- The simultaneous terminal-phase chart is based at the original flattened
physical matrix word. -/
theorem TerminalBlockPrefixAssembly.terminalPhaseLiftedWord_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.terminalPhaseLiftedWord 0 =
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) assembly.liftedWord := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      change List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
          (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          (List.zipWith totalTwoQubitLift edges
            (step.block.prefixGates ++
              terminalPauliGatePath step.block.terminalGate 0 ::
              step.block.suffixGates)) ++
          tail.terminalPhaseLiftedWord 0 =
        List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
          (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          (List.zipWith totalTwoQubitLift edges step.block.gates ++ tail.liftedWord)
      rw [step.block.curve_zero]
      simp only [List.map_append]
      exact congrArg (fun word =>
        List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
          (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          (List.zipWith totalTwoQubitLift edges step.block.gates) ++ word) ih

/-- Contracting the simultaneous terminal-phase chart at its origin recovers
the original flattened circuit contraction. -/
theorem TerminalBlockPrefixAssembly.terminalPhaseContraction_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    (assembly.terminalPhaseLiftedWord 0).reverse.prod =
      (assembly.liftedWord.reverse.prod : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  rw [assembly.terminalPhaseLiftedWord_zero]
  exact List.map_coe_unitary_reverse_prod assembly.liftedWord

/-- The full simultaneous terminal-phase contraction is real analytic at
every finite parameter vector. -/
theorem TerminalBlockPrefixAssembly.analyticAt_terminalPhaseContraction
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    AnalyticAt ℝ (fun y => (assembly.terminalPhaseLiftedWord y).reverse.prod) x := by
  induction assembly with
  | nil =>
      exact analyticAt_const
  | @cons pre P Ps step tail ih =>
      let tailProj : (Fin (P :: Ps).length → ℝ) →L[ℝ] (Fin Ps.length → ℝ) :=
        ContinuousLinearMap.pi fun j : Fin Ps.length =>
          ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (P :: Ps).length => ℝ) j.succ
      have htailProj : AnalyticAt ℝ
          (fun y : Fin (P :: Ps).length → ℝ => Fin.tail y) x := by
        change AnalyticAt ℝ (tailProj :
          (Fin (P :: Ps).length → ℝ) → (Fin Ps.length → ℝ)) x
        exact tailProj.analyticAt _
      have htail : AnalyticAt ℝ
          (fun y : Fin (P :: Ps).length → ℝ =>
            (tail.terminalPhaseLiftedWord (Fin.tail y)).reverse.prod) x :=
        AnalyticAt.comp
          (f := fun y : Fin (P :: Ps).length → ℝ => Fin.tail y)
          (g := fun z : Fin Ps.length → ℝ =>
            (tail.terminalPhaseLiftedWord z).reverse.prod)
          (ih (Fin.tail x)) htailProj
      have hheadBase := step.block.analyticAt_phaseContraction (x 0)
      have hheadProj : AnalyticAt ℝ
          (fun y : Fin (P :: Ps).length → ℝ => y 0) x := by
        exact (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (P :: Ps).length => ℝ) 0).analyticAt _
      have hhead : AnalyticAt ℝ
          (fun y : Fin (P :: Ps).length → ℝ =>
            (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              (List.zipWith totalTwoQubitLift edges
                (step.block.prefixGates ++
                  terminalPauliGatePath step.block.terminalGate (y 0) ::
                  step.block.suffixGates))).reverse.prod) x :=
        AnalyticAt.comp
          (f := fun y : Fin (P :: Ps).length → ℝ => y 0)
          (g := fun s : ℝ =>
            (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              (List.zipWith totalTwoQubitLift edges
                (step.block.prefixGates ++
                  terminalPauliGatePath step.block.terminalGate s ::
                  step.block.suffixGates))).reverse.prod)
          hheadBase hheadProj
      change AnalyticAt ℝ
        (fun y : Fin (P :: Ps).length → ℝ =>
          (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            (List.zipWith totalTwoQubitLift edges
              (step.block.prefixGates ++
                terminalPauliGatePath step.block.terminalGate (y 0) ::
                step.block.suffixGates)) ++
            tail.terminalPhaseLiftedWord (Fin.tail y)).reverse.prod) x
      rw [show
          (fun y : Fin (P :: Ps).length → ℝ =>
            (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              (List.zipWith totalTwoQubitLift edges
                (step.block.prefixGates ++
                  terminalPauliGatePath step.block.terminalGate (y 0) ::
                  step.block.suffixGates)) ++
              tail.terminalPhaseLiftedWord (Fin.tail y)).reverse.prod) =
          (fun y : Fin (P :: Ps).length → ℝ =>
            (tail.terminalPhaseLiftedWord (Fin.tail y)).reverse.prod *
              (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
                (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                (List.zipWith totalTwoQubitLift edges
                  (step.block.prefixGates ++
                    terminalPauliGatePath step.block.terminalGate (y 0) ::
                    step.block.suffixGates))).reverse.prod) by
              funext y
              rw [List.reverse_append, List.prod_append]]
      exact htail.mul hhead

/-- Restricting the simultaneous terminal-phase chart to one coordinate axis
is exactly the corresponding physical terminal-coordinate curve. -/
theorem TerminalBlockPrefixAssembly.terminalPhaseContraction_single_eq_terminalCoordinateCurve
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) (t : ℝ) :
    (assembly.terminalPhaseLiftedWord (Pi.single i t)).reverse.prod =
      assembly.terminalCoordinateCurve i t := by
  induction assembly generalizing t with
  | nil => exact Fin.elim0 i
  | @cons pre P Ps step tail ih =>
      refine Fin.cases ?_ ?_ i
      · have htail : Fin.tail
            (Pi.single (M := fun _ : Fin (P :: Ps).length => ℝ) 0 t) = 0 := by
          funext j
          change Pi.single (M := fun _ : Fin (P :: Ps).length => ℝ) 0 t j.succ = 0
          rw [Pi.single_apply]
          exact if_neg (Fin.succ_ne_zero j)
        let currentWord := List.zipWith totalTwoQubitLift edges step.block.gates
        let prefixWord :=
          List.zipWith totalTwoQubitLift step.block.prefixEdges step.block.prefixGates
        let suffixWord :=
          List.zipWith totalTwoQubitLift step.block.suffixEdges step.block.suffixGates
        let terminalWord := totalTwoQubitLift (cone.mergePlan.terminal, root)
          step.block.terminalGate
        have hcurrent : currentWord = prefixWord ++ terminalWord :: suffixWord := by
          exact step.block.liftedWord_decomp_at
            (cone.mergePlan.terminal, root) step.block.edges_decomp
        have hprefixLength : prefixWord.length = step.block.prefixGates.length := by
          dsimp [prefixWord]
          rw [List.length_zipWith]
          exact Nat.min_eq_right (Nat.le_of_eq step.block.prefix_length)
        unfold TerminalBlockPrefixAssembly.terminalCoordinateCurve
        rw [TerminalBlockPrefixAssembly.terminalIndices_cons_zero_val step tail,
          TerminalBlockPrefixAssembly.terminalLocalGate_cons_zero step tail]
        change (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            (List.zipWith totalTwoQubitLift edges
              (step.block.prefixGates ++
                terminalPauliGatePath step.block.terminalGate t :: step.block.suffixGates)) ++
            tail.terminalPhaseLiftedWord (Fin.tail
              (Pi.single (M := fun _ : Fin (P :: Ps).length => ℝ) 0 t))).reverse.prod =
          (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            ((currentWord ++ tail.liftedWord).take step.block.prefixGates.length) ++
            (totalTwoQubitLift (cone.mergePlan.terminal, root)
              (terminalPauliGatePath step.block.terminalGate t) :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
            List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              ((currentWord ++ tail.liftedWord).drop
                (step.block.prefixGates.length + 1))).reverse.prod
        rw [htail, tail.terminalPhaseLiftedWord_zero,
          step.block.phaseLiftedBlock_decomp]
        rw [hcurrent, List.map_take, List.map_drop]
        have hword : (prefixWord ++ terminalWord :: suffixWord) ++ tail.liftedWord =
            prefixWord ++ terminalWord :: (suffixWord ++ tail.liftedWord) := by
          simp [List.append_assoc]
        have htake : ((prefixWord ++ terminalWord :: suffixWord) ++ tail.liftedWord).take
            step.block.prefixGates.length = prefixWord := by
          rw [hword]
          calc
            (prefixWord ++ (terminalWord :: (suffixWord ++ tail.liftedWord))).take
                step.block.prefixGates.length =
                prefixWord.take step.block.prefixGates.length := by
                  apply List.take_append_of_le_length
                  exact Nat.le_of_eq hprefixLength.symm
            _ = prefixWord := by rw [← hprefixLength, List.take_length]
        have hdrop : ((prefixWord ++ terminalWord :: suffixWord) ++ tail.liftedWord).drop
            (step.block.prefixGates.length + 1) = suffixWord ++ tail.liftedWord := by
          rw [hword]
          simp [List.drop_append, hprefixLength]
        have htakeMap : (List.map
            (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            ((prefixWord ++ terminalWord :: suffixWord) ++ tail.liftedWord)).take
              step.block.prefixGates.length =
            List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) prefixWord := by
          rw [← List.map_take, htake]
        have hdropMap : (List.map
            (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            ((prefixWord ++ terminalWord :: suffixWord) ++ tail.liftedWord)).drop
              (step.block.prefixGates.length + 1) =
            List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              (suffixWord ++ tail.liftedWord) := by
          rw [← List.map_drop, hdrop]
        rw [htakeMap, hdropMap, List.map_append]
        simp [prefixWord, suffixWord, List.append_assoc]
      · intro j
        have htail : Fin.tail
            (Pi.single (M := fun _ : Fin (P :: Ps).length => ℝ) (Fin.succ j) t) =
            Pi.single (M := fun _ : Fin Ps.length => ℝ) j t := by
          funext k
          change Pi.single (M := fun _ : Fin (P :: Ps).length => ℝ)
            (Fin.succ j) t k.succ =
              Pi.single (M := fun _ : Fin Ps.length => ℝ) j t k
          rw [Pi.single_apply, Pi.single_apply]
          simp [Fin.succ_inj]
        let currentWord := List.zipWith totalTwoQubitLift edges step.block.gates
        let currentMatrices := List.map
          (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) currentWord
        have hlength : currentWord.length = step.block.gates.length := by
          dsimp [currentWord]
          rw [List.length_zipWith]
          exact Nat.min_eq_right (Nat.le_of_eq step.block.gates_length)
        have hcurve :
            (TerminalBlockPrefixAssembly.cons step tail).terminalCoordinateCurve (Fin.succ j) t =
              tail.terminalCoordinateCurve j t * currentMatrices.reverse.prod := by
          unfold TerminalBlockPrefixAssembly.terminalCoordinateCurve
          rw [TerminalBlockPrefixAssembly.terminalIndices_cons_succ_val step tail j,
            TerminalBlockPrefixAssembly.terminalLocalGate_cons_succ step tail j]
          change
            (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
                (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                ((currentWord ++ tail.liftedWord).take
                  (step.block.gates.length + (tail.terminalIndices j).1)) ++
              (totalTwoQubitLift (cone.mergePlan.terminal, root)
                (terminalPauliGatePath (tail.terminalLocalGate j) t) :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
              List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
                (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                ((currentWord ++ tail.liftedWord).drop
                  (step.block.gates.length + (tail.terminalIndices j).1 + 1))).reverse.prod =
              tail.terminalCoordinateCurve j t * currentMatrices.reverse.prod
          rw [← hlength, list_take_append_length_add]
          have hdrop : (currentWord ++ tail.liftedWord).drop
              (currentWord.length + (tail.terminalIndices j).1 + 1) =
              tail.liftedWord.drop ((tail.terminalIndices j).1 + 1) := by
            rw [List.drop_append]
            simp [Nat.add_assoc]
          rw [hdrop, List.map_append, List.append_assoc,
            List.reverse_append, List.prod_append]
          unfold TerminalBlockPrefixAssembly.terminalCoordinateCurve
          rfl
        have hhead : Pi.single (M := fun _ : Fin (P :: Ps).length => ℝ)
            (Fin.succ j) t 0 = 0 := by
          rw [Pi.single_apply]
          exact if_neg (Fin.succ_ne_zero j).symm
        unfold TerminalBlockPrefixAssembly.terminalPhaseLiftedWord
        rw [htail, hhead, terminalPauliGatePath_zero, ← step.block.gates_decomp]
        change (currentMatrices ++ tail.terminalPhaseLiftedWord (Pi.single j t)).reverse.prod =
          (TerminalBlockPrefixAssembly.cons step tail).terminalCoordinateCurve (Fin.succ j) t
        rw [List.reverse_append, List.prod_append, ih j t, hcurve]

/-- Every coordinate line of the simultaneous chart has the certified
Appendix-B tangent at its origin. -/
theorem TerminalBlockPrefixAssembly.entrywiseHasDerivAt_terminalPhaseContraction_single
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    EntrywiseMatrixHasDerivAt
      (fun t => (assembly.terminalPhaseLiftedWord (Pi.single i t)).reverse.prod)
      (Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) 0 := by
  rw [show (fun t => (assembly.terminalPhaseLiftedWord (Pi.single i t)).reverse.prod) =
      assembly.terminalCoordinateCurve i by
        funext t
        exact assembly.terminalPhaseContraction_single_eq_terminalCoordinateCurve i t]
  exact assembly.entrywiseHasDerivAt_terminalCoordinateCurve i

/-- The real Fréchet derivative of each coordinate line of the simultaneous
terminal-phase chart is its certified Appendix-B tangent. -/
theorem TerminalBlockPrefixAssembly.hasFDerivAt_terminalPhaseContraction_single
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    HasFDerivAt
      (fun t => (assembly.terminalPhaseLiftedWord (Pi.single i t)).reverse.prod)
      (ContinuousLinearMap.toSpanSingleton ℝ
        (Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2))))) 0 :=
  (assembly.entrywiseHasDerivAt_terminalPhaseContraction_single i).hasFDerivAt

/-- The phase-varying contraction of a leading terminal-aware block is
differentiable with respect to the first coordinate of a finite parameter
vector. -/
theorem TerminalBlockData.differentiableAt_phaseContraction_head
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (block : TerminalBlockData cone P) :
    DifferentiableAt ℝ
      (fun x : Fin (P :: Ps).length → ℝ =>
        (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
          (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          (List.zipWith totalTwoQubitLift edges
            (block.prefixGates ++
              terminalPauliGatePath block.terminalGate (x 0) ::
              block.suffixGates))).reverse.prod) 0 := by
  have hbase : DifferentiableAt ℝ
      (fun t : ℝ =>
        (List.zipWith (fun edge gate =>
          (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          edges
          (block.prefixGates ++ terminalPauliGatePath block.terminalGate t ::
            block.suffixGates)).reverse.prod) 0 :=
    block.contraction_derivative.hasFDerivAt.differentiableAt
  have hcoord : DifferentiableAt ℝ
      (fun x : Fin (P :: Ps).length → ℝ => x 0) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (P :: Ps).length => ℝ) 0) :
      (Fin (P :: Ps).length → ℝ) →L[ℝ] ℝ).differentiableAt
  rw [show
      (fun x : Fin (P :: Ps).length → ℝ =>
        (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
          (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          (List.zipWith totalTwoQubitLift edges
            (block.prefixGates ++ terminalPauliGatePath block.terminalGate (x 0) ::
              block.suffixGates))).reverse.prod) =
      (fun x : Fin (P :: Ps).length → ℝ =>
        (List.zipWith (fun edge gate =>
          (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          edges
          (block.prefixGates ++ terminalPauliGatePath block.terminalGate (x 0) ::
            block.suffixGates)).reverse.prod) by
        funext x
        rw [List.map_zipWith]]
  exact DifferentiableAt.comp
    (f := fun x : Fin (P :: Ps).length → ℝ => x 0)
    (g := fun t : ℝ =>
      (List.zipWith (fun edge gate =>
        (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        edges
        (block.prefixGates ++ terminalPauliGatePath block.terminalGate t ::
          block.suffixGates)).reverse.prod)
    (0 : Fin (P :: Ps).length → ℝ) hbase hcoord

/-- The simultaneous terminal-phase contraction is differentiable at the
base circuit. -/
theorem TerminalBlockPrefixAssembly.differentiableAt_terminalPhaseContraction_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    DifferentiableAt ℝ
      (fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod) 0 := by
  induction assembly with
  | nil =>
      exact differentiableAt_const (c := (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
  | @cons pre P Ps step tail ih =>
      let tailProj : (Fin (P :: Ps).length → ℝ) →L[ℝ] (Fin Ps.length → ℝ) :=
        ContinuousLinearMap.pi fun j : Fin Ps.length =>
          ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (P :: Ps).length => ℝ) j.succ
      have htailProj : DifferentiableAt ℝ
          (fun x : Fin (P :: Ps).length → ℝ => Fin.tail x) 0 := by
        change DifferentiableAt ℝ (tailProj :
          (Fin (P :: Ps).length → ℝ) → (Fin Ps.length → ℝ)) 0
        exact tailProj.differentiableAt
      have htail : DifferentiableAt ℝ
          (fun x : Fin (P :: Ps).length → ℝ =>
            (tail.terminalPhaseLiftedWord (Fin.tail x)).reverse.prod) 0 :=
        DifferentiableAt.comp
          (f := fun x : Fin (P :: Ps).length → ℝ => Fin.tail x)
          (g := fun y : Fin Ps.length → ℝ =>
            (tail.terminalPhaseLiftedWord y).reverse.prod)
          (0 : Fin (P :: Ps).length → ℝ) ih htailProj
      have hhead := step.block.differentiableAt_phaseContraction_head (Ps := Ps)
      change DifferentiableAt ℝ
        (fun x : Fin (P :: Ps).length → ℝ =>
          (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            (List.zipWith totalTwoQubitLift edges
              (step.block.prefixGates ++
                terminalPauliGatePath step.block.terminalGate (x 0) ::
                step.block.suffixGates)) ++
            tail.terminalPhaseLiftedWord (Fin.tail x)).reverse.prod) 0
      rw [show
          (fun x : Fin (P :: Ps).length → ℝ =>
            (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              (List.zipWith totalTwoQubitLift edges
                (step.block.prefixGates ++
                  terminalPauliGatePath step.block.terminalGate (x 0) ::
                  step.block.suffixGates)) ++
              tail.terminalPhaseLiftedWord (Fin.tail x)).reverse.prod) =
          (fun x : Fin (P :: Ps).length → ℝ =>
            (tail.terminalPhaseLiftedWord (Fin.tail x)).reverse.prod *
              (List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
                (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                (List.zipWith totalTwoQubitLift edges
                  (step.block.prefixGates ++
                    terminalPauliGatePath step.block.terminalGate (x 0) ::
                    step.block.suffixGates))).reverse.prod) by
              funext x
              rw [List.reverse_append, List.prod_append]]
      exact htail.mul hhead

/-- The real-linear tangent map of the simultaneous terminal-phase chart. -/
def TerminalBlockPrefixAssembly.terminalPhaseTangentMap
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    (Fin labels.length → ℝ) →L[ℝ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ where
  toFun := fun x => ∑ i, x i • (Complex.I •
    haferkampUnitaryListCoordinateOutput assembly.liftedWord
      (assembly.terminalIndices i)
      (finitePauliMatrix (Function.update (fun _ => none) root (some 2))))
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (c * x i) • (Complex.I •
      haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) =
      c • (x i • (Complex.I •
        haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))))
    rw [mul_smul]

/-- The actual real Fréchet derivative of the simultaneous chart at the base
circuit is its finite terminal-coordinate tangent map. -/
theorem TerminalBlockPrefixAssembly.hasFDerivAt_terminalPhaseContraction_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    HasFDerivAt
      (fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod)
      assembly.terminalPhaseTangentMap 0 := by
  let f : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod
  have hdiff : DifferentiableAt ℝ f 0 := by
    exact assembly.differentiableAt_terminalPhaseContraction_zero
  have hfull : HasFDerivAt f (fderiv ℝ f 0) 0 := hdiff.hasFDerivAt
  have haxis (i : Fin labels.length) :
      (fderiv ℝ f 0) (Pi.single i (1 : ℝ)) =
        Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    let singleCLM : ℝ →L[ℝ] (Fin labels.length → ℝ) :=
      ContinuousLinearMap.single ℝ (fun _ : Fin labels.length => ℝ) i
    have hsingle : HasFDerivAt (fun t : ℝ => Pi.single i t) singleCLM 0 := by
      change HasFDerivAt (singleCLM : ℝ → (Fin labels.length → ℝ)) singleCLM 0
      exact singleCLM.hasFDerivAt
    have hbase : HasFDerivAt f (fderiv ℝ f 0) (Pi.single i (0 : ℝ)) := by
      simpa using hfull
    have hcomp := HasFDerivAt.comp
      (f := fun t : ℝ => Pi.single i t) (g := f) 0 hbase hsingle
    have haxisExact := assembly.hasFDerivAt_terminalPhaseContraction_single i
    have hderiv : (fderiv ℝ f 0).comp singleCLM =
        ContinuousLinearMap.toSpanSingleton ℝ
          (Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
            (assembly.terminalIndices i)
            (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) := by
      apply hcomp.unique
      exact haxisExact
    have hvalue := congrArg (fun L : ℝ →L[ℝ]
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L 1) hderiv
    change (fderiv ℝ f 0) (Pi.single i (1 : ℝ)) = _ at hvalue
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hvalue
  have hmap : fderiv ℝ f 0 = assembly.terminalPhaseTangentMap := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      (fderiv ℝ f 0) x = (fderiv ℝ f 0) (∑ i, Pi.single i (x i)) := by
        rw [Finset.univ_sum_single]
      _ = ∑ i, (fderiv ℝ f 0) (Pi.single i (x i)) := by rw [map_sum]
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
      _ = assembly.terminalPhaseTangentMap x := by rfl
  rw [show (fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod) = f by rfl]
  exact hfull.congr_fderiv hmap

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
