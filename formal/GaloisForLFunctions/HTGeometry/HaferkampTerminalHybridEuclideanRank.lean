import GaloisForLFunctions.HTGeometry.HaferkampFlattenedAssemblyArchitecture

/-!
# Terminal-hybrid coordinate embedding and rank transfer

This module embeds the terminal phase directions of a backwards-light-cone
assembly in the finite terminal-hybrid chart of its flattened architecture.
It transfers the existing independent phase tangents to the derivative of the
finite architecture contraction.  The argument uses L2 operator charts and
entrywise derivatives, so no norm-transport assumption is introduced.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix.Norms.L2Operator

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

namespace TwoQubitArchitecture

def terminalHybridCoordinateAssignment {n R : ℕ}
    (_A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N)
    (p : Fin R → ℝ) :
    Fin R → terminalHybridEuclideanCoordinates N :=
  fun r => terminalHybridEuclideanEmbed N (p r) (z r)

theorem terminalHybridEuclideanContraction_eq_phaseWord
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (p : Fin R → ℝ)
    (hz : A.hybridEuclideanGateAssignment N z = gates) :
    A.terminalHybridEuclideanContraction N
      (A.terminalHybridCoordinateAssignment N z p) =
      (List.ofFn fun r => twoQubitLiftMatrix
        (A.sites r).1 (A.sites r).2 (A.distinct r)
        (terminalPauliGatePath (gates r) (p r))).reverse.prod := by
  unfold terminalHybridEuclideanContraction terminalHybridCoordinateAssignment
  congr 1
  apply congrArg List.reverse
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    rw [List.get_ofFn, List.get_ofFn]
    let r : Fin R := ⟨k, by simpa using hk₁⟩
    change twoQubitLiftMatrix (A.sites r).1 (A.sites r).2 (A.distinct r)
      (terminalHybridEuclideanGate N
        (terminalHybridEuclideanEmbed N (p r) (z r))) = _
    rw [show terminalHybridEuclideanGate N
      (terminalHybridEuclideanEmbed N (p r) (z r)) =
        terminalPauliGatePath (boolTwoQubitHybridEuclideanGate N (z r)) (p r) by rfl,
      show boolTwoQubitHybridEuclideanGate N (z r) = gates r by
        exact congrFun hz r]
    simp [r]

theorem terminalHybridEuclideanContraction_eq_phaseContraction
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (p : Fin R → ℝ)
    (hz : A.hybridEuclideanGateAssignment N z = gates) :
    A.terminalHybridEuclideanContraction N
      (A.terminalHybridCoordinateAssignment N z p) =
      (A.contraction (fun r => terminalPauliGatePath (gates r) (p r)) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  rw [A.terminalHybridEuclideanContraction_eq_phaseWord N z gates p hz]
  unfold contraction gateLift
  rw [← List.map_coe_unitary_reverse_prod]
  congr 1
  apply congrArg List.reverse
  rw [List.map_ofFn]
  congr 1

end TwoQubitArchitecture

def terminalHybridEuclideanPhaseInsertion (N : ℕ) :
    ℝ →L[ℝ] terminalHybridEuclideanCoordinates N :=
  (show ℝ →ₗ[ℝ] terminalHybridEuclideanCoordinates N from
    { toFun := fun t => terminalHybridEuclideanEmbed N t 0
      map_add' := by
        intro s t
        apply (EuclideanSpace.equiv (terminalHybridCoordinateIndex N) ℝ).injective
        ext ij
        cases ij <;> simp [terminalHybridEuclideanEmbed]
      map_smul' := by
        intro c t
        apply (EuclideanSpace.equiv (terminalHybridCoordinateIndex N) ℝ).injective
        ext ij
        cases ij <;> simp [terminalHybridEuclideanEmbed] }).toContinuousLinearMap

theorem terminalHybridEuclideanEmbed_eq_phaseInsertion_add_base
    (N : ℕ) (t : ℝ) (z : boolTwoQubitHybridEuclideanCoordinates N) :
    terminalHybridEuclideanEmbed N t z =
      terminalHybridEuclideanPhaseInsertion N t +
        terminalHybridEuclideanEmbed N 0 z := by
  apply (EuclideanSpace.equiv (terminalHybridCoordinateIndex N) ℝ).injective
  ext ij
  cases ij <;> simp [terminalHybridEuclideanPhaseInsertion,
    terminalHybridEuclideanEmbed]

theorem finrank_range_comp_right_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (A : X →L[ℝ] Y) (C : Y →L[ℝ] Z) :
    Module.finrank ℝ (C.comp A).range ≤ Module.finrank ℝ C.range := by
  have hrange : (C.comp A).range ≤ C.range :=
    LinearMap.range_comp_le_range A.toLinearMap C.toLinearMap
  exact LinearMap.finrank_le_finrank_of_injective
    (f := Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)

theorem ofFn_zipWith_edgeListGatesAsFn_pair
    {α β γ : Type*} (f : α → β → γ)
    (values : List α) (scalars : List β) (n : ℕ)
    (hvalues : values.length = n) (hscalars : scalars.length = n) :
    List.ofFn (fun r : Fin n =>
      f (edgeListGatesAsFn values n hvalues r)
        (edgeListGatesAsFn scalars n hscalars r)) =
      List.zipWith f values scalars := by
  apply List.ext_get
  · simp [hvalues, hscalars]
  · intro k hk₁ hk₂
    rw [List.get_ofFn]
    simp [edgeListGatesAsFn]

namespace BackwardsLightCone

theorem terminalPauliGatePath_zipWith_replicate_zero
    (gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)) :
    List.zipWith terminalPauliGatePath gates (List.replicate gates.length 0) = gates := by
  induction gates with
  | nil => rfl
  | cons U gates ih =>
      simp only [List.length_cons, List.replicate_succ, List.zipWith]
      rw [terminalPauliGatePath_zero, ih]

theorem zipWith_add_replicate_zero (k : ℕ) :
    List.zipWith (· + ·) (List.replicate k (0 : ℝ))
      (List.replicate k 0) = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.zipWith]
      rw [zero_add, ih]

theorem zipWith_add_terminalPhaseScalarSegment
    {α : Type*} (before after : List α) (s t : ℝ) :
    List.zipWith (· + ·)
      (List.replicate before.length 0 ++ s :: List.replicate after.length 0)
      (List.replicate before.length 0 ++ t :: List.replicate after.length 0) =
      List.replicate before.length 0 ++ (s + t) :: List.replicate after.length 0 := by
  induction before with
  | nil =>
      simp only [List.length_nil, List.replicate_zero, List.nil_append, List.zipWith]
      rw [zipWith_add_replicate_zero]
  | cons a before ih =>
      simp only [List.length_cons, List.replicate_succ]
      change (0 + 0) :: List.zipWith (· + ·)
        (List.replicate before.length 0 ++ s :: List.replicate after.length 0)
        (List.replicate before.length 0 ++ t :: List.replicate after.length 0) =
        0 :: List.replicate before.length 0 ++ (s + t) ::
          List.replicate after.length 0
      rw [zero_add, ih]
      simp

theorem map_smul_terminalPhaseScalarSegment
    {α : Type*} (before after : List α) (c s : ℝ) :
    List.map (fun t : ℝ => c • t)
      (List.replicate before.length 0 ++ s :: List.replicate after.length 0) =
      List.replicate before.length 0 ++ (c • s) ::
        List.replicate after.length 0 := by
  induction before with
  | nil =>
      simp only [List.length_nil, List.replicate_zero, List.nil_append,
        List.map_cons]
      rw [List.map_replicate]
      simp
  | cons a before ih =>
      simp only [List.length_cons, List.replicate_succ]
      change (c • 0) :: List.map (fun t : ℝ => c • t)
        (List.replicate before.length 0 ++ s :: List.replicate after.length 0) =
        0 :: List.replicate before.length 0 ++ (c • s) ::
          List.replicate after.length 0
      rw [smul_zero, ih]
      simp

def TerminalBlockPrefixAssembly.terminalPhaseScalarWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      (Fin labels.length → ℝ) → List ℝ
  | .nil _ => fun _ => []
  | .cons step tail => fun x =>
      List.replicate step.block.prefixGates.length 0 ++
        x 0 :: List.replicate step.block.suffixGates.length 0 ++
          tail.terminalPhaseScalarWord (Fin.tail x)

def TerminalBlockPrefixAssembly.terminalPhaseGateWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      (Fin labels.length → ℝ) →
        List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
  | .nil _ => fun _ => []
  | .cons step tail => fun x =>
      step.block.prefixGates ++ terminalPauliGatePath step.block.terminalGate (x 0) ::
        step.block.suffixGates ++ tail.terminalPhaseGateWord (Fin.tail x)

theorem TerminalBlockPrefixAssembly.terminalPhaseScalarWord_add
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x y : Fin labels.length → ℝ) :
    assembly.terminalPhaseScalarWord (x + y) =
      List.zipWith (· + ·) (assembly.terminalPhaseScalarWord x)
        (assembly.terminalPhaseScalarWord y) := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      let sx := List.replicate step.block.prefixGates.length 0 ++ x 0 ::
        List.replicate step.block.suffixGates.length 0
      let sy := List.replicate step.block.prefixGates.length 0 ++ y 0 ::
        List.replicate step.block.suffixGates.length 0
      have hsx : sx.length = sy.length := by
        simp [sx, sy]
      change List.replicate step.block.prefixGates.length 0 ++ (x 0 + y 0) ::
          List.replicate step.block.suffixGates.length 0 ++
            tail.terminalPhaseScalarWord (Fin.tail (x + y)) =
          List.zipWith (· + ·)
            (sx ++ tail.terminalPhaseScalarWord (Fin.tail x))
            (sy ++ tail.terminalPhaseScalarWord (Fin.tail y))
      rw [List.zipWith_append hsx]
      change List.replicate step.block.prefixGates.length 0 ++ (x 0 + y 0) ::
          List.replicate step.block.suffixGates.length 0 ++
            tail.terminalPhaseScalarWord (Fin.tail (x + y)) =
          List.zipWith (· + ·) sx sy ++
            List.zipWith (· + ·) (tail.terminalPhaseScalarWord (Fin.tail x))
              (tail.terminalPhaseScalarWord (Fin.tail y))
      have hsegment : List.zipWith (· + ·) sx sy =
          List.replicate step.block.prefixGates.length 0 ++ (x 0 + y 0) ::
            List.replicate step.block.suffixGates.length 0 := by
        exact zipWith_add_terminalPhaseScalarSegment step.block.prefixGates
          step.block.suffixGates (x 0) (y 0)
      rw [hsegment]
      have htail : Fin.tail (x + y) = Fin.tail x + Fin.tail y := by
        funext i
        rfl
      rw [htail, ih (Fin.tail x) (Fin.tail y)]

theorem TerminalBlockPrefixAssembly.terminalPhaseScalarWord_smul
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (c : ℝ) (x : Fin labels.length → ℝ) :
    assembly.terminalPhaseScalarWord (c • x) =
      List.map (fun t : ℝ => c • t) (assembly.terminalPhaseScalarWord x) := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      change List.replicate step.block.prefixGates.length 0 ++ (c • x 0) ::
          List.replicate step.block.suffixGates.length 0 ++
            tail.terminalPhaseScalarWord (Fin.tail (c • x)) =
          List.map (fun t : ℝ => c • t)
            (List.replicate step.block.prefixGates.length 0 ++ x 0 ::
              List.replicate step.block.suffixGates.length 0 ++
                tail.terminalPhaseScalarWord (Fin.tail x))
      rw [List.map_append]
      rw [map_smul_terminalPhaseScalarSegment step.block.prefixGates
        step.block.suffixGates c (x 0)]
      have htail : Fin.tail (c • x) = c • Fin.tail x := by
        funext i
        rfl
      rw [htail, ih (Fin.tail x)]

theorem TerminalBlockPrefixAssembly.terminalPhaseScalarWord_length_eq_flattenedEdgeWord_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    (assembly.terminalPhaseScalarWord x).length = assembly.flattenedEdgeWord.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp only [terminalPhaseScalarWord, flattenedEdgeWord, List.length_append,
        List.length_replicate, List.length_cons]
      rw [ih (Fin.tail x)]
      have hlocal : step.block.prefixGates.length +
          (step.block.suffixGates.length + 1) = edges.length := by
        calc
          step.block.prefixGates.length + (step.block.suffixGates.length + 1) =
              (step.block.prefixGates ++ step.block.terminalGate ::
                step.block.suffixGates).length := by
                simp
          _ = step.block.gates.length := congrArg List.length step.block.gates_decomp.symm
          _ = edges.length := step.block.gates_length
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun k => k + tail.flattenedEdgeWord.length) hlocal

theorem TerminalBlockPrefixAssembly.terminalPhaseGateWord_length_eq_flattenedEdgeWord_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    (assembly.terminalPhaseGateWord x).length = assembly.flattenedEdgeWord.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp only [terminalPhaseGateWord, flattenedEdgeWord, List.length_append,
        List.length_cons]
      rw [ih (Fin.tail x)]
      have hlocal : step.block.prefixGates.length +
          (step.block.suffixGates.length + 1) = edges.length := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          step.block.curve_length (x 0)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun k => k + tail.flattenedEdgeWord.length) hlocal

theorem TerminalBlockPrefixAssembly.terminalPhaseGateWord_eq_zipWith_gateWord_scalarWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    assembly.terminalPhaseGateWord x =
      List.zipWith terminalPauliGatePath assembly.gateWord
        (assembly.terminalPhaseScalarWord x) := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp only [terminalPhaseGateWord, terminalPhaseScalarWord,
        TerminalBlockPrefixAssembly.gateWord]
      have hscalar : List.replicate step.block.prefixGates.length 0 ++ x 0 ::
          List.replicate step.block.suffixGates.length 0 ++
            tail.terminalPhaseScalarWord (Fin.tail x) =
          (List.replicate step.block.prefixGates.length 0 ++ x 0 ::
            List.replicate step.block.suffixGates.length 0) ++
              tail.terminalPhaseScalarWord (Fin.tail x) := by
        simp [List.append_assoc]
      rw [hscalar]
      have hscalarLength :
          (List.replicate step.block.prefixGates.length 0 ++ x 0 ::
            List.replicate step.block.suffixGates.length 0).length =
            step.block.gates.length := by
        rw [step.block.gates_decomp]
        simp
      rw [List.zipWith_append hscalarLength.symm]
      have hcurrent :
          List.zipWith terminalPauliGatePath step.block.gates
            (List.replicate step.block.prefixGates.length 0 ++ x 0 ::
              List.replicate step.block.suffixGates.length 0) =
            step.block.prefixGates ++
              terminalPauliGatePath step.block.terminalGate (x 0) ::
                step.block.suffixGates := by
        rw [step.block.gates_decomp]
        exact (by
          induction step.block.prefixGates with
          | nil =>
              simp only [List.length_nil, List.replicate_zero, List.nil_append,
                List.zipWith]
              rw [terminalPauliGatePath_zipWith_replicate_zero]
          | cons U before hbefore =>
              simp only [List.length_cons, List.replicate_succ, List.cons_append,
                List.zipWith]
              rw [terminalPauliGatePath_zero, hbefore])
      rw [hcurrent, ih (Fin.tail x)]

theorem TerminalBlockPrefixAssembly.terminalPhaseLiftedWord_eq_zipWith_flattenedEdgeWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    assembly.terminalPhaseLiftedWord x =
      List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (List.zipWith totalTwoQubitLift assembly.flattenedEdgeWord
          (assembly.terminalPhaseGateWord x)) := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp only [terminalPhaseLiftedWord, flattenedEdgeWord, terminalPhaseGateWord]
      rw [List.zipWith_append (step.block.curve_length (x 0)).symm]
      simp only [List.map_append]
      rw [ih (Fin.tail x)]

/-- Finite gate-indexed form of recursive terminal phase scalar word. -/
def TerminalBlockPrefixAssembly.terminalPhaseScalarParameters
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) : Fin assembly.flattenedEdgeWord.length → ℝ :=
  edgeListGatesAsFn (assembly.terminalPhaseScalarWord x)
    assembly.flattenedEdgeWord.length
    (assembly.terminalPhaseScalarWord_length_eq_flattenedEdgeWord_length x)

theorem TerminalBlockPrefixAssembly.ofFn_terminalPhaseScalarParameters
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    List.ofFn (assembly.terminalPhaseScalarParameters x) =
      assembly.terminalPhaseScalarWord x := by
  unfold terminalPhaseScalarParameters
  exact ofFn_edgeListGatesAsFn _ _ _

theorem TerminalBlockPrefixAssembly.terminalPhaseScalarParameters_add
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x y : Fin labels.length → ℝ) :
    assembly.terminalPhaseScalarParameters (x + y) =
      assembly.terminalPhaseScalarParameters x +
        assembly.terminalPhaseScalarParameters y := by
  apply List.ofFn_injective
  rw [assembly.ofFn_terminalPhaseScalarParameters (x + y),
    assembly.terminalPhaseScalarWord_add x y]
  have hofnAdd (p q : Fin assembly.flattenedEdgeWord.length → ℝ) :
      List.ofFn (p + q) = List.zipWith (· + ·) (List.ofFn p) (List.ofFn q) := by
    apply List.ext_get
    · simp
    · intro k hk₁ hk₂
      rw [List.get_ofFn]
      simp
  rw [hofnAdd, assembly.ofFn_terminalPhaseScalarParameters x,
    assembly.ofFn_terminalPhaseScalarParameters y]

theorem TerminalBlockPrefixAssembly.terminalPhaseScalarParameters_smul
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (c : ℝ) (x : Fin labels.length → ℝ) :
    assembly.terminalPhaseScalarParameters (c • x) =
      c • assembly.terminalPhaseScalarParameters x := by
  apply List.ofFn_injective
  rw [assembly.ofFn_terminalPhaseScalarParameters (c • x),
    assembly.terminalPhaseScalarWord_smul c x]
  have hofnSmul (p : Fin assembly.flattenedEdgeWord.length → ℝ) :
      List.ofFn (c • p) = List.map (fun t : ℝ => c • t) (List.ofFn p) := by
    rw [List.map_ofFn]
    congr 1
  rw [hofnSmul, assembly.ofFn_terminalPhaseScalarParameters x]

def TerminalBlockPrefixAssembly.terminalPhaseScalarLinearMap
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    (Fin labels.length → ℝ) →ₗ[ℝ]
      (Fin assembly.flattenedEdgeWord.length → ℝ) where
  toFun := assembly.terminalPhaseScalarParameters
  map_add' := assembly.terminalPhaseScalarParameters_add
  map_smul' := assembly.terminalPhaseScalarParameters_smul

def TerminalBlockPrefixAssembly.terminalHybridCoordinateEmbedding
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (N : ℕ) (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N) :
    (Fin labels.length → ℝ) →
      (Fin assembly.flattenedEdgeWord.length →
        terminalHybridEuclideanCoordinates N) :=
  fun x => assembly.flattenedArchitecture.terminalHybridCoordinateAssignment N z
    (assembly.terminalPhaseScalarParameters x)

theorem TerminalBlockPrefixAssembly.differentiable_terminalHybridCoordinateEmbedding
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (N : ℕ) (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N) :
    Differentiable ℝ (assembly.terminalHybridCoordinateEmbedding N z) := by
  rw [differentiable_pi]
  intro r
  let Lr : (Fin labels.length → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin assembly.flattenedEdgeWord.length => ℝ) r).comp
      assembly.terminalPhaseScalarLinearMap.toContinuousLinearMap
  have hphase : Differentiable ℝ (fun x : Fin labels.length → ℝ =>
      terminalHybridEuclideanPhaseInsertion N (Lr x)) :=
    (terminalHybridEuclideanPhaseInsertion N).differentiable.comp Lr.differentiable
  have hbase : Differentiable ℝ (fun _ : Fin labels.length → ℝ =>
      terminalHybridEuclideanEmbed N 0 (z r)) := differentiable_const _
  have h := hphase.add hbase
  convert h using 1
  funext x
  change terminalHybridEuclideanEmbed N
      (assembly.terminalPhaseScalarParameters x r) (z r) =
    terminalHybridEuclideanPhaseInsertion N (Lr x) +
      terminalHybridEuclideanEmbed N 0 (z r)
  have hLr : Lr x = assembly.terminalPhaseScalarParameters x r := by
    rfl
  rw [hLr]
  exact terminalHybridEuclideanEmbed_eq_phaseInsertion_add_base N
    (assembly.terminalPhaseScalarParameters x r) (z r)

theorem TerminalBlockPrefixAssembly.terminalPhaseGateParameters_eq
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (x : Fin labels.length → ℝ) :
    (fun r => terminalPauliGatePath (assembly.flattenedGateParameters r)
      (assembly.terminalPhaseScalarParameters x r)) =
      edgeListGatesAsFn (assembly.terminalPhaseGateWord x)
        assembly.flattenedEdgeWord.length
        (assembly.terminalPhaseGateWord_length_eq_flattenedEdgeWord_length x) := by
  let p : Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
    fun r => terminalPauliGatePath (assembly.flattenedGateParameters r)
      (assembly.terminalPhaseScalarParameters x r)
  have hp : List.ofFn p = assembly.terminalPhaseGateWord x := by
    change List.ofFn (fun r => terminalPauliGatePath (assembly.flattenedGateParameters r)
      (assembly.terminalPhaseScalarParameters x r)) = _
    unfold flattenedGateParameters terminalPhaseScalarParameters
    rw [ofFn_zipWith_edgeListGatesAsFn_pair terminalPauliGatePath
      assembly.gateWord (assembly.terminalPhaseScalarWord x)
      assembly.flattenedEdgeWord.length
      assembly.flattenedEdgeWord_length_eq_gateWord_length.symm
      (assembly.terminalPhaseScalarWord_length_eq_flattenedEdgeWord_length x)]
    exact assembly.terminalPhaseGateWord_eq_zipWith_gateWord_scalarWord x |>.symm
  apply List.ofFn_injective
  rw [hp]
  exact (ofFn_edgeListGatesAsFn (assembly.terminalPhaseGateWord x)
    assembly.flattenedEdgeWord.length
    (assembly.terminalPhaseGateWord_length_eq_flattenedEdgeWord_length x)).symm

theorem TerminalBlockPrefixAssembly.terminalHybridEuclideanContraction_eq_terminalPhaseContraction
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (N : ℕ) (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N)
    (hz : assembly.flattenedArchitecture.hybridEuclideanGateAssignment N z =
      assembly.flattenedGateParameters)
    (x : Fin labels.length → ℝ) :
    assembly.flattenedArchitecture.terminalHybridEuclideanContraction N
      (assembly.flattenedArchitecture.terminalHybridCoordinateAssignment N z
        (assembly.terminalPhaseScalarParameters x)) =
      (assembly.terminalPhaseLiftedWord x).reverse.prod := by
  rw [assembly.flattenedArchitecture.terminalHybridEuclideanContraction_eq_phaseContraction
    N z assembly.flattenedGateParameters
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

theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalHybridEuclideanContraction_fderiv
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i)))
    (N : ℕ) (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N)
    (hz : assembly.flattenedArchitecture.hybridEuclideanGateAssignment N z =
      assembly.flattenedGateParameters) :
    labels.length ≤ Module.finrank ℝ
      (fderiv ℝ (assembly.flattenedArchitecture.terminalHybridEuclideanContraction N)
        (assembly.terminalHybridCoordinateEmbedding N z 0)).range := by
  let E := assembly.terminalHybridCoordinateEmbedding N z
  let G := assembly.flattenedArchitecture.terminalHybridEuclideanContraction N
  let F : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod
  have hE : DifferentiableAt ℝ E 0 :=
    assembly.differentiable_terminalHybridCoordinateEmbedding N z 0
  have hG : DifferentiableAt ℝ G (E 0) :=
    (assembly.flattenedArchitecture.analyticAt_terminalHybridEuclideanContraction N
      (E 0)).differentiableAt
  have hEq : (fun x => G (E x)) = F := by
    funext x
    exact assembly.terminalHybridEuclideanContraction_eq_terminalPhaseContraction
      N z hz x
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
