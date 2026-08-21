import GaloisForLFunctions.HTGeometry.RightFlipScattering

/-!
# A non-symmetric Yang--Baxter matrix and framed Markov trace

`rMatrix = i · SWAP` acts on `ℂ² ⊗ ℂ²`.  Its braid action satisfies Yang--Baxter, while
`R² = -id`, so it is not a symmetric braiding.  The phase of its crossings gives a closed framed
Markov trace with positive and negative stabilization factors `i` and `-i`.

This is deliberately a framed phase invariant, not the Jones polynomial: the Hecke relation and
nontrivial quantum trace needed for Jones normalization are separate infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry.KnotTheory

noncomputable section

abbrev Qubit := Fin 2
abbrev PairBasis := Qubit × Qubit
abbrev PairState := PairBasis → ℂ
abbrev TripleState := Qubit → Qubit → Qubit → ℂ

def rPermutation : Equiv.Perm PairBasis := Equiv.prodComm Qubit Qubit

/-- A non-symmetric braiding matrix: `i` times the two-qubit swap. -/
def rMatrix : Matrix PairBasis PairBasis ℂ :=
  Complex.I • (rPermutation.permMatrix ℂ)

/-- This concrete braiding is the phase-identity specialization of the existing right-flip
scattering convention.  It is therefore compatible with that module's matrix-level quantum
Yang--Baxter transport. -/
theorem rMatrix_eq_rightFlip_phaseIdentity :
    rMatrix = rightFlip (Complex.I • (1 : Matrix PairBasis PairBasis ℂ))
      (twoParticleFlipMatrix Qubit) := by
  ext x y
  simp [rMatrix, rPermutation, rightFlip, twoParticleFlipMatrix]

private theorem rMatrix_leg12_phase :
    threeParticleLeg12 Qubit rMatrix =
      Complex.I • threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit) := by
  ext x y
  simp [rMatrix, rPermutation, twoParticleFlipMatrix, threeParticleLeg12]

private theorem rMatrix_leg23_phase :
    threeParticleLeg23 Qubit rMatrix =
      Complex.I • threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit) := by
  ext x y
  by_cases h : x.2.swap = y.2
  · simp [rMatrix, rPermutation, twoParticleFlipMatrix, threeParticleLeg23, h, mul_comm]
  · simp [rMatrix, rPermutation, twoParticleFlipMatrix, threeParticleLeg23, h]

private theorem rMatrix_leg13_phase :
    threeParticleLeg13 Qubit rMatrix =
      Complex.I • threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit) := by
  simp only [threeParticleLeg13, rMatrix_leg23_phase, Matrix.mul_smul, Matrix.smul_mul]

private theorem flipMatrix_quantum_yang_baxter :
    threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit) *
          threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit) *
          threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit) =
        threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit) *
          threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit) *
          threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit) := by
  have h := (matrix_rightFlip_adjacentBraid_iff_quantumYangBaxter
    (κ := Qubit) (fun _ : ℤ => 1)).mp (by
      intro x y
      simp)
  simpa [rightFlip] using h

/-- Matrix-leg quantum Yang--Baxter equation for the non-symmetric phase braiding. -/
theorem rMatrix_quantum_yang_baxter :
    threeParticleLeg12 Qubit rMatrix * threeParticleLeg13 Qubit rMatrix *
          threeParticleLeg23 Qubit rMatrix =
        threeParticleLeg23 Qubit rMatrix * threeParticleLeg13 Qubit rMatrix *
          threeParticleLeg12 Qubit rMatrix := by
  rw [rMatrix_leg12_phase, rMatrix_leg13_phase, rMatrix_leg23_phase]
  calc
    (Complex.I • threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit)) *
          (Complex.I • threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit)) *
          (Complex.I • threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit)) =
        (Complex.I * Complex.I * Complex.I) •
          (threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit) *
            threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit) *
            threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit)) := by
          rw [smul_mul_smul, smul_mul_smul]
    _ = (Complex.I * Complex.I * Complex.I) •
          (threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit) *
            threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit) *
            threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit)) := by
          rw [flipMatrix_quantum_yang_baxter]
    _ = (Complex.I • threeParticleLeg23 Qubit (twoParticleFlipMatrix Qubit)) *
          (Complex.I • threeParticleLeg13 Qubit (twoParticleFlipMatrix Qubit)) *
          (Complex.I • threeParticleLeg12 Qubit (twoParticleFlipMatrix Qubit)) := by
          rw [smul_mul_smul, smul_mul_smul]

def rAction (f : PairState) : PairState := fun (i, j) => Complex.I * f (j, i)
def rInverseAction (f : PairState) : PairState := fun (i, j) => -Complex.I * f (j, i)

theorem rMatrix_mulVec (f : PairState) : rMatrix.mulVec f = rAction f := by
  ext x
  obtain ⟨i, j⟩ := x
  simp [rMatrix, rAction, Matrix.smul_mulVec, Matrix.permMatrix_mulVec,
    rPermutation, Function.comp_def]

def r12 (f : TripleState) : TripleState := fun i j k => Complex.I * f j i k
def r23 (f : TripleState) : TripleState := fun i j k => Complex.I * f i k j

/-- Yang--Baxter equation `(R ⊗ id)(id ⊗ R)(R ⊗ id) = (id ⊗ R)(R ⊗ id)(id ⊗ R)`. -/
theorem r_yang_baxter (f : TripleState) : r12 (r23 (r12 f)) = r23 (r12 (r23 f)) := by
  funext i j k
  simp only [r12, r23]

theorem rAction_square (f : PairState) : rAction (rAction f) = -f := by
  funext x
  obtain ⟨i, j⟩ := x
  simp only [rAction, Pi.neg_apply]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

theorem rAction_rInverse (f : PairState) : rAction (rInverseAction f) = f := by
  funext x
  obtain ⟨i, j⟩ := x
  simp only [rAction, rInverseAction]
  rw [← mul_assoc, mul_neg, Complex.I_mul_I]
  simp

theorem rInverse_rAction (f : PairState) : rInverseAction (rAction f) = f := by
  funext x
  obtain ⟨i, j⟩ := x
  simp only [rAction, rInverseAction]
  rw [← mul_assoc, neg_mul, Complex.I_mul_I]
  simp

def ket00 : PairState := fun (i, j) => if i = 0 ∧ j = 0 then 1 else 0

/-- The braiding is not symmetric: its double braiding is not identity. -/
theorem rAction_square_ne_identity : rAction (rAction ket00) ≠ ket00 := by
  intro h
  have h00 := congrFun h (0, 0)
  rw [rAction_square, ket00] at h00
  simp [ket00] at h00
  exact (Ring.neg_one_ne_one_of_char_ne_two (R := ℂ) (by simp [ringChar.eq_zero])) h00

/-- Signed adjacent-crossing words on `n` labelled generators. -/
inductive CrossingSign where
  | positive
  | negative
  deriving DecidableEq

abbrev BraidWord (n : ℕ) := List (Fin n × CrossingSign)

def crossingWrithe : CrossingSign → ℤ
  | .positive => 1
  | .negative => -1

/-- Positive and negative braid crossings act by `R` and `R⁻¹`. -/
def rCrossingAction : CrossingSign → PairState → PairState
  | .positive => rAction
  | .negative => rInverseAction

def rCrossingPhase : CrossingSign → ℂ
  | .positive => Complex.I
  | .negative => -Complex.I

theorem rCrossingAction_cancel (f : PairState) :
    rCrossingAction .positive (rCrossingAction .negative f) = f :=
  rAction_rInverse f

def braidWrithe : BraidWord n → ℤ
  | [] => 0
  | (_, s) :: w => crossingWrithe s + braidWrithe w

theorem braidWrithe_append (w v : BraidWord n) :
    braidWrithe (w ++ v) = braidWrithe w + braidWrithe v := by
  induction w with
  | nil => simp [braidWrithe]
  | cons a w ih =>
      simp only [List.cons_append, braidWrithe, ih]
      ring

def liftBraidWord (w : BraidWord n) : BraidWord (n + 1) :=
  w.map fun (i, s) => (Fin.castSucc i, s)

theorem braidWrithe_lift (w : BraidWord n) : braidWrithe (liftBraidWord w) = braidWrithe w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      obtain ⟨i, s⟩ := a
      simpa [liftBraidWord, braidWrithe] using
        congrArg (fun z : ℤ => crossingWrithe s + z) ih

def stabilizeBraid (s : CrossingSign) (w : BraidWord n) : BraidWord (n + 1) :=
  liftBraidWord w ++ [(Fin.last n, s)]

theorem braidWrithe_stabilize (s : CrossingSign) (w : BraidWord n) :
    braidWrithe (stabilizeBraid s w) = braidWrithe w + crossingWrithe s := by
  rw [stabilizeBraid, braidWrithe_append, braidWrithe_lift]
  simp [braidWrithe]

/-- The one-dimensional framed Markov character carried by the phase of `rMatrix`. -/
def framedMarkovTrace (w : BraidWord n) : ℂ := Complex.I ^ braidWrithe w

theorem framedMarkovTrace_append (w v : BraidWord n) :
    framedMarkovTrace (w ++ v) = framedMarkovTrace w * framedMarkovTrace v := by
  change Complex.I ^ braidWrithe (w ++ v) =
    Complex.I ^ braidWrithe w * Complex.I ^ braidWrithe v
  rw [braidWrithe_append, zpow_add₀ Complex.I_ne_zero]

theorem framedMarkovTrace_cyclic (w v : BraidWord n) :
    framedMarkovTrace (w ++ v) = framedMarkovTrace (v ++ w) := by
  rw [framedMarkovTrace_append, framedMarkovTrace_append, mul_comm]

theorem framedMarkovTrace_stabilize_positive (w : BraidWord n) :
    framedMarkovTrace (stabilizeBraid .positive w) = framedMarkovTrace w * Complex.I := by
  change Complex.I ^ braidWrithe (stabilizeBraid .positive w) =
    Complex.I ^ braidWrithe w * Complex.I
  rw [braidWrithe_stabilize, zpow_add₀ Complex.I_ne_zero]
  simp [crossingWrithe]

theorem framedMarkovTrace_stabilize_negative (w : BraidWord n) :
    framedMarkovTrace (stabilizeBraid .negative w) = framedMarkovTrace w * (-Complex.I) := by
  change Complex.I ^ braidWrithe (stabilizeBraid .negative w) =
    Complex.I ^ braidWrithe w * (-Complex.I)
  rw [braidWrithe_stabilize, zpow_add₀ Complex.I_ne_zero]
  simp [crossingWrithe, zpow_neg, Complex.inv_I]

theorem framedMarkovTrace_stabilize (s : CrossingSign) (w : BraidWord n) :
    framedMarkovTrace (stabilizeBraid s w) = framedMarkovTrace w * rCrossingPhase s := by
  cases s
  · exact framedMarkovTrace_stabilize_positive w
  · exact framedMarkovTrace_stabilize_negative w

/-- A framed Markov trace records cyclicity and both stabilization factors. -/
structure FramedMarkovTrace (positiveFactor negativeFactor : ℂ) where
  trace : ∀ {n : ℕ}, BraidWord n → ℂ
  trace_append : ∀ {n : ℕ} (w v : BraidWord n),
    trace (w ++ v) = trace w * trace v
  trace_cyclic : ∀ {n : ℕ} (w v : BraidWord n), trace (w ++ v) = trace (v ++ w)
  trace_stabilize_positive : ∀ {n : ℕ} (w : BraidWord n),
    trace (stabilizeBraid .positive w) = trace w * positiveFactor
  trace_stabilize_negative : ∀ {n : ℕ} (w : BraidWord n),
    trace (stabilizeBraid .negative w) = trace w * negativeFactor

/-- The phase of the non-symmetric `rMatrix` furnishes a closed framed Markov trace. -/
def phaseMarkovTrace : FramedMarkovTrace Complex.I (-Complex.I) where
  trace := fun {_} => framedMarkovTrace
  trace_append := fun w v => framedMarkovTrace_append w v
  trace_cyclic := fun w v => framedMarkovTrace_cyclic w v
  trace_stabilize_positive := fun w => framedMarkovTrace_stabilize_positive w
  trace_stabilize_negative := fun w => framedMarkovTrace_stabilize_negative w

end

end GaloisForLFunctions.HTGeometry.KnotTheory
