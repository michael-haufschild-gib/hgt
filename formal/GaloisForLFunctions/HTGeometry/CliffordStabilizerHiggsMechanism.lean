import GaloisForLFunctions.HTGeometry.StabilizerCliffordOrbit
import GaloisForLFunctions.HTGeometry.HiggsMechanism

/-!
# Clifford stabilizer Higgs mechanism

The binary-octahedral Clifford group acts on single-qubit density matrices by
conjugation.  All six stabilizer projectors lie in one vacuum orbit.  Choosing
the computational-zero projector retains a nontrivial `Z` half turn but breaks
an `X` half turn, hence gives finite partial symmetry breaking.
-/

open Matrix
open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

@[ext]
structure CliffordDensityField where
  val : Matrix Bool Bool ℂ

instance : SMul QubitTwoDesign.BinaryOctahedral CliffordDensityField :=
  ⟨fun g ρ => ⟨booleanQubitClifford g * ρ.val * (booleanQubitClifford g)ᴴ⟩⟩

instance : MulAction QubitTwoDesign.BinaryOctahedral CliffordDensityField where
  one_smul ρ := by
    apply CliffordDensityField.ext
    change booleanQubitClifford 1 * ρ.val * (booleanQubitClifford 1)ᴴ = ρ.val
    rw [booleanQubitClifford_one]
    simp
  mul_smul g h ρ := by
    apply CliffordDensityField.ext
    change booleanQubitClifford (g * h) * ρ.val * (booleanQubitClifford (g * h))ᴴ =
      booleanQubitClifford g *
        (booleanQubitClifford h * ρ.val * (booleanQubitClifford h)ᴴ) *
          (booleanQubitClifford g)ᴴ
    rw [booleanQubitClifford_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

def qubitZeroDensity : Matrix Bool Bool ℂ :=
  fun i j => if i = false ∧ j = false then 1 else 0

def pureQubitDensity (ψ : Bool → ℂ) : Matrix Bool Bool ℂ :=
  fun i j => ψ i * (starRingEnd ℂ) (ψ j)

theorem qubitZeroDensity_eq_pure : qubitZeroDensity = pureQubitDensity boolZeroState := by
  ext i j
  cases i <;> cases j <;> simp [qubitZeroDensity, pureQubitDensity, boolZeroState]

theorem conjugate_pureQubitDensity (M : Matrix Bool Bool ℂ) (ψ : Bool → ℂ) :
    M * pureQubitDensity ψ * Mᴴ = pureQubitDensity (M *ᵥ ψ) := by
  ext i j
  cases i <;> cases j <;>
    simp [pureQubitDensity, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply]
    <;> ring

theorem pureQubitDensity_phase (c : ℂ) (hc : ‖c‖ = 1) (ψ : Bool → ℂ) :
    pureQubitDensity (c • ψ) = pureQubitDensity ψ := by
  have hnormSq : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc]
    norm_num
  ext i j
  change c * ψ i * (starRingEnd ℂ) (c * ψ j) =
    ψ i * (starRingEnd ℂ) (ψ j)
  rw [map_mul]
  calc
    c * ψ i * ((starRingEnd ℂ) c * (starRingEnd ℂ) (ψ j)) =
        (c * (starRingEnd ℂ) c) * (ψ i * (starRingEnd ℂ) (ψ j)) := by ring
    _ = ψ i * (starRingEnd ℂ) (ψ j) := by
      rw [Complex.mul_conj, hnormSq]
      simp

def cliffordHiggsVacuum : CliffordDensityField := ⟨qubitZeroDensity⟩

def cliffordHiggsMechanism :
    HiggsMechanism QubitTwoDesign.BinaryOctahedral CliffordDensityField :=
  HiggsMechanism.canonicalOrbitWell cliffordHiggsVacuum

def cliffordZHalfTurn : QubitTwoDesign.BinaryOctahedral :=
  cliffordPauliHalfTurnCode (some 2)

def cliffordXHalfTurn : QubitTwoDesign.BinaryOctahedral :=
  cliffordPauliHalfTurnCode (some 0)

theorem cliffordZHalfTurn_fixes_vacuum :
    cliffordZHalfTurn • cliffordHiggsVacuum = cliffordHiggsVacuum := by
  apply CliffordDensityField.ext
  change booleanQubitClifford cliffordZHalfTurn * qubitZeroDensity *
      (booleanQubitClifford cliffordZHalfTurn)ᴴ = qubitZeroDensity
  rw [cliffordZHalfTurn, booleanQubitClifford_pauliHalfTurn]
  ext i j
  cases i <;> cases j <;>
    simp [cliffordPauliHalfTurnPhase, boolPauliOption, finiteQubitPauli,
      qubitZeroDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem cliffordZHalfTurn_ne_one : cliffordZHalfTurn ≠ 1 := by
  intro h
  have hm := congrArg booleanQubitClifford h
  rw [cliffordZHalfTurn, booleanQubitClifford_pauliHalfTurn,
    booleanQubitClifford_one] at hm
  have he := congrFun₂ hm false false
  simp [cliffordPauliHalfTurnPhase, boolPauliOption, finiteQubitPauli] at he
  norm_num [Complex.ext_iff] at he

theorem cliffordHiggs_unbroken_ne_bot : cliffordHiggsMechanism.unbroken ≠ ⊥ := by
  intro hbot
  have hmem : cliffordZHalfTurn ∈ cliffordHiggsMechanism.unbroken := by
    rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
    exact cliffordZHalfTurn_fixes_vacuum
  rw [hbot] at hmem
  exact cliffordZHalfTurn_ne_one (by simpa using hmem)

theorem cliffordXHalfTurn_not_fix_vacuum :
    cliffordXHalfTurn • cliffordHiggsVacuum ≠ cliffordHiggsVacuum := by
  intro h
  have hm := congrArg CliffordDensityField.val h
  change booleanQubitClifford cliffordXHalfTurn * qubitZeroDensity *
      (booleanQubitClifford cliffordXHalfTurn)ᴴ = qubitZeroDensity at hm
  rw [cliffordXHalfTurn, booleanQubitClifford_pauliHalfTurn] at hm
  have he := congrFun₂ hm false false
  simp [cliffordPauliHalfTurnPhase, boolPauliOption, finiteQubitPauli,
    qubitZeroDensity, Matrix.mul_apply, Matrix.conjTranspose_apply] at he

theorem cliffordHiggs_unbroken_ne_top : cliffordHiggsMechanism.unbroken ≠ ⊤ := by
  intro htop
  apply cliffordXHalfTurn_not_fix_vacuum
  have hmem : cliffordXHalfTurn ∈ cliffordHiggsMechanism.unbroken := by
    rw [htop]
    simp
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff] at hmem
  exact hmem

theorem cliffordHiggs_partiallyBroken : cliffordHiggsMechanism.IsPartiallyBroken :=
  ⟨cliffordHiggs_unbroken_ne_bot, cliffordHiggs_unbroken_ne_top⟩

def cliffordStabilizerDensity (t : Fin 6) : CliffordDensityField :=
  ⟨pureQubitDensity (boolStabAmp t)⟩

theorem cliffordStabilizerDensity_mem_vacuumOrbit (t : Fin 6) :
    cliffordStabilizerDensity t ∈ cliffordHiggsMechanism.vacuumOrbit := by
  obtain ⟨c, hc, hact⟩ := booleanQubitClifford_stabClifford_mulVec t
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  refine ⟨stabClifford t, ?_⟩
  apply CliffordDensityField.ext
  change booleanQubitClifford (stabClifford t) * qubitZeroDensity *
      (booleanQubitClifford (stabClifford t))ᴴ = pureQubitDensity (boolStabAmp t)
  rw [qubitZeroDensity_eq_pure, conjugate_pureQubitDensity, hact,
    pureQubitDensity_phase c hc]

theorem cliffordStabilizerDensity_zeroPotential (t : Fin 6) :
    cliffordHiggsMechanism.potential (cliffordStabilizerDensity t) = 0 :=
  cliffordHiggsMechanism.potential_eq_zero_of_mem_vacuumOrbit
    (cliffordStabilizerDensity_mem_vacuumOrbit t)

end GaloisForLFunctions.HTGeometry
