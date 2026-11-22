import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.ComplexSystem
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.OperatorBall
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # Real algebraic incidence for a fixed physical gate architecture -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
abbrev PairBits := Bool × Bool
abbrev Bits (N : ℕ) := Fin N → Bool
abbrev Square (d : Type*) := Matrix d d ℂ

/-- The product of ambient gate matrices, before imposing the special
unitary equations on each parameter. -/
def rawWord {N g : ℕ} (D : TwoQubitArchitecture N g) (G : Fin g → Square PairBits) : Square (Bits N) :=
  (List.ofFn fun k => twoQubitLiftMatrix (D.sites k).1 (D.sites k).2 (D.distinct k) (G k)).reverse.prod

theorem rawWord_eval {N g : ℕ} (D : TwoQubitArchitecture N g)
    (G : Fin g → Matrix.specialUnitaryGroup PairBits ℂ) :
    rawWord D (fun k => (G k).val) = (D.contraction G).val := by
  let F := (unitary (Square (Bits N))).subtype
  change _ = F ((List.ofFn fun k => D.gateLift k (G k)).reverse.prod)
  rw [map_list_prod,List.map_reverse,List.map_ofFn]
  rfl

theorem rawWord_rep {A X : Type*} [CommRing A] {ρ : X → A →+* ℝ} {N g : ℕ} (D : TwoQubitArchitecture N g)
    {G : X → Fin g → Square PairBits} (h : ∀ k, MatrixRep ρ (fun x => G x k)) :
    MatrixRep ρ (fun x => rawWord D (G x)) := by
  let L := fun x k => twoQubitLiftMatrix (D.sites k).1 (D.sites k).2 (D.distinct k) (G x k)
  have hh (l : List (Fin g)) : MatrixRep ρ (fun x => (l.map (L x)).prod) := by
    induction l with
    | nil => exact MatrixRep.one
    | cons k l ih => exact ((h k).lift (D.sites k).1 (D.sites k).2 (D.distinct k)).mul ih
  simpa only [List.map_reverse,List.map_ofFn,Function.comp_id,L,rawWord] using
    hh ((List.ofFn (id : Fin g → Fin g)).reverse)

abbrev ComplexVars (N g : ℕ) := Unit ⊕ ((Fin g × PairBits × PairBits) ⊕ (Bits N × Bits N))
abbrev Coord (N g : ℕ) := ComplexVars N g × Bool
abbrev Equation (N g : ℕ) := Unit ⊕ ((Fin g × (Unit ⊕ (PairBits × PairBits))) ⊕ (Bits N × Bits N))

def readVar {N g : ℕ} (w : Coord N g → ℝ) (i : ComplexVars N g) : ℂ := ⟨w (i,false),w (i,true)⟩
def phaseVar {N g : ℕ} (w : Coord N g → ℝ) := readVar w (.inl ())
def gateVar {N g : ℕ} (w : Coord N g → ℝ) (k : Fin g) : Square PairBits :=
  fun i j => readVar w (.inr (.inl (k,i,j)))
def slackVar {N g : ℕ} (w : Coord N g → ℝ) : Square (Bits N) :=
  fun i j => readVar w (.inr (.inr (i,j)))

/-- The phase, gates, and slack have independent complex coordinates. -/
theorem exists_witness_tuple {N g : ℕ} (z : ℂ) (G : Fin g → Square PairBits) (B : Square (Bits N)) :
    ∃ w : Coord N g → ℝ, phaseVar w = z ∧ gateVar w = G ∧ slackVar w = B := by
  let v : ComplexVars N g → ℂ := Sum.elim (fun _ => z) (Sum.elim (fun k => G k.1 k.2.1 k.2.2) (fun q => B q.1 q.2))
  let w (i : Coord N g) := if i.2 then (v i.1).im else (v i.1).re
  exact ⟨w,Complex.ext rfl rfl,funext fun _ => Matrix.ext fun _ _ => Complex.ext rfl rfl,
    Matrix.ext fun _ _ => Complex.ext rfl rfl⟩

/-- Each complex residual vanishes precisely when its scalar, special
unitary, or positive-semidefinite slack constraint is satisfied. -/
def residual {N g : ℕ} (D : TwoQubitArchitecture N g) (U : Square (Bits N)) (ε : ℝ)
    (w : Coord N g → ℝ) : Equation N g → ℂ
  | .inl _ => star (phaseVar w)*phaseVar w-1
  | .inr (.inl (k,.inl _)) => (gateVar w k).det-1
  | .inr (.inl (k,.inr (i,j))) => (star (gateVar w k)*gateVar w k-1) i j
  | .inr (.inr (i,j)) =>
    let M := U-phaseVar w • rawWord D (gateVar w)
    ((ε^2) • (1 : Square (Bits N))-star M*M-star (slackVar w)*slackVar w) i j

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
