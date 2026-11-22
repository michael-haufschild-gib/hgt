import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Represented
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPauliCoordinate

/-! # Polynomial entries of gate products, adjoints and determinants -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A X d : Type*} [CommRing A] {ρ : X → A →+* ℝ}

theorem ComplexRep.intCast (m : ℤ) : ComplexRep ρ (fun _ => (m:ℂ)) := by
  refine ⟨⟨m,fun x => ?_⟩,⟨0,fun x => ?_⟩⟩ <;> simp

theorem ComplexRep.prod {ι : Type*} (s : Finset ι) {f : ι → X → ℂ} (h : ∀ i ∈ s, ComplexRep ρ (f i)) :
    ComplexRep ρ (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (ComplexRep.one (ρ := ρ))
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h _ (Finset.mem_insert_self ..)).mul (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

def MatrixRep (ρ : X → A →+* ℝ) (M : X → Matrix d d ℂ) : Prop :=
  ∀ i j, ComplexRep ρ (fun x => M x i j)

theorem MatrixRep.one [DecidableEq d] : MatrixRep ρ (fun _ => (1:Matrix d d ℂ)) := by
  intro i j
  by_cases h : i=j
  · subst j; simpa only [Matrix.one_apply_eq] using (ComplexRep.one (ρ := ρ))
  · simpa only [Matrix.one_apply_ne h] using (ComplexRep.zero (ρ := ρ))

theorem MatrixRep.mul [Fintype d] {M L : X → Matrix d d ℂ} (hm : MatrixRep ρ M) (hl : MatrixRep ρ L) :
    MatrixRep ρ (fun x => M x * L x) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ComplexRep.sum _ (fun k _ => (hm i k).mul (hl k j))

theorem MatrixRep.sub {M L : X → Matrix d d ℂ} (hm : MatrixRep ρ M) (hl : MatrixRep ρ L) :
    MatrixRep ρ (fun x => M x - L x) := fun i j => (hm i j).sub (hl i j)

theorem MatrixRep.star {M : X → Matrix d d ℂ} (hm : MatrixRep ρ M) :
    MatrixRep ρ (fun x => star (M x)) := fun i j => (hm j i).star

theorem MatrixRep.smul {f : X → ℂ} {M : X → Matrix d d ℂ} (hf : ComplexRep ρ f) (hm : MatrixRep ρ M) :
    MatrixRep ρ (fun x => f x • M x) := fun i j => hf.mul (hm i j)

theorem MatrixRep.det [Fintype d] [DecidableEq d] {M : X → Matrix d d ℂ} (hm : MatrixRep ρ M) :
    ComplexRep ρ (fun x => (M x).det) := by
  simp only [Matrix.det_apply']
  exact ComplexRep.sum _ (fun σ _ => (ComplexRep.intCast (Equiv.Perm.sign σ : ℤ)).mul
    (ComplexRep.prod _ (fun j _ => hm (σ j) j)))

/-- A lifted gate has either zero entry or the corresponding local matrix entry. -/
theorem MatrixRep.lift {N : ℕ} {M : X → Matrix (Bool×Bool) (Bool×Bool) ℂ}
    (hm : MatrixRep ρ M) (a b : Fin N) (hab : a≠b) :
    MatrixRep ρ (fun x => twoQubitLiftMatrix a b hab (M x)) := by
  let I := {i : Fin N // i≠a ∧ i≠b}
  let rest (v : Fin N → Bool) := fun i : I => v i.val
  intro v w
  change ComplexRep ρ (fun x => M x (v a,v b) (w a,w b) * (1 : Matrix (I → Bool) _ ℂ) (rest v) (rest w))
  refine (hm (v a,v b) (w a,w b)).mul (g := fun _ : X => (1 : Matrix (I → Bool) _ ℂ) (rest v) (rest w)) ?_
  by_cases h : rest v = rest w
  · have he : (1 : Matrix (I → Bool) _ ℂ) (rest v) (rest w)=1 := by rw [Matrix.one_apply,if_pos h]
    exact he.symm ▸ (ComplexRep.one (ρ := ρ))
  · have he : (1 : Matrix (I → Bool) _ ℂ) (rest v) (rest w)=0 := Matrix.one_apply_ne h
    exact he.symm ▸ (ComplexRep.zero (ρ := ρ))

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
