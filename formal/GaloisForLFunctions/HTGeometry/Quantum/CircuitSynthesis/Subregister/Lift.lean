import GaloisForLFunctions.HTGeometry.HaferkampExactCircuitComplexity
import GaloisForLFunctions.HTGeometry.HypergraphComponentWitness

/-! # Placing a physical two-qubit circuit on a subset of wires -/
open Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.Subregister
noncomputable section

private abbrev Config (n : ℕ) := Fin n → Bool
private abbrev Reg (n : ℕ) := Matrix (Config n) (Config n) ℂ

/-- Put a numbered small matrix on S in wire order e, with identity outside. -/
def place {n k : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) (A : Reg k) : Reg n :=
  liftLocalMatrix (A := fun _ : Fin n => Bool) S
    (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.arrowCongr e (Equiv.refl Bool)) A)

private theorem local_mul {n : ℕ} (S : Finset (Fin n))
    (A B : Matrix (S → Bool) (S → Bool) ℂ) :
    liftLocalMatrix (A := fun _ : Fin n => Bool) S (A*B) = liftLocalMatrix S A * liftLocalMatrix S B := by
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ (configurationSplitEquiv (fun _ : Fin n => Bool) S)
  have h (M : Matrix (S → Bool) (S → Bool) ℂ) :
      Φ (liftLocalMatrix S M) = M ⊗ₖ (1 : Matrix (OutsideConfiguration (fun _ : Fin n => Bool) S)
        (OutsideConfiguration (fun _ : Fin n => Bool) S) ℂ) :=
    reindex_liftLocalMatrix_eq_kronecker_one (A := fun _ : Fin n => Bool) S M
  apply Φ.injective
  rw [map_mul,h,h,h]
  let O := OutsideConfiguration (fun _ : Fin n => Bool) S
  simpa only [one_mul] using Matrix.mul_kronecker_mul A B (1 : Matrix O O ℂ) (1 : Matrix O O ℂ)

/-- Placing on fixed wires preserves gate products. -/
def placeHom {n k : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) : Reg k →* Reg n where
  toFun := place e
  map_one' := by simp only [place,map_one,liftLocalMatrix_one]
  map_mul' A B := by simp only [place,map_mul,local_mul]

theorem place_smul {n k : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) (z : ℂ) (A : Reg k) :
    place e (z • A) = z • place e A := by
  ext x y
  by_cases h : restrictOutsideConfiguration S x = restrictOutsideConfiguration S y
    <;> simp [place,liftLocalMatrix,h,Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply]

private theorem gate_entry {Q : Type*} [Fintype Q] [DecidableEq Q] (a b : Q) (hab : a ≠ b)
    (G : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) (x y : Q → Bool) :
    (twoQubitLift a b hab G : Matrix (Q → Bool) (Q → Bool) ℂ) x y =
      if ∀ v, v ≠ a → v ≠ b → x v = y v then G.val (x a,x b) (y a,y b) else 0 := by
  classical
  let rest (u : Q → Bool) := fun v : {v : Q // v ≠ a ∧ v ≠ b} => u v.val
  change G.val (x a,x b) (y a,y b) * (1 : Matrix _ _ ℂ) (rest x) (rest y) = _
  have he : rest x = rest y ↔ ∀ v, v ≠ a → v ≠ b → x v = y v := by
    exact ⟨fun h v ha hb => congrFun h ⟨v,ha,hb⟩,fun h => funext fun v => h v.val v.2.1 v.2.2⟩
  by_cases h : rest x = rest y
  · rw [Matrix.one_apply,if_pos h,if_pos (he.mp h),mul_one]
  · rw [Matrix.one_apply,if_neg h,if_neg (fun hh => h (he.mpr hh)),mul_zero]

private theorem place_gate {n k : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) (a b : Fin k) (hab : a ≠ b)
    (G : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    place e (twoQubitLift a b hab G) = (twoQubitLift (e a).val (e b).val
      (fun h => hab (e.injective (Subtype.ext h))) G : Reg n) := by
  classical
  ext x y
  let f (i : Fin k) := (e i).val
  let loc (u : Config n) (i : Fin k) := u (f i)
  let out (u : Config n) := restrictOutsideConfiguration S u
  let E := ∀ v, v ≠ f a → v ≠ f b → x v = y v
  let I := ∀ i, i ≠ a → i ≠ b → loc x i = loc y i
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have he : E ↔ out x = out y ∧ I := by
    constructor
    · intro h
      refine ⟨funext fun v => h v.val (fun hh => v.2 (hh.symm ▸ (e a).2)) (fun hh => v.2 (hh.symm ▸ (e b).2)),?_⟩
      exact fun i ha hb => h (f i) (fun h => ha (hf h)) (fun h => hb (hf h))
    · rintro ⟨ho,hi⟩ v ha hb
      by_cases hv : v ∈ S
      · obtain ⟨i,hi'⟩ := e.surjective ⟨v,hv⟩
        have hv' : f i = v := congrArg Subtype.val hi'
        rw [←hv'] at ha hb ⊢
        exact hi i (fun h => ha (congrArg f h)) (fun h => hb (congrArg f h))
      · exact congrFun ho ⟨v,hv⟩
  rw [gate_entry]
  unfold place liftLocalMatrix
  by_cases ho : out x = out y
  · rw [if_pos ho]
    change (twoQubitLift a b hab G : Reg k) (loc x) (loc y) = _
    rw [gate_entry]
    by_cases hi : I
    · rw [if_pos hi,if_pos (he.mpr ⟨ho,hi⟩)]
    · rw [if_neg hi,if_neg (fun h => hi (he.mp h).2)]
  · rw [if_neg ho,if_neg (fun h => ho (he.mp h).1)]

/-- Relabel each gate location by e. Every spectator wire is idle. -/
def placeCircuit {n k : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) (C : TwoQubitCircuit k) : TwoQubitCircuit n where
  gateCount := C.gateCount
  gates := C.gates
  architecture := {
    sites := fun i => ((e (C.architecture.sites i).1).val,(e (C.architecture.sites i).2).val)
    distinct := fun i h => C.architecture.distinct i (e.injective (Subtype.ext h)) }

/-- Evaluation commutes with placement, with exactly the original gate count. -/
theorem placeCircuit_eval {n k : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) (C : TwoQubitCircuit k) :
    ((placeCircuit e C).eval : Reg n) = place e C.eval := by
  let g := fun i => C.architecture.gateLift i (C.gates i)
  let h := fun i => (placeCircuit e C).architecture.gateLift i (C.gates i)
  let F := (placeHom e).comp (unitary (Reg k)).subtype
  have hg (i) : F (g i) = (h i : Reg n) := place_gate e _ _ _ _
  let G := (unitary (Reg n)).subtype
  change G ((List.ofFn h).reverse.prod) = F ((List.ofFn g).reverse.prod)
  rw [map_list_prod,map_list_prod,List.map_reverse,List.map_reverse,List.map_ofFn,List.map_ofFn]
  exact congrArg (fun l : List (Reg n) => l.reverse.prod)
    (congrArg List.ofFn (funext fun i => (hg i).symm))

#print axioms placeCircuit_eval
end
end GaloisForLFunctions.HTGeometry.Subregister
