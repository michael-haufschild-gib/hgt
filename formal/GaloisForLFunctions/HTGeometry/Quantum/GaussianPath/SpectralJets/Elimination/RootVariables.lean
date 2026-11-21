import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.WeightedHankel

/-! # Elimination of several independent spectral root variables -/

open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} {D : ℕ}

/-- A parameter alphabet with k additional root variables. -/
def RootVariables (ι : Type*) : ℕ → Type _
  | 0 => ι
  | k+1 => Option (RootVariables ι k)

instance rootVariablesFintype [Fintype ι] (k : ℕ) : Fintype (RootVariables ι k) := by
  induction k with
  | zero => exact (inferInstance : Fintype ι)
  | succ k ih =>
    letI := ih
    exact (inferInstance : Fintype (Option (RootVariables ι k)))

/-- Inclusion of parameters into the enlarged alphabet. -/
def baseVariable : (k : ℕ) → ι → RootVariables ι k
  | 0, i => i
  | k+1, i => some (baseVariable k i)

/-- The i-th root variable in an alphabet with k root variables. -/
def rootVariable : (k : ℕ) → Fin k → RootVariables ι k
  | 0 => Fin.elim0
  | k+1 => Fin.cases none (fun j => some (rootVariable k j))

/-- Assign independent choices of eigenvalues to the root variables. -/
def assignRoots (x : ι → ℂ) : (k : ℕ) → (Fin k → ℂ) → RootVariables ι k → ℂ
  | 0, _, i => x i
  | k+1, v, i => i.elim (v 0) (assignRoots x k fun j => v j.succ)

@[simp] theorem assignRoots_base (x : ι → ℂ) (k : ℕ) (v : Fin k → ℂ) (i : ι) :
    assignRoots x k v (baseVariable k i) = x i := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _

@[simp] theorem assignRoots_root (x : ι → ℂ) (k : ℕ) (v : Fin k → ℂ) (i : Fin k) :
    assignRoots x k v (rootVariable k i) = v i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih => exact Fin.cases rfl (fun j => ih _ j) i

/-- Extend a polynomial family to a larger parameter space by ignoring the new coordinates. -/
def extendPencil (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ)) (k : ℕ) :=
  (MvPolynomial.rename (R := ℂ) (baseVariable (ι := ι) k)).toRingHom.mapMatrix M

theorem extend_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (k : ℕ) (i j : Fin D) :
    ((extendPencil M k) i j).totalDegree ≤ 1 :=
  (totalDegree_rename_le (baseVariable k) (M i j)).trans (hM i j)

theorem extend_trace (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι → ℂ) (k : ℕ) (v : Fin k → ℂ) (a : ℕ) :
    eval (assignRoots x k v) ((extendPencil M k)^a).trace = eval x (M^a).trace := by
  have he : (eval (assignRoots x k v)).mapMatrix (extendPencil M k) = (eval x).mapMatrix M := by
    ext i j
    change eval (assignRoots x k v) (rename (baseVariable k) (M i j)) = eval x (M i j)
    rw [eval_rename]
    exact congrArg (fun z => eval z (M i j)) (funext (assignRoots_base x k v))
  rw [← trace_mapMatrix,map_pow,he,← map_pow,trace_mapMatrix]

variable [Fintype ι]

/-- Eliminate the root variables one at a time. -/
def eliminateRoots (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ)) :
    (k : ℕ) → MvPolynomial (RootVariables ι k) ℂ → MvPolynomial ι ℂ
  | 0, p => p
  | k+1, p => eliminateRoots M k (rootProduct (extendPencil M k) p)

/-- Degree growth is at most one fixed polynomial factor in D per root variable. -/
theorem eliminateRoots_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (k : ℕ) (p : MvPolynomial (RootVariables ι k) ℂ) :
    (eliminateRoots M k p).totalDegree+1 ≤ (D+2*D*D+1)^k*(p.totalDegree+1) := by
  induction k with
  | zero => exact (Nat.le_refl _).trans_eq (by rw [pow_zero,one_mul]; rfl)
  | succ k ih =>
    let A := D+2*D*D+1
    have h := rootProduct_degree (extendPencil M k) (extend_degree M hM k) p
    have h₁ : D ≤ A := by dsimp [A]; omega
    have h₂ : 2*D*D+1 ≤ A := by dsimp [A]; omega
    have hb : (rootProduct (extendPencil M k) p).totalDegree+1 ≤ A*(p.totalDegree+1) := by
      refine (Nat.add_le_add_right h 1).trans ?_
      calc D*(p.totalDegree+2*D)+1 = D*p.totalDegree+(2*D*D+1) := by ring
           _ ≤ A*p.totalDegree+A := Nat.add_le_add (Nat.mul_le_mul_right _ h₁) h₂
           _ = _ := by ring
    exact (ih _).trans ((Nat.mul_le_mul_left (A^k) hb).trans_eq (by rw [pow_succ,mul_assoc]))

/-- At a simple spectrum, the eliminated polynomial vanishes exactly when some
assignment to the independent root variables makes the input vanish. -/
theorem eval_eliminateRoots_eq_zero_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι → ℂ) (E : Fin D → ℂ) (hi : Function.Injective E)
    (ht : ∀ k : ℕ, eval x (M^k).trace = ∑ j, E j^k)
    (k : ℕ) (p : MvPolynomial (RootVariables ι k) ℂ) :
    eval x (eliminateRoots M k p) = 0 ↔
      ∃ s : Fin k → Fin D, eval (assignRoots x k (fun j => E (s j))) p = 0 := by
  induction k with
  | zero => exact ⟨fun h => ⟨Fin.elim0,h⟩,fun ⟨_,h⟩ => h⟩
  | succ k ih =>
    rw [eliminateRoots,ih]
    have hstep (s : Fin k → Fin D) := eval_rootProduct_eq_zero_iff (extendPencil M k)
      (assignRoots x k (fun j => E (s j))) E hi
      (fun a => (extend_trace M x k _ a).trans (ht a)) p
    constructor
    · rintro ⟨s,hs⟩
      obtain ⟨j,hj⟩ := (hstep s).mp hs
      refine ⟨Fin.cons j s,?_⟩
      have ha : assignRoots x (k+1) (fun i => E ((show Fin (k+1) → Fin D from Fin.cons j s) i)) =
          (fun o : Option (RootVariables ι k) => o.elim (E j) (assignRoots x k (fun i => E (s i)))) := by
        funext o
        cases o <;> rfl
      rw [ha]
      exact hj
    · rintro ⟨s,hs⟩
      refine ⟨fun j => s j.succ,(hstep _).mpr ⟨s 0,hs⟩⟩

#print axioms eliminateRoots_degree
#print axioms eval_eliminateRoots_eq_zero_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets
