import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.StatePreparation

/-! # Exact circuits for spectral phases in an arbitrary eigenbasis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section
private abbrev Config (n : ℕ) := Fin n → Bool
private def origin (n : ℕ) : Config n := fun _ => false
/-- A phase on one basis vector, equal to one on its complement. -/
def pointPhase {α : Type*} [DecidableEq α] (i : α) (z : ℂ) (x : α) :=
  if x=i then z else 1

/-- When column i of a unitary is supported on one row, that row vanishes in
every other column. -/
private theorem isolated_row {α : Type*} [Fintype α] [DecidableEq α]
    (R : Matrix α α ℂ) (hR : R ∈ unitary (Matrix α α ℂ)) (a i : α)
    (hcol : ∀ x, x ≠ a → R x i=0) {j : α} (hj : j≠i) : R a j=0 := by
  have h (k : α) : star (R a i)*R a k = (1:Matrix α α ℂ) i k := by
    have eq := congrFun (congrFun (Unitary.mem_iff.mp hR).1 i) k
    change (∑ x, star (R x i)*R x k) = _ at eq
    rw [Finset.sum_eq_single a] at eq
    · exact eq
    · intro b _ hb; rw [hcol b hb,star_zero,zero_mul]
    · simp
  have hdiag := h i
  rw [Matrix.one_apply_eq] at hdiag
  have hne : star (R a i) ≠ 0 := by intro he; simp [he] at hdiag
  exact (mul_eq_zero.mp (by simpa [Matrix.one_apply,hj.symm] using h j : star (R a i)*R a j=0)).resolve_left hne

/-- Two state preparations and one computational-basis point phase. -/
def eigenphaseCost (n : ℕ) := 2*(n*(2*(2^n*(2*n+1)+1))) + 2^n*(2*n+1)

/-- An exact phase rotation about one column of an arbitrary eigenbasis. -/
theorem eigenline_phase {n : ℕ} (hn : 2 ≤ n) (V : Matrix.unitaryGroup (Config n) ℂ)
    (i : Config n) (z : ℂ) (hz : ‖z‖=1) :
    Realizes (eigenphaseCost n) ((V : Register n)*diagonal (pointPhase i z)*star (V : Register n)) := by
  let v (x : Config n) := (V : Register n) x i
  obtain ⟨C,hC,hcol⟩ := prepare_to_zero hn v
  let Q : Register n := C.eval
  let R : Register n := Q*(V : Register n)
  let D₀ := diagonal (pointPhase (origin n) z)
  let D := diagonal (pointPhase i z)
  have hQ : star Q*Q=1 := (Unitary.mem_iff.mp C.eval.2).1
  have hV : (V : Register n)*star (V : Register n)=1 := (Unitary.mem_iff.mp V.2).2
  have hr (x) (hx : x≠origin n) : R x i=0 := hcol x hx
  have hr' {j : Config n} (hj : j ≠ i) : R (origin n) j=0 :=
    isolated_row R (mul_mem C.eval.2 V.2) (origin n) i hr hj
  have hcomm : D₀*R=R*D := by
    ext x y
    simp only [D₀,D,diagonal_mul,mul_diagonal,pointPhase]
    by_cases hx : x=origin n <;> by_cases hy : y=i
    · simp [hx,hy,mul_comm]
    · simp [hx,hy,hr' hy]
    · simp [hx,hy,hr _ hx]
    · simp [hx,hy]
  have hchange : star Q*D₀*Q = (V : Register n)*D*star (V : Register n) := by
    calc
      _ = (star Q*(D₀*R))*star (V : Register n) := by
        simp only [R,mul_assoc,hV,mul_one]
      _ = _ := by rw [hcomm]; simp only [R,← mul_assoc,hQ,one_mul]
  have hcost : Realizes (n*(2*(2^n*(2*n+1)+1))) Q := ⟨1,norm_one,C,hC,by simp [Q]⟩
  have hphase := diagonal_phases hn (pointPhase (origin n) z) (fun x => by
    by_cases hh : x=origin n <;> simp [pointPhase,hh,hz])
  change Realizes _ ((V : Register n)*D*star (V : Register n))
  rw [← hchange]
  convert (hcost.adjoint.mul hphase).mul hcost using 1
  dsimp [eigenphaseCost]
  omega

/-- Synthesize an arbitrary diagonal in an arbitrary fixed eigenbasis by
applying one phase to each of its eigenlines. -/
theorem eigenbasis_phases {n : ℕ} (hn : 2 ≤ n) (V : Matrix.unitaryGroup (Config n) ℂ)
    (p : Config n → ℂ) (hp : ∀ x, ‖p x‖=1) :
    Realizes ((4*n+1)*(2*n+2)*(2^n)^2) ((V : Register n)*diagonal p*star (V : Register n)) := by
  classical
  let f (s : Finset (Config n)) (x : Config n) := if x∈s then p x else 1
  let U (s : Finset (Config n)) := (V : Register n)*diagonal (f s)*star (V : Register n)
  have hV := Unitary.mem_iff.mp V.2
  have hconj (B C : Register n) :
      ((V : Register n)*B*star (V : Register n))*((V : Register n)*C*star (V : Register n)) =
      (V : Register n)*(B*C)*star (V : Register n) := by
    calc
      _ = (V : Register n)*B*(star (V : Register n)*(V : Register n))*C*star (V : Register n) := by
        simp only [mul_assoc]
      _ = _ := by rw [hV.1,mul_one]; simp only [mul_assoc]
  have h (s : Finset (Config n)) : Realizes (s.card*eigenphaseCost n) (U s) := by
    induction s using Finset.induction_on with
    | empty => simpa [U,f,hV.2] using Realizes.one n
    | @insert i s hi ih =>
      let D := diagonal (pointPhase i (p i))
      have hf : diagonal (f (insert i s))=D*diagonal (f s) := by
        rw [diagonal_mul_diagonal]
        congr 1; funext x
        by_cases hx : x=i
        · subst x; simp [pointPhase,f,hi]
        · simp [pointPhase,f,hx]
      have he : U (insert i s)=((V : Register n)*D*star (V : Register n))*U s := by
        simp only [U,hf,hconj]
      rw [he,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,Nat.add_comm]
      exact (eigenline_phase hn V i (p i) (hp i)).mul ih
  obtain ⟨z,hz,C,hC,he⟩ := h Finset.univ
  refine ⟨z,hz,C,?_,by simpa [U,f] using he⟩
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hC
  apply hC.trans
  dsimp [eigenphaseCost]
  have hD : 1 ≤ (2:ℕ)^n := Nat.one_le_two_pow
  nlinarith only [Nat.mul_le_mul_left (4*n*(2^n)) hD,hD]

/-- At every time, every Hermitian evolution on n qubits has an exact
ancilla-free projective circuit of size at most (4n+1)(2n+2)4^n. -/
theorem exact_evolution_gate_cap {n : ℕ} (hn : 2 ≤ n) (H : selfAdjoint (Register n)) (t : ℝ) :
    Realizes ((4*n+1)*(2*n+2)*(2^n)^2) (unitaryEvolution H.val t) := by
  rw [unitaryEvolution_spectral H.2.isHermitian]
  apply eigenbasis_phases hn _ _
  intro x
  simp [Complex.norm_exp]

#print axioms exact_evolution_gate_cap
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
