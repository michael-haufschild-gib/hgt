import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.WordStep
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.PathFactors
import GaloisForLFunctions.HTGeometry.PauliProductLaw

/-! # Real four-site Pauli expansion of a shifted path Hamiltonian squared -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev Word (n : ℕ) := Fin n → Option (Fin 3)

private theorem weight_product {n : ℕ} (P Q : Word n) :
    pauliWeight (fun i => optMul (P i) (Q i)) ≤ pauliWeight P+pauliWeight Q := by
  classical
  unfold pauliWeight
  refine (Finset.card_le_card (t := (Finset.univ.filter fun i => P i ≠ none) ∪
    (Finset.univ.filter fun i => Q i ≠ none)) ?_).trans Finset.card_union_le
  intro i hi
  by_contra h
  have hz : P i=none ∧ Q i=none := by simpa only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
    true_and,not_or,not_not] using h
  exact (Finset.mem_filter.mp hi).2 (by rw [hz.1,hz.2]; rfl)

private theorem path_weight {n : ℕ} (l : PathLabel n) : pauliWeight (pathWord l) ≤ 2 := by
  classical
  rw [pauliWeight]
  rcases l with ⟨s,a⟩ | ⟨e,ab⟩
  · apply (Finset.card_le_card (t := {s}) ?_).trans (by simp)
    intro i hi
    by_contra hn
    have h : i ≠ s := by simpa using hn
    simpa [pathWord,onsiteWord,h] using (Finset.mem_filter.mp hi).2
  · apply (Finset.card_le_card (t := {e.castSucc,e.succ}) ?_).trans
      ((Finset.card_insert_le _ _).trans (by simp))
    intro i hi
    by_contra hn
    have h : i ≠ e.castSucc ∧ i ≠ e.succ := by simpa using hn
    simpa [pathWord,couplingWord,h.1,h.2] using (Finset.mem_filter.mp hi).2

/-- Hermitian symmetrization of a complex Pauli expansion replaces
each coefficient by its real part, also when the labels repeat. -/
private theorem real_parts {I : Type*} [Fintype I] {n : ℕ} (P : I → Word n) (z : I → ℂ)
    (A : Reg n) (ha : star A=A) (he : A=∑ i, z i • finitePauliMatrix (P i)) :
    A = ∑ i, (z i).re • finitePauliMatrix (P i) := by
  classical
  calc
    A = (1/2:ℂ) • (A+star A) := by rw [ha,←two_smul ℂ A,smul_smul]; norm_num
    _ = ∑ i, (z i).re • finitePauliMatrix (P i) := by
      rw [he,star_sum,←Finset.sum_add_distrib,Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_smul,show star (finitePauliMatrix (P i))=finitePauliMatrix (P i) from finitePauliMatrix_isHermitian _,
        ←add_smul,smul_smul,←algebraMap_smul ℂ (z i).re]
      congr 1
      change (1/2:ℂ)*(z i+star (z i))=((z i).re:ℂ)
      rw [show z i+star (z i)=(2:ℂ)*(z i).re by apply Complex.ext <;> simp <;> ring]
      ring

/-- Squaring an offset path generator gives at most (J+1)² real Pauli
terms, each supported on at most four sites. -/
theorem shifted_square_words {n : ℕ} (u : PathShell n) (a : ℝ) :
    let L := Option (PathLabel n)
    ∃ (P : L×L → Word (n+2)) (c : L×L → ℝ), (∀ i, pauliWeight (P i) ≤ 4) ∧
      (pathHamiltonian u-(a:ℂ) • (1 : Reg (n+2)))^2=∑ i, c i • finitePauliMatrix (P i) := by
  classical
  intro L
  let B : L → Word (n+2) := fun i => i.elim (fun _ => none) pathWord
  let b : L → ℝ := fun i => i.elim (-a) (fun l => u l)
  let H := pathHamiltonian u-(a:ℂ) • (1 : Reg (n+2))
  have hb : ∀ i, pauliWeight (B i) ≤ 2 := by
    rintro (_|l)
    · simp [B,pauliWeight]
    · exact path_weight l
  have he : H=∑ i : L, (b i:ℂ) • finitePauliMatrix (B i) := by
    rw [Fintype.sum_option]
    simp only [B,b,Option.elim_none,Option.elim_some,Complex.ofReal_neg,finitePauliMatrix_const_none,neg_smul]
    rw [←pathHamiltonian_eq_sum]
    dsimp only [H]
    abel
  have hH : star H=H := by
    dsimp only [H]
    rw [star_sub,star_smul,star_one,(isSelfAdjoint_pathHamiltonian u).star_eq]
    simp
  let P (v : L×L) (i : Fin (n+2)) := optMul (B v.1 i) (B v.2 i)
  let z (v : L×L) : ℂ := ((b v.1:ℂ)*(b v.2:ℂ))*(∏ i, optPhase (B v.1 i) (B v.2 i))
  have hprod : H^2=∑ v : L×L, z v • finitePauliMatrix (P v) := by
    rw [sq,he,Finset.sum_mul_sum,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_smul_comm,finitePauliMatrix_mul,smul_smul]
  exact ⟨P,fun v => (z v).re,fun v => (weight_product _ _).trans (Nat.add_le_add (hb v.1) (hb v.2)),
    real_parts P z _ (by rw [sq,star_mul,hH]) hprod⟩

/-- Evolution under the quadratic spectral generator has a one-step
compiler at a quadratic gate budget and quadratic short-time error. -/
theorem shifted_square_step {n : ℕ} (u : PathShell n) (a : ℝ) :
    ∃ A > (0:ℝ), ∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) (A*t^2)
      (((Fintype.card (PathLabel n))+1)^2*9)
      (unitaryEvolution ((pathHamiltonian u-(a:ℂ) • (1 : Reg (n+2)))^2) t) := by
  obtain ⟨P,c,hp,he⟩ := shifted_square_words u a
  have h := sparse_word_step (by omega : 2≤n+2) P c 4 hp
  rw [←he] at h
  simpa only [Fintype.card_prod,Fintype.card_option,sq] using h

#print axioms shifted_square_words
#print axioms shifted_square_step
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
