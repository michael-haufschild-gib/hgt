import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.ExponentialWords
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.OrbitContacts
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw

/-! # Finite exponential expansions of polynomial tests on a physical orbit -/

open Matrix Finset Set
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount
noncomputable section

private theorem entry_pair {N d : ℕ} (e : Bits N ≃ Fin (d+1))
    (H : selfAdjoint (Square (Bits N))) (i j : Bits N) :
    ∃ u v : Word, ∀ t : ℝ, evaluate t u=relativeOrbit e H t i j ∧
      evaluate t v=conj (relativeOrbit e H t i j) := by
  let E := H.2.isHermitian.eigenvalues ∘ e.symm
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let y (k : Bits N) : ℂ := (Fin.cases 0 (RHTower.zeroProjectiveFrequency E) (e k) : ℝ)*Complex.I
  let c (k : Bits N) := V.val i k*(V⁻¹).val k j
  have he (t : ℝ) : relativeOrbit e H t i j=∑ k, c k*Complex.exp (y k*t) := by
    change ((V.val * diagonal _)*(V⁻¹).val) i j=_
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal,RHTower.fourier_projectiveChoiPhase_eq_exp]
    dsimp only [y,c,E]
    push_cast
    ring_nf
  refine ⟨∑ k, AddMonoidAlgebra.single (y k) (c k),
    ∑ k, AddMonoidAlgebra.single (conj (y k)) (conj (c k)),?_⟩
  intro t
  rw [he]
  simp only [map_sum,evaluate_single,map_mul,←Complex.exp_conj,Complex.conj_ofReal]
  exact ⟨rfl,rfl⟩

private theorem coordinate_word {N d : ℕ} (e : Bits N ≃ Fin (d+1))
    (H : selfAdjoint (Square (Bits N))) (k : Bits N × Bits N × Bool) :
    ∃ w : Word, ∀ t : ℝ, evaluate t w=(entryEval (RingHom.id ℝ) (relativeOrbit e H t) (MvPolynomial.X k):ℂ) := by
  obtain ⟨i,j,b⟩ := k
  obtain ⟨u,v,huv⟩ := entry_pair e H i j
  cases b
  · refine ⟨algebraMap ℂ Word (2:ℂ)⁻¹*(u+v),?_⟩
    intro t
    rw [map_mul,AlgHom.commutes,map_add,(huv t).1,(huv t).2,Complex.add_conj]
    simp only [entryEval,MvPolynomial.eval₂Hom_X',Bool.false_eq_true,if_false,
      Algebra.algebraMap_self, RingHom.id_apply,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  · refine ⟨algebraMap ℂ Word (-(Complex.I/2))*(u-v),?_⟩
    intro t
    rw [map_mul,AlgHom.commutes,map_sub,(huv t).1,(huv t).2,Complex.sub_conj]
    simp only [entryEval,MvPolynomial.eval₂Hom_X',if_true,Algebra.algebraMap_self,
      RingHom.id_apply,Complex.ofReal_mul,Complex.ofReal_ofNat]
    linear_combination -((relativeOrbit e H t i j).im:ℂ)*Complex.I_sq

/-- Every real polynomial in relative matrix entries restricts to one
real-valued exponential sum, including for repeated energies. -/
theorem polynomial_word {N d : ℕ} (e : Bits N ≃ Fin (d+1))
    (H : selfAdjoint (Square (Bits N))) (p : EntryPolynomial N ℝ) :
    ∃ w : Word, ∀ t : ℝ, evaluate t w=(entryEval (RingHom.id ℝ) (relativeOrbit e H t) p:ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨algebraMap ℂ Word (r:ℂ),fun t => ?_⟩
    rw [AlgHom.commutes]; simp [entryEval]
  | add p q hp hq =>
    obtain ⟨u,hu⟩ := hp
    obtain ⟨v,hv⟩ := hq
    exact ⟨u+v,fun t => by rw [map_add,hu,hv,map_add,Complex.ofReal_add]⟩
  | mul_X p i hp =>
    obtain ⟨u,hu⟩ := hp
    obtain ⟨v,hv⟩ := coordinate_word e H i
    exact ⟨u*v,fun t => by rw [map_mul,hu,hv,map_mul,Complex.ofReal_mul]⟩

#print axioms polynomial_word
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount

