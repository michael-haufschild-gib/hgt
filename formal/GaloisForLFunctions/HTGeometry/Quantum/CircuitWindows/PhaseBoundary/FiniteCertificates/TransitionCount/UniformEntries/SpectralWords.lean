import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries.Families
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries.CommonEquations
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw

/-! # Uniform bandwidth of matrix-and-tolerance tests on physical trajectories -/

open Matrix Finset Polynomial
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
noncomputable section

private abbrev Inputs (N : ℕ) := selfAdjoint (Square (Bits N)) × ℝ
private abbrev width {N : ℕ} (x : Inputs N) := circuitHamiltonianSpectralWidth x.1

/-- Each entry and its conjugate need at most one exponential per energy.
Removing the reference phase places all frequencies within one bandwidth. -/
private theorem entry_terms {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N)))
    (i j : Bits N) : ∃ u v : Word,
    wordBounds (Fintype.card (Bits N)) (circuitHamiltonianSpectralWidth H) u ∧
    wordBounds (Fintype.card (Bits N)) (circuitHamiltonianSpectralWidth H) v ∧
    ∀ t : ℝ, evaluate t u=relativeOrbit e H t i j ∧ evaluate t v=conj (relativeOrbit e H t i j) := by
  let E := H.2.isHermitian.eigenvalues
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let y (k : Bits N) : ℂ := ((E (e.symm 0)-E k : ℝ):ℂ)*Complex.I
  let c (k : Bits N) := V.val i k*(V⁻¹).val k j
  have hy (k : Bits N) : |(y k).im|≤circuitHamiltonianSpectralWidth H := by
    simp only [y,Complex.mul_I_im,Complex.ofReal_re]
    rw [abs_le]
    change -(_-_)≤E (e.symm 0)-E k ∧ E (e.symm 0)-E k≤_-_
    have bounds (l : Bits N) := And.intro (Finset.inf'_le E (Finset.mem_univ l)) (Finset.le_sup' E (Finset.mem_univ l))
    constructor <;> linarith only [(bounds k).1,(bounds k).2,(bounds (e.symm 0)).1,(bounds (e.symm 0)).2]
  have he (t : ℝ) : relativeOrbit e H t i j=∑ k, c k*Complex.exp (y k*t) := by
    change ((V.val * diagonal _)*(V⁻¹).val) i j=_
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal,RHTower.fourier_projectiveChoiPhase_eq_exp]
    have hfreq : Fin.cases 0 (RHTower.zeroProjectiveFrequency (E ∘ e.symm)) (e k)=E (e.symm 0)-E k := by
      generalize hr : e k=r
      have hk : e.symm r=k := by rw [←hr,e.symm_apply_apply]
      rw [←hk]
      refine Fin.cases ?_ (fun z => ?_) r
      · simp
      · rfl
    simp only [hfreq,c,y,E,Complex.ofReal_mul,Complex.ofReal_sub]
    push_cast
    ring_nf
  refine ⟨∑ k, AddMonoidAlgebra.single (y k) (c k),
    ∑ k, AddMonoidAlgebra.single (conj (y k)) (conj (c k)),?_,?_,?_⟩
  · exact wordBounds.sum_single univ y c _ (fun k _ => hy k)
  · exact wordBounds.sum_single univ _ _ _ (fun k _ => by simpa only [Complex.conj_im,abs_neg] using hy k)
  · intro t
    rw [he]
    simp only [map_sum,evaluate_single,map_mul,←Complex.exp_conj,Complex.conj_ofReal]
    exact ⟨rfl,rfl⟩

private theorem coordinate_expansion {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (k : Bits N×Bits N×Bool) :
    uniformExpansion (width (N:=N)) (fun x t => (entryEval (RingHom.id ℝ)
      (relativeOrbit e x.1 t) (MvPolynomial.X k):ℂ)) := by
  obtain ⟨i,j,b⟩ := k
  let U (x : Inputs N) (t : ℝ) := relativeOrbit e x.1 t i j
  have hW (x : Inputs N) := circuitHamiltonianSpectralWidth_nonneg x.1
  have hU : uniformExpansion width U ∧ uniformExpansion width (fun x t => conj (U x t)) := by
    constructor
    · refine ⟨_,1,fun x => ?_⟩
      obtain ⟨u,v,hu,_,he⟩ := entry_terms e x.1 i j
      exact ⟨u,by simpa only [Nat.cast_one,one_mul] using hu,fun t => (he t).1⟩
    · refine ⟨_,1,fun x => ?_⟩
      obtain ⟨u,v,_,hv,he⟩ := entry_terms e x.1 i j
      exact ⟨v,by simpa only [Nat.cast_one,one_mul] using hv,fun t => (he t).2⟩
  cases b
  · have h := (uniformExpansion.const width (fun _ : Inputs N => (2:ℂ)⁻¹)).mul (hU.1.add hW hU.2)
    convert h using 1
    funext x t
    simp only [U,entryEval,MvPolynomial.eval₂Hom_X',Bool.false_eq_true,if_false,Complex.add_conj]
    push_cast
    ring
  · have hneg := (uniformExpansion.const width (fun _ : Inputs N => (-1:ℂ))).mul hU.2
    have h := (uniformExpansion.const width (fun _ : Inputs N => -(Complex.I/2))).mul (hU.1.add hW hneg)
    convert h using 1
    funext x t
    simp only [U,entryEval,MvPolynomial.eval₂Hom_X',if_true,neg_one_mul,←sub_eq_add_neg,Complex.sub_conj]
    push_cast
    linear_combination ((relativeOrbit e x.1 t i j).im:ℂ)*Complex.I_sq

private theorem matrix_expansion {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (p : EntryPolynomial N ℝ) :
    uniformExpansion (width (N:=N)) (fun x t => (entryEval (RingHom.id ℝ) (relativeOrbit e x.1 t) p:ℂ)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [entryEval,MvPolynomial.eval₂Hom_C,RingHom.id_apply] using uniformExpansion.const width (fun _ : Inputs N => (r:ℂ))
  | add p q hp hq => simpa only [map_add,Complex.ofReal_add] using hp.add (fun x => circuitHamiltonianSpectralWidth_nonneg x.1) hq
  | mul_X p k hp => simpa only [map_mul,Complex.ofReal_mul] using hp.mul (coordinate_expansion e k)

/-- The zero-count constant for a fixed matrix-and-height equation can be
chosen before the Hamiltonian and the height. -/
theorem physical_test_zero_bound {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (p : Polynomial (EntryPolynomial N ℝ)) :
    ∃ C ≥ (0:ℝ), ∀ x : Inputs N,
      let f (t : ℝ) := testEval (relativeOrbit e x.1 t,x.2) p
      (∃ t, f t≠0) → ∀ a b : ℝ, a<b → ∀ Z : Finset ℝ,
      (∀ t∈Z, t∈Set.Icc a b) → (∀ t∈Z, f t=0) →
      (Z.card:ℝ)≤C*(1+(b-a)*width x) := by
  let val (q : Polynomial (EntryPolynomial N ℝ)) (x : Inputs N) (t : ℝ) : ℂ :=
    testEval (relativeOrbit e x.1 t,x.2) q
  have h (q) : uniformExpansion width (val q) := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simpa only [val,map_add,Complex.ofReal_add] using hp.add (fun x => circuitHamiltonianSpectralWidth_nonneg x.1) hq
    | monomial n c =>
      simpa only [val,testEval,appendEval,eval₂RingHom_apply,eval₂_monomial,Complex.ofReal_mul,Complex.ofReal_pow] using
        (matrix_expansion e c).mul (uniformExpansion.const width (fun x : Inputs N => (x.2:ℂ)^n))
  obtain ⟨C,hC,hbound⟩ := (h p).zero_bound (fun x => circuitHamiltonianSpectralWidth_nonneg x.1) (fun _ _ => Complex.ofReal_im _)
  refine ⟨C,hC,fun x f hn a b hab Z hZ hz => hbound x ?_ a b hab Z hZ ?_⟩
  · obtain ⟨t,ht⟩ := hn
    exact ⟨t,Complex.ofReal_ne_zero.mpr ht⟩
  · exact fun t ht => Complex.ofReal_zero ▸ congrArg Complex.ofReal (hz t ht)

#print axioms physical_test_zero_bound
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
