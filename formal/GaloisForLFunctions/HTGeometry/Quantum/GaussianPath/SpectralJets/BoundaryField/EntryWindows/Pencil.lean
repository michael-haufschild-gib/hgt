import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.GapDeterminant
import GaloisForLFunctions.HTGeometry.WeightedDeterminantDegree
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FirstReturnDates

/-! # A degree bound for the conditional gap polynomial -/

open Polynomial Set Matrix Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- In one field coordinate the matrix testing a fixed gap is affine. -/
def gapPencil (A Z : Matrix I I ℂ) (b : ℝ) : Matrix (I × I) (I × I) ℂ[X] :=
  fun i j => C ((Matrix.scalar (I × I) (b:ℂ)-gapOperator A) i j) - X*C (gapOperator Z i j)

theorem eval_gapPencil (A Z : Matrix I I ℂ) (b : ℝ) (y : ℝ) :
    (gapPencil A Z b).det.eval (y:ℂ)=(Matrix.scalar (I × I) (b:ℂ)-gapOperator (A+(y:ℂ) • Z)).det := by
  rw [←Polynomial.coe_evalRingHom,RingHom.map_det,gapOperator_affine]
  congr 1
  ext i j
  simp only [gapPencil,RingHom.mapMatrix_apply,Matrix.map_apply,Polynomial.coe_evalRingHom,eval_sub,
    eval_C,eval_mul,eval_X,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem gapPencil_degree (A Z : Matrix I I ℂ) (b : ℝ) :
    (gapPencil A Z b).det.natDegree≤Fintype.card I^2 := by
  let e := Fintype.equivFin (I × I)
  let M := gapPencil A Z b
  have hd (i j : I × I) : (M i j).natDegree≤1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp only [natDegree_C]; omega
    · exact Polynomial.natDegree_mul_le.trans (by simp only [natDegree_X,natDegree_C,add_zero,le_refl])
  have h := natDegree_det_le_of_degree_le (Matrix.reindex e e M) (fun _ => 0) (fun _ => 1)
    (fun i j => by rw [Nat.cast_zero,zero_add]; exact Polynomial.natDegree_le_iff_degree_le.mp (hd (e.symm i) (e.symm j)))
  simpa only [Matrix.det_reindex_self,Finset.sum_const_zero,zero_add,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one,Fintype.card_prod,pow_two,M] using h

/-- Almost every frozen background gives a nonzero polynomial for every
nonzero forecast gap, including forecasts chosen after seeing the background. -/
theorem gaussian_gapPencil_nonzero :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ a b : ℝ, b≠0 →
      (gapPencil (boundaryHamiltonian ω k a) (SpinExtension.lastPauli (k+2) 2) b).det≠0 := by
  filter_upwards [gaussian_boundary_frequency_avoidance] with ω hω
  intro k a b hb
  obtain ⟨B,hB,ha⟩ := hω k {b} (countable_singleton _)
  obtain ⟨y,hy⟩ := hB.exists_notMem
  let E := (boundaryHermitian ω k y).eigenvalues
  have hsep (i j : Fin (k+3)→Bool) : E i-E j≠b := by
    by_cases hij : i=j
    · subst j; rwa [sub_self,ne_comm]
    obtain ⟨m,hm,hs,hd⟩ := gap_packet E hij
    exact fun he => ha y hy m hm hs (hd.trans he)
  intro hz
  have hu := congrArg (fun p : ℂ[X] => p.eval ((y-a:ℝ):ℂ)) hz
  rw [eval_gapPencil,Polynomial.eval_zero] at hu
  have he : boundaryHamiltonian ω k a+((y-a:ℝ):ℂ) • SpinExtension.lastPauli (k+2) 2=boundaryHamiltonian ω k y := by
    rw [boundaryHamiltonian,boundaryHamiltonian,add_assoc,←add_smul,←Complex.ofReal_add,show a+(y-a)=y by ring]
  rw [he] at hu
  rw [gap_determinant _ (boundaryHermitian ω k y)] at hu
  obtain ⟨p,_,hp⟩ := Finset.prod_eq_zero_iff.mp hu
  exact hsep p.1 p.2 (by exact_mod_cast (sub_eq_zero.mp hp).symm)

#print axioms gaussian_gapPencil_nonzero
#print axioms gapPencil_degree
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
