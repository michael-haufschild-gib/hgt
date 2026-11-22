import GaloisForLFunctions.HTGeometry.AffineEigenbranchGeneralSecondOrderLaw
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.SimpleSpectrumAnalyticBranch

/-! # Analytic slopes in the physical energy eigenbasis -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The analytic eigenbranch through each simple energy has field derivative
equal to the expectation of that field in the corresponding eigenstate. -/
theorem energy_basis_slopes (H Z : Mat I) (hH : H.IsHermitian) (hi : Function.Injective hH.eigenvalues) :
    let V : Mat I := hH.eigenvectorUnitary
    ∃ f : I → ℂ → ℂ, ∀ j, AnalyticAt ℂ (f j) 0 ∧ f j 0=(hH.eigenvalues j:ℂ) ∧
      (∀ᶠ s in 𝓝 0, matrixCharpolyRelation (H+s • Z,f j s)=0) ∧
      deriv (f j) 0=(star V*Z*V) j j := by
  intro V
  let E (j : I) := (hH.eigenvalues j:ℂ)
  let B := star V*Z*V
  have hE : Function.Injective E := Complex.ofReal_injective.comp hi
  have ha : AnalyticAt ℂ (fun s : ℂ => diagonal E+s • B) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  choose f hf hbase hr using analyticMatrixFamily_eigenvalueBranch ha E hE (by rw [zero_smul,add_zero])
  have hV : V ∈ unitary (Mat I) := hH.eigenvectorUnitary.2
  have hv := Unitary.mem_iff.mp hV
  have hunit : IsUnit V := ⟨⟨V,star V,hv.2,hv.1⟩,rfl⟩
  have hdiag : star V*H*V=diagonal E := by
    have hh : H=V*diagonal E*star V := isHermitian_eq_conj_diagonal hH
    rw [hh]
    simp only [mul_assoc,hv.1,mul_one]
    rw [←mul_assoc,hv.1,one_mul]
  have heq (s : ℂ) : V⁻¹*(H+s • Z)*V=diagonal E+s • B := by
    rw [inv_eq_star_of_mem_unitary hV,Matrix.mul_add,Matrix.add_mul,hdiag,Matrix.mul_smul,Matrix.smul_mul]
  refine ⟨f,fun j => ⟨hf j,hbase j,?_,affineEigenbranch_firstDerivative_eq_diagonal E hE B j _ (hf j)
    (hbase j) (hr j)⟩⟩
  filter_upwards [hr j] with s hs
  rwa [←matrixCharpolyRelation_conj ((Matrix.isUnit_iff_isUnit_det V).mp hunit),heq]

#print axioms energy_basis_slopes
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
