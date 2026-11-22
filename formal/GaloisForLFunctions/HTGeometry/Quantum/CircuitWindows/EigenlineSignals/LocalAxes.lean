import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.SpinRelations
import GaloisForLFunctions.HTGeometry.MatrixRankSubadditive
import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction

/-! # Unit spin directions obeying two real linear constraints -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
open UntouchedSites

/-- Two real tests leave a unit vector of three spin coefficients. -/
theorem exists_unit_axis (M : Matrix (Fin 2) (Fin 3) ℝ) :
    ∃ r : Fin 3→ℝ, r ⬝ᵥ r=1 ∧ M *ᵥ r=0 := by
  let L := M.mulVecLin
  have hk : L.ker ≠ ⊥ := by
    intro h
    have hd := LinearMap.finrank_le_finrank_of_injective (f:=L) (LinearMap.ker_eq_bot.mp h)
    simp at hd
  obtain ⟨v,hv,hne⟩ := L.ker.ne_bot_iff.mp hk
  have hs := dotProduct_self_pos hne
  let u := Real.sqrt (v ⬝ᵥ v)
  have hu : 0 < u := Real.sqrt_pos.mpr hs
  have hu₂ : u^2=v ⬝ᵥ v := Real.sq_sqrt hs.le
  refine ⟨u⁻¹ • v,?_,?_⟩
  · rw [smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul,←hu₂]
    field_simp [hu.ne']
  · change L (u⁻¹ • v)=0
    rw [map_smul,show L v=0 from hv,smul_zero]

/-- A real linear combination of the three local Pauli directions. -/
def axis {N : ℕ} (i : Fin N) (r : Fin 3→ℝ) : SpinMatrix (Fin N) :=
  ∑ a, (r a:ℂ) • spin i a

theorem axis_selfAdjoint {N : ℕ} (i : Fin N) (r : Fin 3→ℝ) :
    IsSelfAdjoint (axis i r) := by
  change star (∑ a, (r a:ℂ) • spin i a)=_
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [star_smul,Complex.star_def,Complex.conj_ofReal,(finitePauliMatrix_isHermitian _).isSelfAdjoint.star_eq]

private theorem qubit_square (r : Fin 3→ℝ) (hr : r ⬝ᵥ r=1) :
    let A := ∑ a, (r a:ℂ) • finiteQubitPauli a
    A*A=(1 : Matrix Bool Bool ℂ) := by
  intro A
  have h : (r 0:ℂ)^2+(r 1:ℂ)^2+(r 2:ℂ)^2=1 := by
    have h' : (r 0)^2+(r 1)^2+(r 2)^2=1 := by simpa [dotProduct,Fin.sum_univ_three,sq] using hr
    exact_mod_cast h'
  ext i j
  cases i <;> cases j <;>
    simp [A,Matrix.mul_apply,Fintype.sum_bool,Fin.sum_univ_three,finiteQubitPauli,
      Matrix.one_apply,show (2:Fin 3) ≠ 1 by decide,show (2:Fin 3) ≠ 0 by decide,
      show (1:Fin 3) ≠ 0 by decide] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> first | linear_combination h | ring

theorem axis_square {N : ℕ} (i : Fin N) (r : Fin 3→ℝ) (hr : r ⬝ᵥ r=1) :
    axis i r*axis i r=1 := by
  let A := ∑ a, (r a:ℂ) • finiteQubitPauli a
  have h : axis i r=finiteSingleSiteMatrix i A := by
    simp only [axis,A,Fin.sum_univ_three,finiteSingleSiteMatrix_add,finiteSingleSiteMatrix_smul,
      finiteSingleSiteMatrix_pauli,spin]
  rw [h,finiteSingleSiteMatrix_mul,show A*A=1 from qubit_square r hr,finiteSingleSiteMatrix_one]

theorem axis_unitary {N : ℕ} (i : Fin N) (r : Fin 3→ℝ) (hr : r ⬝ᵥ r=1) :
    axis i r ∈ unitary _ := by
  rw [Unitary.mem_iff,(axis_selfAdjoint i r).star_eq,axis_square i r hr]
  exact ⟨rfl,rfl⟩

theorem spin_supported {N : ℕ} (i : Fin N) (a : Fin 3) : IsSiteSupported {i} (spin i a) := by
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro j hj
  simp only [Finset.mem_singleton] at hj
  simp [siteLabel,hj]

theorem axis_supported {N : ℕ} (i : Fin N) (r : Fin 3→ℝ) : IsSiteSupported {i} (axis i r) := by
  have h (a : Fin 3) := IsSiteSupported.complex_smul (r a:ℂ) (spin_supported i a)
  rw [axis,Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
