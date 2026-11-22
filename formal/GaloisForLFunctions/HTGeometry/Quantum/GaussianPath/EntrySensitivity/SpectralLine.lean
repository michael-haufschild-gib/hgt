import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.EnergySlopes
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic
import Mathlib.Analysis.Complex.RealDeriv

/-! # Real eigenvalue branches along an arbitrary Hermitian perturbation -/
open Filter Set Matrix Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev R (I : Type*) := Matrix I I ℂ

/-- The first variable is the Hamiltonian and the second is a fixed field. -/
def fieldLine (H Z : selfAdjoint (R I)) (s : ℝ) : selfAdjoint (R I) :=
  ⟨H.val+(s:ℂ) • Z.val,by
    change star (H.val+(s:ℂ) • Z.val)=_
    rw [star_add,star_smul,H.2.star_eq,Z.2.star_eq,Complex.star_def,Complex.conj_ofReal]⟩

/-- The same continuously labeled real roots give both the physical
spectrum and all of its first derivatives at a simple Hamiltonian. -/
theorem spectral_line_branches (H Z : selfAdjoint (R I)) (hi : Function.Injective H.2.isHermitian.eigenvalues) :
    let V : R I := H.2.isHermitian.eigenvectorUnitary
    ∃ g : ℝ→I→ℝ, g 0=H.2.isHermitian.eigenvalues ∧
      (∀ j, HasDerivAt (fun s => g s j) ((star V*Z.val*V) j j).re 0) ∧
      ∀ᶠ s : ℝ in 𝓝 0, ∃ p : Equiv.Perm I,
        g s=(fieldLine H Z s).2.isHermitian.eigenvalues ∘ p := by
  classical
  intro V
  obtain ⟨f,hf⟩ := FirstGate.Boundary.energy_basis_slopes H.val Z.val H.2.isHermitian hi
  let g (s : ℝ) (j : I) := (f j (s:ℂ)).re
  have hz : g 0=H.2.isHermitian.eigenvalues := funext fun j => by simp only [g,Complex.ofReal_zero,(hf j).2.1,Complex.ofReal_re]
  have hd (j : I) : HasDerivAt (fun s => g s j) ((star V*Z.val*V) j j).re 0 := by
    have h : HasDerivAt (f j) ((star V*Z.val*V) j j) ((0:ℝ):ℂ) := by
      rw [Complex.ofReal_zero,←(hf j).2.2.2]
      exact (hf j).1.differentiableAt.hasDerivAt
    exact h.real_of_complex
  have hroot (j : I) : ∀ᶠ s : ℝ in 𝓝 0, ∃ l, g s j=(fieldLine H Z s).2.isHermitian.eigenvalues l := by
    have hcont : Tendsto ((↑) : ℝ→ℂ) (𝓝 0) (𝓝 0) := by
      simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto (0:ℝ)
    filter_upwards [hcont.eventually (hf j).2.2.1] with s hs
    obtain ⟨l,hl⟩ := exists_eigenvalue_eq_of_charpolyDet_eq_zero (fieldLine H Z s).2.isHermitian hs
    exact ⟨l,congrArg Complex.re hl⟩
  have hp (i j : I) : ∀ᶠ s : ℝ in 𝓝 0, g s i=g s j → i=j := by
    by_cases he : i=j
    · exact Eventually.of_forall fun _ _ => he
    have h0 : g 0 i≠g 0 j := by rw [hz]; exact hi.ne he
    have hh := ((hd i).continuousAt.sub (hd j).continuousAt).tendsto.eventually
      (isOpen_compl_singleton.mem_nhds (show g 0 i-g 0 j∈({0}:Set ℝ)ᶜ from sub_ne_zero.mpr h0))
    filter_upwards [hh] with s hs h
    exact (hs (sub_eq_zero.mpr h)).elim
  refine ⟨g,hz,hd,?_⟩
  filter_upwards [Filter.eventually_all.mpr hroot,Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))]
    with s hs hsep
  choose p he using hs
  have hi' : Function.Injective p := fun i j hij => hsep i j ((he i).trans ((congrArg _ hij).trans (he j).symm))
  let e := Equiv.ofBijective p ⟨hi',Finite.surjective_of_injective hi'⟩
  exact ⟨e,funext he⟩

#print axioms spectral_line_branches
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
