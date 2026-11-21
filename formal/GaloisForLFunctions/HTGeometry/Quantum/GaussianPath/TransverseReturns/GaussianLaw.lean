import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.FirstWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PrecisionBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw

/-! # Improved precision exponent for the first quadratic-budget return -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section
open PrecisionReturns

/-- On every Gaussian prefix, a quadratic budget bounds the first
affordable time by a constant times ε^(-(2D−5)/2), uniformly for all
small physical errors. The origin may be chosen from the whole chain. -/
theorem gaussian_quadratic_first_visit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let S := (Fintype.card (PathLabel (k+1))+1)^2*9
      let D : ℕ := 2^N
      ∃ B > (0:ℝ), ∀ A > (0:ℝ), ∃ K > (0:ℝ), ∀ ε ∈ Ioc 0 B,
        (firstVisit H A S ε)^2*ε^(2*D-5) ≤ K := by
  filter_upwards [gaussian_gap_clock,gaussian_path_all_prefixes_maximally_projective] with ω hclock hgeneric k
  intro N H S D
  obtain ⟨e,hgap,_⟩ := hclock k
  let z : Fin (2^N-3+3) := ⟨2,by omega⟩
  have hz0 : z ≠ 0 := by intro he; have h := congrArg Fin.val he; change 2=0 at h; omega
  have hz1 : z ≠ 1 := by
    intro he
    have h := congrArg Fin.val he
    simp only [z,Fin.val_one] at h
    omega
  have hi := (hgeneric k).injective
  obtain ⟨B,hB,h⟩ := path_quadratic_deadline (pathPauliDisorderShell ω (k+1)) (e.symm 0) (e.symm 1) (e.symm z)
    (sub_pos.mp hgap) (hi.ne (e.symm.injective.ne hz0)) (hi.ne (e.symm.injective.ne hz1))
  refine ⟨B,hB,?_⟩
  intro A hA
  obtain ⟨τ,hτ,hh⟩ := h A
  exact ⟨τ^2*(4*B)^(2*D-5),by positivity,uniform_first_deadline H hA hB hτ hh⟩

/-- At the same first robust crossing, low budgets have precision exponent
D−2 while the quadratic budget has an elapsed-wait upper exponent D−5/2. -/
theorem gaussian_quadratic_first_crossing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let D : ℕ := 2^N
      let S := (Fintype.card (PathLabel (k+1))+1)^2*9
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        (∃ B > (0:ℝ), ∃ K > (0:ℝ), ∀ ε ∈ Ioc 0 B,
          (firstVisit H σ S ε-σ)^2*ε^(2*D-5) ≤ K) ∧
        ∀ s : ℕ, 2*s<N →
          Tendsto (fun ε => log (firstVisit H σ s ε-σ)/log (1/ε))
            (𝓝[>] (0:ℝ)) (𝓝 ((D-2:ℕ):ℝ)) := by
  filter_upwards [gaussian_quadratic_first_visit,gaussian_first_crossing_precision_wait] with ω hquad hcross
  filter_upwards [hcross] with k hk
  intro N H D S P
  obtain ⟨σ,hσ,he,hearly,hsmall⟩ := hk
  obtain ⟨B,hB,h⟩ := hquad k
  obtain ⟨K,hK,hb⟩ := h σ hσ
  refine ⟨σ,hσ,he,hearly,⟨B,hB,K,hK,?_⟩,hsmall⟩
  intro ε hε
  have hv := (firstVisit_isLeast H σ S hε.1).1.1
  exact (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (sub_nonneg.mpr hv) (hσ.le.trans hv)).mpr
    (sub_le_self _ hσ.le)) (pow_nonneg hε.1.le _)).trans (hb ε hε)

#print axioms gaussian_quadratic_first_visit
#print axioms gaussian_quadratic_first_crossing
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
