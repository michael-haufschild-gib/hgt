import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.Semicircle
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # The first empty-circuit ascent on one Gaussian chain -/
open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- The first empty-circuit exit is set by the energy diameter, which lies
between deterministic positive multiples of the number of spins. The same
draw gives the entire first semicircle simultaneously at every tolerance. -/
theorem gaussian_initial_clock :
    ∃ a b : ℝ, 0<a ∧ 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let p := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      let W := circuitHamiltonianSpectralWidth H
      a*N ≤ W ∧ W ≤ b*N ∧ ∀ t ∈ Icc (0:ℝ) (π/W), ∀ ε ∈ Icc (0:ℝ) 2,
        HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val t) ↔
          t ≤ 4*arcsin (ε/2)/W := by
  obtain ⟨a,_,ha,_,hl⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨b,hb,hu⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  refine ⟨2*a,2*b,by positivity,by positivity,?_⟩
  filter_upwards [hl,hu] with ω hωl hωu
  filter_upwards [hωl,hωu] with n hn hu
  intro N p H W
  let E := H.2.isHermitian.eigenvalues
  obtain ⟨i,j,hij,_⟩ := exists_path_spectral_width_ge_onsite p
  have h₁ : E i-E j ≤ W := sub_le_sub (Finset.le_sup' E (Finset.mem_univ i))
    (Finset.inf'_le E (Finset.mem_univ j))
  have hlow : 2*a*N ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hn.1 (by norm_num : (0:ℝ)≤2)
    change 2*(∑ s : Fin N, |p (.inl (s,2))|) ≤ E i-E j at hij
    exact (mul_assoc 2 a (N:ℝ)).le.trans ((hh.trans hij).trans h₁)
  have hW : 0<W := (show 0<2*a*(N:ℝ) by dsimp [N]; positivity).trans_le hlow
  refine ⟨hlow,?_,?_⟩
  · obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty E
    obtain ⟨l,_,hl⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
    have hmax := (abs_le.mp (abs_eigenvalue_le_l2_opNorm H.2.isHermitian k)).2
    have hmin := (abs_le.mp (abs_eigenvalue_le_l2_opNorm H.2.isHermitian l)).1
    change Finset.univ.sup' Finset.univ_nonempty E-Finset.univ.inf' Finset.univ_nonempty E ≤ _
    rw [hk,hl]
    change ‖H.val‖ ≤ b*N at hu
    change E k ≤ ‖H.val‖ at hmax
    change -‖H.val‖ ≤ E l at hmin
    linarith only [hu,hmax,hmin]
  · intro t ht ε hε
    have hs : t*W≤π := (le_div_iff₀ hW).mp ht.2
    exact (zeroGateApproximation_iff_enclosingArc H t ⟨ε,hε⟩).trans
      (by rw [initial_arc H ht.1 hs]; exact (le_div_iff₀ hW).symm)

#print axioms gaussian_initial_clock
end
end GaloisForLFunctions.HTGeometry.FirstAscent
