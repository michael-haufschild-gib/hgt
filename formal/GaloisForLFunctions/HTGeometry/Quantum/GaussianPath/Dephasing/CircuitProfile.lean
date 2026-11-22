import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.InverseTime
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw

/-! # The circuit distance profile seen by a field at the first low-gate return -/
open Matrix Real Metric Filter Topology MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
open PrecisionReturns

/-- Projective operator-norm distance to circuits within the specified gate count. -/
abbrev circuitDistance {n : ℕ} (s : ℕ) (U : Register n) := infDist U (phaseCircuitMatrixImageAtMost n s)

private theorem phase_distance {n : ℕ} (s : ℕ) (U : Register n) (z : ℂ) (hz : ‖z‖=1) :
    circuitDistance s (z • U)=circuitDistance s U := by
  have h (w : ℂ) (hw : ‖w‖=1) (V : Register n) : circuitDistance s (w • V) ≤ circuitDistance s V := by
    obtain ⟨p,hp,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist V s _).mpr (le_refl (circuitDistance s V))
    apply (hasProjectiveCircuitApproximation_iff_infDist _ s _).mp
    refine ⟨w*p,by rw [norm_mul,hw,hp,one_mul],C,hC,?_⟩
    rw [mul_smul,←smul_sub,norm_smul,hw,one_mul]
    exact he
  have hn : z≠0 := fun h => by rw [h,norm_zero] at hz; exact zero_ne_one hz
  apply le_antisymm (h z hz U)
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using h z⁻¹ (by rw [norm_inv,hz,inv_one]) (z • U)

/-- At every date the dephased orbit controls all circuit distances.
The cost of replacing the unperturbed propagator by a phase is exactly
its empty-circuit distance. -/
theorem dephased_circuit_profile {n : ℕ} (H Z : selfAdjoint (Register n)) (hi : Function.Injective H.2.isHermitian.eigenvalues) :
    let D := pinching H.2.isHermitian Z.val
    ∃ C > (0:ℝ), ∀ u T : ℝ, 0 < T → ∀ j : ℕ,
      |circuitDistance j (unitaryEvolution (H.val+(u/T) • Z.val) T)-circuitDistance j (unitaryEvolution D u)| ≤
        orbitCircuitDistance H 0 T+C*(|u|+u^2)/T := by
  intro D
  obtain ⟨hd,C,hC,hbound⟩ := dephased_evolution H Z hi
  refine ⟨C,hC,fun u T hT j => ?_⟩
  let U := unitaryEvolution H.val T
  let V := unitaryEvolution D u
  let A := unitaryEvolution (H.val+(u/T) • Z.val) T
  obtain ⟨z,hz,F,hF,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist U 0 _).mpr (le_refl (circuitDistance 0 U))
  rw [zeroGateCircuit_eval F hF] at he
  have hUV : ‖U*V-z • V‖ ≤ orbitCircuitDistance H 0 T := by
    rw [show U*V-z • V=(U-z • (1 : Register n))*V by rw [sub_mul,smul_mul_assoc,one_mul]]
    rw [CStarRing.norm_mul_mem_unitary _ (unitaryEvolution_mem_unitary hd u)]
    exact he
  have htri := norm_sub_le_norm_sub_add_norm_sub A (U*V) (z • V)
  have hl := (lipschitz_infDist_pt (phaseCircuitMatrixImageAtMost n j)).dist_le_mul A (z • V)
  change dist (circuitDistance j A) (circuitDistance j (z • V)) ≤ (1:ℝ)*dist A (z • V) at hl
  rw [phase_distance j V z hz,Real.dist_eq,one_mul,dist_eq_norm] at hl
  exact (hl.trans (htri.trans (add_le_add (hbound u T hT) hUV))).trans_eq (add_comm ..)

/-- For each Gaussian prefix, every Hermitian field and every return from
a positive origin at budget 2s<N, the inverse-time field profile converges
uniformly on bounded field intervals, simultaneously for all test budgets. -/
theorem gaussian_first_visit_dephased_profile :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ Z : selfAdjoint (Register N),
        let D := pinching H.2.isHermitian Z.val
        ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ a > (0:ℝ), ∀ s : ℕ, 2*s < N →
          ∀ ε > (0:ℝ), let v := firstVisit H a s ε
          ∀ u : ℝ, ∀ j : ℕ,
            |circuitDistance j (unitaryEvolution (H.val+(u/v) • Z.val) v)-circuitDistance j (unitaryEvolution D u)| ≤
              A*ε+C*(|u|+u^2)/v := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,UntouchedSites.gaussian_few_gate_scalar_return] with ω hi hs k
  intro N H Z D
  obtain ⟨A,hA,hscalar⟩ := hs (k+1)
  obtain ⟨C,hC,hp⟩ := dephased_circuit_profile H Z (hi k).injective
  refine ⟨A,C,hA,hC,?_⟩
  intro a ha s hsmall ε hε v u j
  have hfit := (firstVisit_isLeast H a s hε).1
  have hv := ha.trans_le hfit.1
  have he := (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp (hscalar v ε s hsmall hfit.2)
  exact (hp u v hv j).trans (add_le_add he le_rfl)

#print axioms gaussian_first_visit_dephased_profile
end
end GaloisForLFunctions.HTGeometry.Dephasing
