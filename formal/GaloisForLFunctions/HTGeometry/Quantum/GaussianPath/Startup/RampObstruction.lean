import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MinimumGateCount

/-! # No constant-factor linear ramp across the inverse-size startup interval -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Even a speed chosen after seeing the prefix cannot fit both endpoint
costs, even when the tolerance may vary in [1/20,1/4] with time. -/
theorem gaussian_path_startup_no_common_slope :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ M : ℝ, 0 < M → ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ¬ ∃ v : ℝ, ∀ t ∈ Icc (A/(N:ℝ)) (1/Real.sqrt N), ∃ ε ∈ Icc (1/20:ℝ) (1/4),
        ∃ s : ℕ, IsLeast {r | HasProjectiveCircuitApproximation N ε r (unitaryEvolution H t)} s ∧
          v*t ≤ s ∧ (s:ℝ) ≤ M*(v*t) := by
  obtain ⟨A,c,J,hA,hc,hw⟩ := gaussian_path_startup_minimum_gate_count
  refine ⟨A,hA,?_⟩
  filter_upwards [hw] with ω hω
  intro M hM
  let B := max A (M*(J:ℝ)*A/c)
  have hB : 0 < B := hA.trans_le (le_max_left _ _)
  obtain ⟨m,hm⟩ := exists_nat_gt (B^2)
  filter_upwards [hω,eventually_ge_atTop m] with n hn hlarge
  let N := n+2
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  let d := Real.sqrt N
  have hd : 0 < d := Real.sqrt_pos.mpr hN
  have hsq : d*d = (N:ℝ) := by rw [← pow_two]; exact Real.sq_sqrt hN.le
  have hBd : B < d := by
    have hmn : (m:ℝ) ≤ N := by exact_mod_cast (show m ≤ N by dsimp [N]; omega)
    by_contra! h
    have hb := mul_self_le_mul_self hd.le h
    nlinarith only [hsq,hb,hm,hmn]
  have hab : A/(N:ℝ) ≤ 1/d := by
    apply (div_le_div_iff₀ hN hd).mpr
    rw [one_mul,← hsq]
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hBd.le) hd.le
  have ha : A/(N:ℝ) ∈ Icc (A/(N:ℝ)) (1/d) := ⟨le_rfl,hab⟩
  have hb : 1/d ∈ Icc (A/(N:ℝ)) (1/d) := ⟨hab,le_rfl⟩
  intro _ _ hfit
  obtain ⟨v,hv⟩ := hfit
  obtain ⟨e,he,s',hs',_,hsfit⟩ := hv _ ha
  obtain ⟨f,hf,r',hr',hrfit,_⟩ := hv _ hb
  obtain ⟨s,hs,hlo,_⟩ := hn _ ha e he
  obtain ⟨r,hr,_,hhi⟩ := hn _ hb f hf
  obtain rfl : s = s' := hs.unique hs'
  obtain rfl : r = r' := hr.unique hr'
  have hR : (r:ℝ) ≤ (J:ℝ)*N := by exact_mod_cast hhi
  have hspeed : v ≤ (J:ℝ)*N*d := (div_le_iff₀ hd).mp (by
    simpa only [mul_one_div] using hrfit.trans hR)
  have hcontra : c*(N:ℝ) ≤ M*(J:ℝ)*A*d := calc
    _ ≤ (s:ℝ) := hlo
    _ ≤ M*(v*(A/(N:ℝ))) := hsfit
    _ ≤ M*((J*N*d)*(A/(N:ℝ))) := by gcongr
    _ = _ := by field_simp
  have hl : M*(J:ℝ)*A < c*d := by
    have h := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hBd)
    simpa only [mul_comm d c] using h
  have hh := mul_lt_mul_of_pos_right hl hd
  rw [mul_assoc c,hsq] at hh
  exact (not_lt_of_ge hcontra) hh

#print axioms gaussian_path_startup_no_common_slope
end
end GaloisForLFunctions.HTGeometry

