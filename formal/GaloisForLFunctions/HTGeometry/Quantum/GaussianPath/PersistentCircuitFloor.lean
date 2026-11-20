import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldDensity
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.IsolatedSiteFloor

/-! # Persistent circuit hardness throughout a fixed physical time horizon -/
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- For any fixed T>0, almost every chain eventually has an extensive gate
floor at every lag in [A/N,T]. At each such lag, circuits at any two time
origins separated by that lag must pay the same extensive total cost. -/
theorem gaussian_pauli_persistent_circuit_floor (T : ℝ) (hT : 0 < T) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ t : ℝ, A/(N:ℝ) ≤ t → t ≤ T →
        (∀ (C : TwoQubitCircuit N) (z : ℂ), ‖unitaryEvolution H t-z • (C.eval : Reg N)‖ ≤ 1/4 →
          c*(N:ℝ) ≤ C.gateCount) ∧
        ∀ v : ℝ, ∀ s r : ℕ, HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation N (1/10:ℝ) r (unitaryEvolution H (v+t)) →
          c*(N:ℝ) ≤ (s:ℝ)+r := by
  let q := 1/(8*T)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨p,hp,hblocks⟩ := gaussian_path_eventual_isolated_sites q (q/200) (by positivity)
  let A := 4*Real.pi/(q*p)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,p/8,hA,by positivity,?_⟩
  filter_upwards [hblocks] with ω hω
  obtain ⟨k,hk⟩ := exists_nat_gt (8/p)
  filter_upwards [hω,eventually_ge_atTop k] with n hS hlarge
  obtain ⟨S,hS,his⟩ := hS
  let N := n+2
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hsize : 8 ≤ p*(N:ℝ) := by
    have h' : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show k ≤ N by dsimp [N]; omega)
    have h8 : 8 < (k:ℝ)*p := (div_lt_iff₀ hp).mp hk
    linarith only [h8,mul_le_mul_of_nonneg_right h' hp.le]
  intro _ _ t hlo hhi
  have ht : 0 < t := (div_pos hA hN).trans_le hlo
  have hstart : A ≤ (N:ℝ)*t := by simpa only [mul_comm t] using (div_le_iff₀ hN).mp hlo
  have hend : q*t ≤ 1/8 := by
    apply (mul_le_mul_of_nonneg_left hhi hq.le).trans_eq
    dsimp [q]; field_simp [hT.ne']
  have hf := isolated_sites_uniform_circuit_floor u q p hq hp S hS his hsize t ht hstart hend
  refine ⟨hf,?_⟩
  intro v s r hv he
  by_contra! hsmall
  have hh : ProjectiveCircuitSeparated N (1/4:ℝ) (r+s) (unitaryEvolution H.val t) := by
    intro z _ C hC
    by_contra! happrox
    have hc : (C.gateCount:ℝ) ≤ (r:ℝ)+s := by exact_mod_cast hC
    linarith only [hf C z happrox,hc,hsmall]
  have hx := projectiveCircuitSeparated_unitaryEvolution_backward_cone H
    (by omega : s ≤ r+s) hh (hv.neg_time H) (by norm_num : (1/10:ℝ)+1/10 ≤ 1/4)
  rw [show t-(-v) = v+t by ring,Nat.add_sub_cancel] at hx
  obtain ⟨z,hz,C,hC,heC⟩ := he
  exact (not_lt_of_ge heC) (hx z hz C hC)

/-- For every sublinear gate budget, two affordable times more than A/N
apart must eventually be farther apart than any fixed macroscopic duration.
One deterministic A works for every duration and every budget sequence. -/
theorem gaussian_pauli_sublinear_dip_spacing :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ,
      Tendsto (fun n => (s n:ℝ)/((n+2:ℕ):ℝ)) atTop (nhds 0) →
      ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H := pathHamiltonian (pathPauliDisorderShell ω n)
        ∀ t : ℝ, A/(N:ℝ) ≤ t → ∀ v : ℝ,
          HasProjectiveCircuitApproximation N (1/10:ℝ) (s n) (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation N (1/10:ℝ) (s n) (unitaryEvolution H (v+t)) → T < t := by
  have hall (k : ℕ) := gaussian_pauli_persistent_circuit_floor ((k:ℝ)+1) (by positivity)
  choose A c hA hc hw using hall
  refine ⟨A 0,hA 0,?_⟩
  filter_upwards [ae_all_iff.mpr hw] with ω hω
  intro s hsub T
  obtain ⟨k,hk⟩ := exists_nat_gt T
  obtain ⟨m,hm⟩ := exists_nat_gt (A k)
  have hsmall i := hsub.eventually_lt_const (div_pos (hc i) (by norm_num : (0:ℝ) < 2))
  filter_upwards [hω 0,hω k,hsmall 0,hsmall k,eventually_ge_atTop m]
    with n hzero hwide hsmall0 hsmallk hlarge
  let N := n+2
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hcost (i : ℕ) (hs : (s n:ℝ)/(N:ℝ) < c i/2) :
      (s n:ℝ)+(s n:ℝ) < c i*(N:ℝ) := by
    linarith only [(div_lt_iff₀ hN).mp hs]
  have hone : A k/(N:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    rw [one_mul]
    exact hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  intro _ _ t ht v hv he
  by_contra! hT
  by_cases htone : t ≤ 1
  · have h := (hzero t ht (by simpa using htone)).2 v (s n) (s n) hv he
    exact (not_lt_of_ge h) (hcost 0 hsmall0)
  · have h := (hwide t (hone.trans (le_of_not_ge htone))
      (by linarith only [hT,hk])).2 v (s n) (s n) hv he
    exact (not_lt_of_ge h) (hcost k hsmallk)

/-- For every time sequence tending to zero after the inverse-size startup,
the minimum gate count exceeds every fixed multiple of Nt. A size-uniform
linear upper ramp must therefore start on a macroscopic time scale. -/
theorem gaussian_pauli_submacroscopic_cost_exceeds_linear_clock :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ f : ℕ → ℝ,
      Tendsto f atTop (nhds 0) → (∀ᶠ n : ℕ in atTop, A/((n+2:ℕ):ℝ) ≤ f n) →
      ∀ v : ℝ, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (f n)) →
        v*((n+2:ℕ):ℝ)*f n < s := by
  obtain ⟨A,c,hA,hc,hw⟩ := gaussian_pauli_persistent_circuit_floor 1 zero_lt_one
  refine ⟨A,hA,?_⟩
  filter_upwards [hw] with ω hω
  intro f hf hstart v
  have hv : Tendsto (fun n => v*f n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := v)).mul hf
  filter_upwards [hω,hstart,hf.eventually_lt_const zero_lt_one,hv.eventually_lt_const hc]
    with n hn ht hT he
  intro s hs
  obtain ⟨z,_,C,hC,herr⟩ := hs
  have hfloor := (hn (f n) ht hT.le).1 C z (herr.trans (by norm_num))
  calc
    _ = (v*f n)*((n+2:ℕ):ℝ) := by ring
    _ < c*((n+2:ℕ):ℝ) := mul_lt_mul_of_pos_right he (by positivity)
    _ ≤ (C.gateCount:ℝ) := hfloor
    _ ≤ _ := by exact_mod_cast hC

#print axioms gaussian_pauli_submacroscopic_cost_exceeds_linear_clock
#print axioms gaussian_pauli_persistent_circuit_floor
#print axioms gaussian_pauli_sublinear_dip_spacing
end
end GaloisForLFunctions.HTGeometry
