import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathCircuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Occupation of starts with an affordable visit within one time unit -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

def windowHits {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε W : ℝ) : Set ℝ :=
  {u | ∃ v ∈ Icc u (u+W), v ∈ visitSet H s ε}

/-- At any fixed extra error, a unit interval can be swept into the
affordable set by adding at most N^4 gates on a typical growing chain. -/
theorem gaussian_unit_hit_enlargement :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ s ε, windowHits H s ε 1 ⊆ visitSet H (s+N^4) (ε+δ) := by
  obtain ⟨_,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hmass] with ω hω
  intro δ hδ
  obtain ⟨m,hm⟩ := exists_nat_gt (84*b/δ)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,eventually_ge_atTop m,
    eventually_ge_atTop 12] with k hnorm hk h12
  intro N H s ε u hu
  obtain ⟨v,hv,he⟩ := hu
  let x := pathPauliDisorderShell ω (k+1)
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have h12' : 12 ≤ N := by dsimp [N]; omega
  have hpay : 84*b ≤ δ*(N:ℝ) := by
    have hmN : m ≤ N := by dsimp [N]; omega
    have h : 84*b/δ ≤ (N:ℝ) := hm.le.trans (Nat.cast_le.mpr hmN)
    simpa only [mul_comm δ] using (div_le_iff₀ hδ).mp h
  have hτ : 0 ≤ v-u := sub_nonneg.mpr hv.1
  have hτ' : v-u ≤ 1 := by linarith only [hv.2]
  obtain ⟨c,hc,C,hC,hd⟩ := exists_path_circuit_squared_mass_error x (v-u) hτ (N^2) (by dsimp [N]; positivity)
  have herr : (v-u)^2/((N^2:ℕ):ℝ)*(84*‖x‖^2) ≤ δ := by
    push_cast
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hN 2)).mpr
    calc
      _ ≤ 1*(84*(b*(N:ℝ))) := mul_le_mul (by simpa using pow_le_pow_left₀ hτ hτ' 2)
        (mul_le_mul_of_nonneg_left hnorm.2 (by norm_num)) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hpay hN.le]
  have hJ : Fintype.card (PathLabel (k+1)) ≤ 12*N := by
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp [N]; omega
  have hcnt : C.gateCount ≤ N^4 := calc
    _ ≤ N^2*(12*N) := hC.trans_le (Nat.mul_le_mul_left _ hJ)
    _ ≤ N^2*(N*N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h12')
    _ = _ := by ring
  have hinc : HasProjectiveCircuitApproximation N δ (N^4) (unitaryEvolution H.val (v-u)) :=
    ⟨c,hc,C,hcnt,hd.trans herr⟩
  have hneg := hinc.neg_time H
  have hprod := LocalPatches.approx_product
    (unitaryEvolution_mem_unitary H.2 (-(v-u))) he hneg
  have heq := unitaryEvolution_sub_mul H u (-(v-u))
  rw [show u-(-(v-u))=v by ring] at heq
  rwa [heq] at hprod

theorem subcritical_add_pow_four {s : ℕ → ℕ} (hs : subcriticalBudget s) :
    subcriticalBudget (fun n => s n+n^4) := by
  unfold subcriticalBudget at *
  have hp := polynomial_subcritical 4
  unfold subcriticalBudget at hp
  have hi := polynomial_subcritical 0
  unfold subcriticalBudget at hi
  have h := (hs.add hp).sub (hi.div_const 2)
  rw [zero_add,zero_div,sub_zero] at h
  apply h.congr
  intro n
  push_cast
  ring

#print axioms gaussian_unit_hit_enlargement
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
