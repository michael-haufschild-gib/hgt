import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathCircuit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PersistentCircuitFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Minimum gate count on the inverse square-root time scale -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Almost every chain has the same extensive order of minimum gate count
from A/N through 1/√N. Both constants and the number of Lie sweeps are
independent of the disorder, the chain length, and the tolerance in [1/20,1/4]. -/
theorem gaussian_path_startup_minimum_gate_count :
    ∃ A c : ℝ, ∃ J : ℕ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ t ∈ Icc (A/(N:ℝ)) (1/Real.sqrt N), ∀ ε ∈ Icc (1/20:ℝ) (1/4), ∃ s : ℕ,
        IsLeast {r | HasProjectiveCircuitApproximation N ε r (unitaryEvolution H t)} s ∧
          c*(N:ℝ) ≤ s ∧ s ≤ J*N := by
  classical
  obtain ⟨A,c,hA,hc,hfloor⟩ := gaussian_pauli_persistent_circuit_floor 1 zero_lt_one
  obtain ⟨_,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨r,hr⟩ := exists_nat_gt (1680*b)
  have hr' : 0 < (r:ℝ) := (by positivity : 0 < 1680*b).trans hr
  have hrnat : 0 < r := by exact_mod_cast hr'
  refine ⟨A,c,r*12,hA,hc,?_⟩
  filter_upwards [hfloor,hmass] with ω hw hm
  filter_upwards [hw,hm] with n hlow hmass'
  let N := n+2
  let u := pathPauliDisorderShell ω n
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hNpos : 0 < (N:ℝ) := zero_lt_one.trans_le hN
  have hroot := Real.sqrt_pos.mpr hNpos
  have hroot1 : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have hsq := Real.sq_sqrt hNpos.le
  intro _ _ t ht ε hε
  have ht0 := (div_pos hA hNpos).le.trans ht.1
  have htu : t*Real.sqrt N ≤ 1 := (le_div_iff₀ hroot).mp ht.2
  have htsq : t^2*(N:ℝ) ≤ 1 := by
    rw [← hsq,← mul_pow]
    simpa using pow_le_pow_left₀ (mul_nonneg ht0 hroot.le) htu 2
  have ht1 : t ≤ 1 := ht.2.trans ((div_le_iff₀ hroot).mpr (by simpa using hroot1))
  have hmassu : ‖u‖^2 ≤ b*(N:ℝ) := hmass'.2
  obtain ⟨z,hz,C,hC,herr⟩ := exists_path_circuit_squared_mass_error u t ht0 r hrnat
  have he : t^2/(r:ℝ)*(84*‖u‖^2) ≤ 1/20 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hr').mpr
    calc
      _ ≤ t^2*(84*(b*(N:ℝ))) := by gcongr
      _ = (84*b)*(t^2*(N:ℝ)) := by ring
      _ ≤ 84*b*1 := mul_le_mul_of_nonneg_left htsq (by positivity)
      _ ≤ _ := by linarith only [hr]
  let affordable (k : ℕ) := HasProjectiveCircuitApproximation N ε k
    (unitaryEvolution (pathHamiltonian u) t)
  have hfit : affordable C.gateCount := ⟨z,hz,C,le_rfl,herr.trans (he.trans hε.1)⟩
  have hex : ∃ k, affordable k := ⟨_,hfit⟩
  let s := Nat.find hex
  have hmin : affordable s := Nat.find_spec hex
  obtain ⟨z',_,D,hD,he'⟩ := hmin
  have hminlow := (hlow t ht.1 ht1).1 D z' (he'.trans hε.2)
  have hcard : Fintype.card (PathLabel n) ≤ 12*N := by
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp [N]; omega
  refine ⟨s,⟨Nat.find_spec hex,fun _ hk => Nat.find_min' hex hk⟩,
    hminlow.trans (by exact_mod_cast hD),?_⟩
  calc
    s ≤ C.gateCount := Nat.find_min' hex hfit
    _ = r*Fintype.card (PathLabel n) := hC
    _ ≤ r*(12*N) := Nat.mul_le_mul_left _ hcard
    _ = _ := by rw [Nat.mul_assoc]

#print axioms gaussian_path_startup_minimum_gate_count
end
end GaloisForLFunctions.HTGeometry

