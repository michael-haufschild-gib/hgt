import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedPathCircuit
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # Nearly linear gate cost at every physical time scale -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Up to integrated interaction mass 2^d/100, the gate count exceeds the
dyadic scale times the number of interactions by a factor at most
2^(8 floor(sqrt d)+8). The same bound covers the entire time interval. -/
theorem path_dyadic_nearly_linear_simulation {n : ℕ} (u : PathShell n) (d : ℕ) (t : ℝ)
    (ht : 100*(1+∑ l : PathLabel n, |u l|)*|t| ≤ (2:ℝ)^d) :
    HasProjectiveCircuitApproximation (n+2) (1/100:ℝ)
      (2^(d+8*d.sqrt+8)*Fintype.card (PathLabel n)) (unitaryEvolution (pathHamiltonian u) t) := by
  let s := d.sqrt
  let q : ℕ := 2^(s+4)
  let m := Fintype.card (PathLabel n)
  let M := 1+∑ l : PathLabel n, |u l|
  have h7 : (7:ℝ)^s ≤ 2^(3*s) := by rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h3 : (3:ℕ)^s ≤ 2^(2*s) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) _
  have hhi : d < (s+1)*(s+1) := Nat.lt_succ_sqrt d
  have hlo : s^2 ≤ d := Nat.sqrt_le' d
  have htime : 7^s*M*|t| ≤ (q:ℝ)^(s+1)/100 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    calc
      _ = 7^s*(100*M*|t|) := by ring
      _ ≤ 2^(3*s)*(2:ℝ)^d := (mul_le_mul_of_nonneg_left ht (by positivity)).trans
        (mul_le_mul_of_nonneg_right h7 (by positivity))
      _ ≤ (2:ℝ)^((s+4)*(s+1)) := by
        rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by nlinarith only [hhi])
      _ = _ := by dsimp [q]; push_cast; rw [pow_mul]
  obtain ⟨z,hz,C,hC,he⟩ := exists_high_order_path_circuit u s q t (by dsimp [q]; positivity) htime
  refine ⟨z,hz,C,?_,he⟩
  rw [hC]
  change q^(s+2)*(3^s*m) ≤ 2^(d+8*s+8)*m
  calc
    _ ≤ q^(s+2)*(2^(2*s)*m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
    _ = 2^((s+4)*(s+2)+2*s)*m := by dsimp only [q]; rw [← mul_assoc,← pow_mul,← pow_add]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith only [hlo]))

#print axioms path_dyadic_nearly_linear_simulation
end
end GaloisForLFunctions.HTGeometry
