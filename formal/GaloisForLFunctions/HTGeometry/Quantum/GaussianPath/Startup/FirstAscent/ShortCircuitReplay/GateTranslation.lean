import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.PhysicalComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Density
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Comparing gate distance after a short-circuit visit with the scalar orbit -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open ThermodynamicEdges
noncomputable section

private theorem best {N : ℕ} (H : selfAdjoint (Register N)) (k : ℕ) (v : ℝ) :
    HasProjectiveCircuitApproximation N (orbitCircuitDistance H k v) k (unitaryEvolution H.val v) :=
  (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr le_rfl

/-- Translating by a k-gate visit costs its approximation error in both
directions. The reverse comparison spends the inverse returning circuit. -/
theorem translate_distance {N k s : ℕ} (H : selfAdjoint (Register N)) (v t : ℝ) (hks : k ≤ s) :
    orbitCircuitDistance H s (v+t) ≤ orbitCircuitDistance H k v+orbitCircuitDistance H 0 t ∧
    orbitCircuitDistance H (k+s) t ≤ orbitCircuitDistance H k v+orbitCircuitDistance H s (v+t) := by
  have hv := best H k v
  constructor
  · obtain ⟨z,hz,C,hC,he⟩ := affordable_add_time H hv (best H 0 t)
    exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
      ⟨z,hz,C,(Nat.add_zero k ▸ hC).trans hks,he⟩
  · have h := affordable_add_time H (hv.neg_time H) (best H s (v+t))
    rw [neg_add_cancel_left] at h
    exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp h

private theorem subset_sq {n : ℕ} (u : PathShell n) (L : Finset (PathLabel n)) :
    (∑ l ∈ L, |u l|)^2 ≤ (L.card:ℝ)*‖u‖^2 := by
  apply (sq_sum_le_card_mul_sum_sq (s:=L) (f:=fun l => |u l|)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [EuclideanSpace.norm_sq_eq]
  apply (sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun _ _ _ => sq_nonneg _)).trans_eq
  simp only [Real.norm_eq_abs]

/-- At scaled lag x, a short circuit's advantage over the scalar error
is controlled by the square root of its gate density. -/
theorem scaled_advantage {n : ℕ} (u : PathShell n) (s : ℕ) (x : ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hu : ‖u‖^2 ≤ b*((n+2 : ℕ):ℝ)) :
    let N : ℝ := (n+2 : ℕ)
    let H := shellOperator u
    orbitCircuitDistance H 0 (x/N) ≤ orbitCircuitDistance H s (x/N)+
      2*|x|*sqrt ((42*b)*((s:ℝ)/N)) := by
  intro N H
  have hN : 0<N := by dsimp only [N]; positivity
  obtain ⟨L,hL,he⟩ := circuit_advantage u s (x/N)
  let M := ∑ l ∈ L, |u l|
  have hM : 0 ≤ M := sum_nonneg fun _ _ => abs_nonneg _
  have hsq : M^2 ≤ (42*(s:ℝ))*(b*N) := (subset_sq u L).trans
    (mul_le_mul (by exact_mod_cast hL) hu (sq_nonneg _) (by positivity))
  have hh : M/N ≤ sqrt ((42*b)*((s:ℝ)/N)) := by
    apply (sq_le_sq₀ (div_nonneg hM hN.le) (sqrt_nonneg _)).mp
    rw [sq_sqrt (mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg _) hN.le)),div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    exact hsq.trans_eq (by field_simp)
  change orbitCircuitDistance H 0 (x/N) ≤ orbitCircuitDistance H s (x/N)+2*|x/N|*M at he
  apply he.trans
  apply add_le_add_left
  rw [abs_div,abs_of_pos hN,show 2*(|x|/N)*M=(2*|x|)*(M/N) by ring]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

#print axioms translate_distance
#print axioms scaled_advantage
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
