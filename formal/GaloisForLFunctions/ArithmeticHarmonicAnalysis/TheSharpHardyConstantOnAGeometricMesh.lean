import GaloisForLFunctions.ArithmeticHarmonicAnalysis.HardyEnergyOnAFiniteMesh
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The sharp quadratic Hardy constant on a geometric mesh

On a geometric mesh the weighted Hardy difference becomes xᵢ − q xᵢ₊₁.
Completing its square gives the exact deficit, including the boundary flux.
Grounded plateaus approach the optimal coefficient (1−q)².
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The shifted difference has a Dirichlet remainder and a signed endpoint term. -/
theorem geometric_hardy_deficit (q : ℝ) (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m,(x i-q*x (i+1))^2) =
      (1-q)^2*(∑ i ∈ range m,(x i)^2) + q*(∑ i ∈ range m,(x i-x (i+1))^2) +
        q*(1-q)*(x 0^2-x m^2) := by
  let b (i : ℕ) := q*(1-q)*x i^2
  calc _ = ∑ i ∈ range m,((1-q)^2*x i^2+q*(x i-x (i+1))^2+(b i-b (i+1))) :=
             sum_congr rfl fun i _ => by dsimp only [b]; ring
       _ = _ := by
             rw [sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,sum_range_sub']
             dsimp only [b]
             ring

/-- The exact remainder is nonnegative when the final value vanishes. -/
theorem geometric_hardy_grounded {q : ℝ} (hq : 0≤q) (hq1 : q≤1) {x : ℕ → ℝ}
    {m : ℕ} (edge : x m=0) :
    (1-q)^2*(∑ i ∈ range m,x i^2) ≤ ∑ i ∈ range m,(x i-q*x (i+1))^2 := by
  rw [geometric_hardy_deficit,edge,zero_pow (by norm_num : 2≠0),sub_zero]
  have internal := mul_nonneg hq (sum_nonneg (s:=range m) (fun i _ => sq_nonneg (x i-x (i+1))))
  have endpoint := mul_nonneg (mul_nonneg hq (sub_nonneg.mpr hq1)) (sq_nonneg (x 0))
  linarith only [internal,endpoint]

/-- A grounded plateau has constant interior loss and one final unit jump.
Its two endpoint samplings differ by exactly one vertex. -/
theorem grounded_geometric_plateau (q : ℝ) (n : ℕ) : ∃ x : ℕ → ℝ, x (n+1)=0 ∧
    (∑ i ∈ range (n+1),x i^2)=(n:ℝ)+1 ∧
    (∑ i ∈ range (n+1),(q*x (i+1))^2)=(n:ℝ)*q^2 ∧
    (∑ i ∈ range (n+1),(x i-q*x (i+1))^2)=(n:ℝ)*(1-q)^2+1 := by
  let x (i : ℕ) : ℝ := if i≤n then 1 else 0
  have on (i : ℕ) (hi : i≤n) : x i=1 := if_pos hi
  have off : x (n+1)=0 := if_neg (by omega)
  have weight : (∑ i ∈ range (n+1),x i^2)=(n:ℝ)+1 := by
    calc _ = ∑ _i ∈ range (n+1),(1:ℝ) := sum_congr rfl fun i hi => by
                   rw [on i (Nat.lt_succ_iff.mp (mem_range.mp hi)),one_pow]
         _ = _ := by simp
  have jumps : (∑ i ∈ range n,(x i-q*x (i+1))^2)=(n:ℝ)*(1-q)^2 := by
    calc _ = ∑ _i ∈ range n,(1-q)^2 := sum_congr rfl fun i hi => by
                   have small := mem_range.mp hi
                   rw [on i small.le,on (i+1) small,mul_one]
         _ = _ := by simp
  refine ⟨x,off,weight,?_,?_⟩
  · rw [sum_range_succ,off,mul_zero,zero_pow (by norm_num : 2≠0),add_zero]
    calc _ = ∑ _i ∈ range n,q^2 := sum_congr rfl fun i hi => by rw [on (i+1) (mem_range.mp hi),mul_one]
         _ = _ := by simp
  · rw [sum_range_succ,jumps,on n le_rfl,off,mul_zero,sub_zero,one_pow]

/-- All grounded meshes admit exactly the coefficients through (1−q)².
For a plateau of length n+1 the terminal jump costs one. -/
theorem sharp_grounded_geometric_hardy_constant {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (c : ℝ) :
    (∀ (x : ℕ → ℝ) (m : ℕ), x m=0 →
      c*(∑ i ∈ range m,x i^2) ≤ ∑ i ∈ range m,(x i-q*x (i+1))^2) ↔ c≤(1-q)^2 := by
  constructor
  · intro bound
    have plateau (n : ℕ) : c*((n:ℝ)+1)≤(n:ℝ)*(1-q)^2+1 := by
      obtain ⟨x,off,weight,_,jumps⟩ := grounded_geometric_plateau q n
      have h := bound x (n+1) off
      rw [weight,jumps] at h
      exact h
    by_contra! strict
    obtain ⟨n,large⟩ := exists_nat_gt ((1-c)/(c-(1-q)^2))
    have contradiction := (div_lt_iff₀ (sub_pos.mpr strict)).mp large
    linarith only [contradiction,plateau n]
  · intro hc x m edge
    exact (mul_le_mul_of_nonneg_right hc (sum_nonneg fun i _ => sq_nonneg (x i))).trans
      (geometric_hardy_grounded hq hq1 edge)

/-- Reversing the two coefficients in the difference leaves precisely
the loss of squared endpoint amplitude. The reversed difference vanishes
on the geometric extension xᵢ₊₁ = q xᵢ. -/
theorem geometric_hardy_boundary_deficit (q : ℝ) (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m,(x i-q*x (i+1))^2) =
      (1-q^2)*(x 0^2-x m^2) + ∑ i ∈ range m,(q*x i-x (i+1))^2 := by
  calc _ = ∑ i ∈ range m,((1-q^2)*(x i^2-x (i+1)^2)+(q*x i-x (i+1))^2) :=
             sum_congr rfl fun i _ => by ring
       _ = _ := by rw [sum_add_distrib,←mul_sum,sum_range_sub']

private theorem weighted_difference {q : ℝ} (hq : q≠0) (i : ℕ) (v w : ℝ) :
    (q⁻¹)^i*v-q*((q⁻¹)^(i+1)*w)=(q⁻¹)^i*(v-w) := by
  rw [pow_succ,show q*((q⁻¹^i*q⁻¹)*w)=(q*q⁻¹)*(q⁻¹^i*w) by ring,mul_inv_cancel₀ hq,one_mul]
  ring

/-- A vanishing sequence is controlled by the square sum of its weighted
successive losses. Subtracting its terminal value before truncating
requires only the unweighted limit to vanish. -/
theorem geometric_hardy_tail_control {q : ℝ} (hq : 0<q) (hq1 : q<1) (v : ℕ → ℝ)
    (decay : Tendsto v atTop (𝓝 0)) {C : ℝ}
    (loss : ∀ m : ℕ, (∑ i ∈ range m,((q⁻¹)^i*(v i-v (i+1)))^2)≤C) (L : ℕ) :
    (1-q)^2*(∑ i ∈ range L,((q⁻¹)^i*v i)^2)≤C := by
  let x (m i : ℕ) := (q⁻¹)^i*(v i-v m)
  have edge (m : ℕ) : x m m=0 := by simp [x]
  have step (m i : ℕ) : x m i-q*x m (i+1)=(q⁻¹)^i*(v i-v (i+1)) := by
    dsimp only [x]
    rw [weighted_difference hq.ne']
    ring
  have term (i : ℕ) : Tendsto (fun m => x m i^2) atTop (𝓝 (((q⁻¹)^i*v i)^2)) := by
    simpa only [x,sub_zero] using (((tendsto_const_nhds (x:=v i)).sub decay).const_mul ((q⁻¹)^i)).pow 2
  apply le_of_tendsto ((tendsto_finsetSum (range L) (fun i _ => term i)).const_mul ((1-q)^2))
  filter_upwards [eventually_ge_atTop L] with m large
  have part := sum_le_sum_of_subset_of_nonneg (range_mono large)
    (fun i _ _ => sq_nonneg (x m i))
  have full := geometric_hardy_grounded hq.le hq1.le (edge m)
  simp_rw [step] at full
  exact (mul_le_mul_of_nonneg_left part (sq_nonneg (1-q))).trans (full.trans (loss m))

/-- Releasing a prescribed amount from an initial state costs at least
1−q² times its square. Compensation at a remote endpoint avoids any
assumption on the weighted final value. -/
theorem geometric_hardy_endpoint_cost {q : ℝ} (hq : 0<q) (v : ℕ → ℝ)
    (decay : Tendsto v atTop (𝓝 0)) {C : ℝ}
    (loss : ∀ m : ℕ, (∑ i ∈ range m,((q⁻¹)^i*(v i-v (i+1)))^2)≤C) :
    (1-q^2)*v 0^2≤C := by
  have lim := (((tendsto_const_nhds (x:=v 0)).sub decay).pow 2).const_mul (1-q^2)
  rw [sub_zero] at lim
  apply le_of_tendsto lim
  apply Filter.Eventually.of_forall
  intro m
  let x (i : ℕ) := (q⁻¹)^i*(v i-v m)
  have step (i : ℕ) : x i-q*x (i+1)=(q⁻¹)^i*(v i-v (i+1)) := by
    dsimp only [x]
    rw [weighted_difference hq.ne']
    ring
  have bound := geometric_hardy_boundary_deficit q x m
  simp_rw [step] at bound
  rw [show x m=0 by simp [x],show x 0=v 0-v m by simp [x],zero_pow (by norm_num : 2≠0),sub_zero] at bound
  exact (le_add_of_nonneg_right (sum_nonneg fun i _ => sq_nonneg (q*x i-x (i+1)))).trans
    (bound.symm.le.trans (loss m))

#print axioms geometric_hardy_boundary_deficit
#print axioms geometric_hardy_endpoint_cost
#print axioms geometric_hardy_tail_control
#print axioms geometric_hardy_deficit
#print axioms sharp_grounded_geometric_hardy_constant
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
