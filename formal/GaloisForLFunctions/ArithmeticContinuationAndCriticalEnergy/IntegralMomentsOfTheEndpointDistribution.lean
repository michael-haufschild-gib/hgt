import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CumulativeEndpointQuadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral moments of the endpoint distribution

Place the length of each cell at its right endpoint. On each open cell
the distribution function is constant and its lag behind length grows
with slope one. Integrating gives every positive moment exactly, even
when some successive endpoints coincide.
-/

noncomputable section
open Filter MeasureTheory Finset
open scoped Interval
namespace GaloisForLFunctions.CumulativeQuadrature

/-- Length from the initial endpoint minus mass already placed at or
below y. Its restriction to the partition is nonnegative. -/
def endpointLag (x : ℕ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  y-x 0-rightSum x (fun t => if t ≤ y then 1 else 0) n

/-- On a cell the lag equals the distance from the left endpoint. -/
theorem endpointLag_on_cell {x : ℕ → ℝ} (hx : Monotone x) {i n : ℕ} (hi : i < n)
    {y : ℝ} (hlo : x i ≤ y) (hhi : y < x (i+1)) :
    endpointLag x n y = y-x i := by
  have ht : (∑ j ∈ range i, (x (j+1)-x j)*(if x (j+1) ≤ y then (1:ℝ) else 0)) = x i-x 0 := by
    rw [←sum_range_sub x i]
    refine sum_congr rfl fun j hj => ?_
    rw [if_pos ((hx (Nat.succ_le_of_lt (mem_range.mp hj))).trans hlo),mul_one]
  have hr : (∑ j ∈ range (n-i), (x (i+j+1)-x (i+j))*
      (if x (i+j+1) ≤ y then (1:ℝ) else 0)) = 0 := by
    apply sum_eq_zero
    intro j _
    rw [if_neg (hhi.trans_le (hx (by omega))).not_ge,mul_zero]
  unfold endpointLag rightSum
  rw [show n=i+(n-i) by omega,sum_range_add,ht,hr]
  ring

/-- Exact integrated power of the discrepancy. Normalizing both
length and mass by the total length divides this integral by its
(p+1)-st power. -/
theorem integral_endpoint_lag_rpow {x : ℕ → ℝ} (hx : Monotone x) (n : ℕ)
    {p : ℝ} (hp : 0 < p) :
    (∫ y in x 0..x n, (endpointLag x n y)^p) =
      (∑ i ∈ range n, (x (i+1)-x i)^(p+1))/(p+1) := by
  have local_eq (i : ℕ) (hi : i < n) :
      (fun y => (endpointLag x n y)^p) =ᵐ[volume.restrict (Set.uIoc (x i) (x (i+1)))]
        fun y => (y-x i)^p := by
    rw [Set.uIoc_of_le (hx (Nat.le_succ i)),ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [volume.ae_ne (x (i+1))] with y hy hmem
    rw [endpointLag_on_cell hx hi hmem.1.le (lt_of_le_of_ne hmem.2 hy)]
  have integrable (i : ℕ) (hi : i < n) :
      IntervalIntegrable (fun y => (endpointLag x n y)^p) volume (x i) (x (i+1)) := by
    have hc : Continuous (fun y : ℝ => (y-x i)^p) :=
      (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr hp.le)
    exact hc.intervalIntegrable .. |>.congr_ae (local_eq i hi).symm
  rw [←intervalIntegral.sum_integral_adjacent_intervals integrable,Finset.sum_div]
  refine sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_congr_ae_restrict (local_eq i (mem_range.mp hi)),
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => u^p) (x i),sub_self,
    integral_rpow (Or.inl (by linarith only [hp] : -1<p)),
    Real.zero_rpow (by linarith only [hp] : p+1 ≠ 0),sub_zero]

#print axioms endpointLag_on_cell
#print axioms integral_endpoint_lag_rpow
end GaloisForLFunctions.CumulativeQuadrature
