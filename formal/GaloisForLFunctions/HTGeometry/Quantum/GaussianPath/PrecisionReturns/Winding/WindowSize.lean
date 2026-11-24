import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ChangeOfRadius
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity

/-! # Admissible moduli below a first-passage precision clock -/

open Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
open SharpOccupation
noncomputable section

/-- An integer mesh whose Dirichlet error is less than half the physical arc. -/
def meshOrder (ε : ℝ) : ℕ := ⌈4*π/ε⌉₊

theorem meshOrder_bounds {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) :
    0 < meshOrder ε ∧ 4/(meshOrder ε:ℝ) ≤ physicalArc ε ∧
      (meshOrder ε:ℝ) ≤ (4*π+1)*(1/ε) := by
  have hp : 0 < 4*π/ε := div_pos (mul_pos (by norm_num) pi_pos) hε.1
  have hlo : 4*π/ε ≤ (meshOrder ε:ℝ) := Nat.le_ceil _
  have hQ := hp.trans_le hlo
  have he := ShortTimeProducts.physical_arc_bounds hε.1
    (hε.2.trans_le (one_le_sqrt.mpr (by norm_num)))
  refine ⟨Nat.cast_pos.mp hQ,((div_le_div_iff₀ hQ pi_pos).mpr ?_).trans he.1,?_⟩
  · simpa only [mul_comm ε] using (div_le_iff₀ hε.1).mp hlo
  have hh : (meshOrder ε:ℝ) < 4*π/ε+1 := Nat.ceil_lt_add_one hp.le
  have hi := (one_lt_div hε.1).mpr hε.2
  apply hh.le.trans
  calc 4*π/ε+1 ≤ 4*π/ε+1/ε := add_le_add le_rfl hi.le
       _ = (4*π+1)*(1/ε) := by ring

/-- A precision exponent larger than m eventually allows *every* fixed
multiple of the m-dimensional mesh search before the first date. -/
theorem modulus_window {v : ℝ → ℝ} {m : ℕ} {d c : ℝ} (hc : 0 < c)
    (hpos : ∀ ε > 0, 0 < v ε) (hd : (m:ℝ) < d)
    (h : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), c*(meshOrder ε:ℝ)^m < v ε := by
  let B := 4*π+1
  let C := c*B^m
  have hB : 0 < B := by dsimp [B]; positivity
  have hC := mul_pos hc (pow_pos hB m)
  have hcl := (tendsto_const_div_log_one_div (log C)).add_const (m:ℝ)
  rw [zero_add] at hcl
  have hgap := Filter.Tendsto.eventually_lt hcl h hd
  filter_upwards [hgap,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε hsmall
  have hi := (one_lt_div hsmall.1).mpr hsmall.2
  have hl := log_pos hi
  have hm : log (C*(1/ε)^m) < log (v ε) := by
    rw [log_mul hC.ne' (pow_pos (zero_lt_one.trans hi) m).ne',log_pow]
    apply (div_lt_div_iff_of_pos_right hl).mp
    rw [add_div,mul_div_cancel_right₀ _ hl.ne']
    exact hε
  have hfinal := (log_lt_log_iff (mul_pos hC (pow_pos (zero_lt_one.trans hi) _)) (hpos ε hsmall.1)).mp hm
  have hq := pow_le_pow_left₀ (Nat.cast_nonneg _) (meshOrder_bounds hsmall).2.2 m
  apply (mul_le_mul_of_nonneg_left hq hc.le).trans_lt
  simpa only [mul_pow,C,B,mul_assoc] using hfinal

#print axioms meshOrder_bounds
#print axioms modulus_window
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
