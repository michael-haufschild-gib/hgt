import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.GeometricScales
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GaussianRate

/-! # Circuit entropy and the loss of two pinned eigenphases -/

open Real Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open SharpOccupation AntipodalHorizons
noncomputable section

/-- Enlarging the arc by any fixed amount pays for the two missing
spectator coordinates at a prescribed pair winding. -/
theorem two_missing_powers {y z : ℝ} (hy : 0<y) (hyz : y<z) :
    ∀ᶠ d : ℕ in atTop, y^d ≤ z^(d+2) := by
  have hz := hy.trans hyz
  have hC : 0 ≤ 1/z^2 := by positivity
  filter_upwards [FirstClockIndex.linear_mul_pow_eventually_lt (1/z^2) hy hyz] with d hd
  have hle : (1/z^2)*y^d ≤ z^d := (mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right hC (le_add_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) d))) (pow_nonneg hy.le _)).trans hd.le
  rw [one_div_mul_eq_div,div_le_iff₀ (pow_pos hz _)] at hle
  simpa only [pow_add] using hle

/-- The circuit metric entropy remains negligible for subcritical budgets
even when the two pinned levels are removed from the Haar short-arc test. -/
theorem spectator_net_scale {s : ℕ→ℕ} (hs : subcriticalBudget s) {η y b : ℝ}
    (hη : 0<η) (hy : 0<y) (hyb : y<b) :
    ∀ᶠ k : ℕ in atTop, let N := k+3
      let d := 2^N-3
      ((s N:ℝ)+1)*((((N:ℝ)+1)^2)*(1+4*(s N:ℝ)/η)^32)^(s N)*
        (((d:ℝ)+2)*y^d) < b^(2^N:ℕ) := by
  obtain ⟨z,hyz,hzb⟩ := exists_between hyb
  let d (k : ℕ) := 2^(k+3)-3
  have hD (k : ℕ) : d k+3=2^(k+3) := by
    have := Nat.lt_two_pow_self (n:=k+3)
    dsimp only [d]
    omega
  have htop : Tendsto d atTop atTop := tendsto_atTop_mono (fun k => by
    have := Nat.lt_two_pow_self (n:=k+3)
    dsimp only [d]
    omega) tendsto_id
  have hcost := (tendsto_add_atTop_nat 3).eventually
    ((enlarged_arc_eventually_lt hs (36+128/η) z b (hy.trans hyz) hzb).and (budget_le_dimension_eventually hs))
  filter_upwards [htop.eventually (two_missing_powers hy hyz),hcost] with k hp hk
  intro N m
  have hpow : y^m ≤ z^(2^N-1:ℕ) := by
    change y^(d k) ≤ z^(2^(k+3)-1:ℕ)
    simpa only [←hD k,show d k+3-1=d k+2 by omega] using hp
  have hcount : (m:ℝ)+2 ≤ (2:ℝ)^N := by
    have h : m+2 ≤ 2^N := (Nat.le_succ _).trans_eq (hD k)
    exact_mod_cast h
  have hmass := mul_le_mul hcount hpow (pow_nonneg hy.le _) (by positivity : (0:ℝ)≤2^N)
  have henv := net_envelope_le_exp N (s N) η hη hk.2
  exact (mul_le_mul henv hmass (mul_nonneg (by positivity) (pow_nonneg hy.le _)) (Real.exp_pos _).le).trans_lt hk.1

#print axioms spectator_net_scale
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
