import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.SubcriticalWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # A prescribed spectral antipode in a robust near-Hilbert plateau -/

open MeasureTheory Set Filter Topology Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open AntipodalHorizons SharpOccupation
noncomputable section

/-- At P = floor(D/(64(K+1))) the entropy costs half a bit per level.
Below the semicircle threshold, the net size times the spectator arc
probability is eventually less than (3/4)^D per mesh observation. -/
private theorem near_hilbert_net_scale {η y : ℝ} (hη : 0<η) (hy : y∈Ioo (0:ℝ) (1/2)) :
    ∀ᶠ k : ℕ in atTop, let N := k+3
      let s := nearHilbertContinuousCircuitBudget N
      let d : ℕ := 2^N-3
      ((s:ℝ)+1)*((((N:ℝ)+1)^2)*(1+4*(s:ℝ)/η)^32)^s*
        (((d:ℝ)+2)*y^d)<(3/4:ℝ)^(2^N:ℕ) := by
  obtain ⟨z,hyz,hz⟩ := exists_between hy.2
  have hz₀ := hy.1.trans hyz
  have hroot : sqrt 2<3/2 := by
    nlinarith only [sq_sqrt zero_le_two,sqrt_nonneg 2]
  have hprod : z*sqrt 2<3/4 := (mul_lt_mul_of_pos_right hz (sqrt_pos.mpr zero_lt_two)).trans
    (by linarith only [hroot])
  have hlog : log z+32*log 2/(64:ℝ)<log (3/4) := calc
    _ = log (z*sqrt 2) := by rw [log_mul hz₀.ne' (sqrt_pos.mpr zero_lt_two).ne',log_sqrt zero_le_two]; ring
    _ < _ := Real.log_lt_log (mul_pos hz₀ (sqrt_pos.mpr zero_lt_two)) hprod
  have hcost := (tendsto_add_atTop_nat 3).eventually
    (positive_budget_exponent 64 (by decide) η z (3/4) hη hz₀ (by norm_num) hlog)
  let d (k : ℕ) := 2^(k+3)-3
  have hD (k : ℕ) : d k+3=2^(k+3) := by dsimp only [d]; have := Nat.lt_two_pow_self (n:=k+3); omega
  have ht : Tendsto d atTop atTop := tendsto_atTop_mono (fun k => by
    change k≤2^(k+3)-3
    have := Nat.lt_two_pow_self (n:=k+3)
    omega) tendsto_id
  filter_upwards [ht.eventually (two_missing_powers hy.1 hyz),hcost] with k hp hk
  intro N s m
  have hpow : y^m≤z^(2^N-1:ℕ) := by
    change y^(d k)≤z^(2^(k+3)-1:ℕ)
    simpa only [←hD k,show d k+3-1=d k+2 by omega] using hp
  have hnum : (m:ℝ)+2 ≤ (2^N:ℕ) := by
    exact_mod_cast (show m+2≤2^N from (Nat.le_succ _).trans_eq (hD k))
  have hmass : ((m:ℝ)+2)*y^m ≤ zeroGateArcDensity (2^N) z :=
    mul_le_mul hnum hpow (pow_nonneg hy.1.le _) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤((s:ℝ)+1)*((((N:ℝ)+1)^2)*(1+4*(s:ℝ)/η)^32)^s)).trans_lt hk

/-- Even the full near-Hilbert budget misses an entire doubly exponential
interval from a sufficiently late prescribed winding, with exponentially
small failure probability in the register dimension. -/
theorem gaussian_near_hilbert_antipodal_window {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2)) :
    ∃ c∈Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop, ∀ q : ℝ, ∀ᶠ n : ℕ in atTop,
      let D : ℕ := 2^(k+3)
      pathPauliDisorderLaw.real (gateWindow k n (nearHilbertContinuousCircuitBudget (k+3)) q
        ((1/(7/8:ℝ))^D) ε)<c^(D-3) := by
  obtain ⟨η,hη,δ,hδ,he,hy⟩ := circuit_mesh_margins hε (physicalArc_spec hε.1 hε.2).1.2
  have hy' : physicalArc (ε+η)+δ<1/2 := hy.trans_le (min_le_right ..)
  have hy₀ := add_pos (physicalArc_spec (add_pos hε.1 hη) he).1.1 hδ
  exact gate_window_of_net_rate hε.1 hη he hδ hy'.le (by norm_num : (0:ℝ)<3/4)
    (by norm_num : (3/4:ℝ)<7/8) (by norm_num) (near_hilbert_net_scale hη ⟨hy₀,hy'⟩)

#print axioms gaussian_near_hilbert_antipodal_window
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
