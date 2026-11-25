import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.FirstIndex
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Jumps.VisitJump
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.PhaseComparison

/-! # From the first simultaneous gap approximation to the first affordable tick -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
open PrecisionReturns ResonantReturns
noncomputable section

/-- The discrete physical first-index exponent equals the simultaneous
gap exponent when a circuit fit forces a scalar fit at a fixed multiple
of the tolerance. -/
theorem index_exponent_of_gaps {n d : ℕ} (H : selfAdjoint (Register n))
    (e : (Fin n → Bool) ≃ Fin (d+1)) (τ : ℝ) (s : ℕ) {A : ℝ} (hA : 0<A)
    (hc : ∀ t ε, HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t) →
      HasProjectiveCircuitApproximation n (A*ε) 0 (unitaryEvolution H.val t)) {D : ℝ} :
    let E := H.2.isHermitian.eigenvalues
    let β := fun i : Fin d => τ*(E (e.symm i.succ)-E (e.symm 0))/(2*π)
    Tendsto (fun r => log (firstHit β r)/log (1/r)) (𝓝[>] (0:ℝ)) (𝓝 D) →
      Tendsto (fun ε => log (firstIndex H τ s ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 D) := by
  intro E β hβ
  let c := (2*π)⁻¹
  have hc0 : 0<c := by dsimp only [c]; positivity
  have hq (q : ℕ) (i : Fin d) :
      ((q:ℝ)*τ)*(E (e.symm i.succ)-E (e.symm 0))/(2*π)=(q:ℝ)*β i := by dsimp only [β]; ring
  have hbounds : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      log (firstHit β (A*ε))/log (1/ε) ≤ log (firstIndex H τ s ε)/log (1/ε) ∧
      log (firstIndex H τ s ε)/log (1/ε) ≤ log (firstHit β (c*ε))/log (1/ε) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    let q := firstHit β (c*ε)
    obtain ⟨hq1,hh⟩ := firstHit_mem β (mul_pos hc0 hε.1)
    have hp := empty_of_anchored_gaps H (e.symm 0) ((q:ℝ)*τ) (mul_nonneg hc0.le hε.1.le) (by
      intro j
      obtain ⟨i,rfl⟩ := e.symm.surjective j
      refine Fin.cases ?_ (fun i => ?_) i
      · exact ⟨0,by simpa only [sub_self,mul_zero,zero_div,Int.cast_zero,abs_zero] using mul_pos hc0 hε.1⟩
      · change latticeClose (((q:ℝ)*τ)*(E (e.symm i.succ)-E (e.symm 0))/(2*π)) _
        rw [hq]
        exact hh i)
    rw [show 2*π*(c*ε)=ε by dsimp only [c]; field_simp] at hp
    let S : Set ℕ := fun j => 1 ≤ j ∧
      HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val ((j:ℝ)*τ))
    obtain ⟨z,hz,C,hC,hfit⟩ := hp
    have hqS : q∈S := ⟨hq1,z,hz,C,hC.trans (Nat.zero_le _),hfit⟩
    let m := firstIndex H τ s ε
    have hm : m∈S := Nat.sInf_mem ⟨q,hqS⟩
    have hsmall := anchored_gaps_of_empty H (e.symm 0) (mul_pos hA hε.1) (hc _ _ hm.2)
    have hlow : firstHit β (A*ε) ≤ m := Nat.sInf_le (show 1 ≤ m ∧ ∀ i, latticeClose ((m:ℝ)*β i) (A*ε) from
      ⟨hm.1,fun i => hq m i ▸ hsmall (e.symm i.succ)⟩)
    have hlog := (log_pos ((one_lt_div hε.1).mpr hε.2)).le
    have hlo : 0<(firstHit β (A*ε):ℝ) := Nat.cast_pos.mpr (one_le_firstHit β (mul_pos hA hε.1))
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm.1
    exact ⟨div_le_div_of_nonneg_right (log_le_log hlo (Nat.cast_le.mpr hlow)) hlog,
      div_le_div_of_nonneg_right (log_le_log hmpos (Nat.cast_le.mpr (Nat.sInf_le hqS))) hlog⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (Jumps.scaled_exponent (f:=fun r => (firstHit β r:ℝ)) hA hβ)
    (Jumps.scaled_exponent (f:=fun r => (firstHit β r:ℝ)) hc0 hβ)
    (hbounds.mono fun _ hh => hh.1) (hbounds.mono fun _ hh => hh.2)

#print axioms index_exponent_of_gaps
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
