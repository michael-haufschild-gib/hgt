import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.GaussianLaw

/-! # Date of the full-support subdivision before a first return -/

open Set Real Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
noncomputable section

private theorem ceiling_rate :
    Tendsto (fun ε : ℝ => log (⌈1/ε⌉₊:ℝ)/log (1/ε)) (𝓝[>] 0) (𝓝 1) := by
  have htop := (tendsto_const_div_log_one_div (log 2)).add_const 1
  rw [zero_add] at htop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε he
    have hi := (one_lt_div he.1).mpr he.2
    exact (le_div_iff₀ (log_pos hi)).mpr (by
      simpa only [one_mul] using log_le_log (one_div_pos.mpr he.1) (Nat.le_ceil (1/ε)))
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε he
    have hi := (one_lt_div he.1).mpr he.2
    have hp := one_div_pos.mpr he.1
    have hc := Nat.ceil_lt_add_one hp.le
    have hb : (⌈1/ε⌉₊:ℝ) ≤ 2*(1/ε) := by linarith only [hc,hi]
    have hl := log_le_log (hp.trans_le (Nat.le_ceil _)) hb
    rw [log_mul (by norm_num : (2:ℝ)≠0) hp.ne'] at hl
    have h := div_le_div_of_nonneg_right hl (log_pos hi).le
    simpa only [add_div,div_self (log_pos hi).ne'] using h

/-- At the first return divided by the ceiling of inverse precision,
the date has precision exponent D−3. At exactly this date and error,
every approximating circuit uses all physical sites, in every basis. -/
theorem gaussian_subperiod_date :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), ∀ s : ℕ, s+1<N →
        let t := fun ε : ℝ => firstVisit H a s ε/(⌈1/ε⌉₊:ℝ)
        Tendsto (fun ε => log (t ε)/log (1/ε)) (𝓝[>] 0) (𝓝 ((2^N-3:ℕ):ℝ)) ∧
          ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ (V : unitaryGroup (Fin N→Bool) ℂ) (C : TwoQubitCircuit N) (c : ℂ),
            ‖V.val*unitaryEvolution H.val (t ε)*star V.val-c • C.eval.val‖ ≤ ε →
              C.touchedSites=Finset.univ ∧ N ≤ 2*C.gateCount := by
  filter_upwards [gaussian_inverse_precision_subperiod,gaussian_gap_clock,
    DisconnectedReturns.gaussian_disconnected_scalar_return] with ω hwire hclock hscalar k
  intro N H a ha s hs t
  refine ⟨?_,hwire k a ha s hs⟩
  obtain ⟨e,hg,hy⟩ := hclock k
  obtain ⟨A,hA,h⟩ := hscalar (k+1)
  have hbudget : s<k+1+1 := by dsimp only [N] at hs; omega
  have hdate := exponent_of_scalar_control H e s hA (fun u ε => h u ε s hbudget) hg hy ha
  change Tendsto _ _ (𝓝 ((2^N-3+1:ℕ):ℝ)) at hdate
  have hr := hdate.sub ceiling_rate
  rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hr
  refine hr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (he : 0<ε)
  have hv := ha.trans_le (firstVisit_isLeast H a s he).1.1
  have hd := (one_div_pos.mpr he).trans_le (Nat.le_ceil (1/ε))
  change log (firstVisit H a s ε)/log (1/ε)-log (⌈1/ε⌉₊:ℝ)/log (1/ε)=
    log (firstVisit H a s ε/(⌈1/ε⌉₊:ℝ))/log (1/ε)
  rw [log_div hv.ne' hd.ne',sub_div]

#print axioms gaussian_subperiod_date
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
