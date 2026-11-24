import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GapTimes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Jumps.VisitJump

/-! # Continuous collision clock for an extremal family of energy gaps -/

open Filter Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

private theorem scaled_integer_time {n : ℕ} (hn : 0<n) {y : Fin n → ℝ}
    (hy : ¬KleinbockMargulis.VWA y) {B K : ℝ} (hB : 0<B) (hK : 0<K) :
    Tendsto (fun ε : ℝ => log (B*(firstHit y (K*ε):ℝ))/log (1/ε))
      (𝓝[>] 0) (𝓝 (n:ℝ)) := by
  have h := (tendsto_const_div_log_one_div (log B)).add
    (Jumps.scaled_exponent hK (tendsto_log_firstHit_div_log hn hy))
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (he : 0<ε)
  have hq : 0 < (firstHit y (K*ε):ℝ) := Nat.cast_pos.mpr (one_le_firstHit _ (mul_pos hK he))
  change log B/log (1/ε)+log (firstHit y (K*ε):ℝ)/log (1/ε)=_
  rw [log_mul hB.ne' hq.ne',add_div]

/-- With r independent gaps whose ratios are extremal, no collision occurs
below precision exponent r−1, and some collision occurs below every larger
exponent. The estimates allow arbitrary fixed origin and radius factor. -/
theorem optimal_gap_window {n : ℕ} (hn : 0<n) (g : Fin (n+1) → ℝ) (hg : g 0≠0)
    (hy : ¬KleinbockMargulis.VWA (fun i : Fin n => gapRatio g i.succ))
    {a K lo hi : ℝ} (ha : 0<a) (hK : 0<K) (hlo : lo<(n:ℝ)) (hhi : (n:ℝ)<hi) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (∀ t ≥ a, ContinuousReturn g (K*ε) t → lo < log t/log (1/ε)) ∧
      ∃ t ≥ a, ContinuousReturn g (K*ε) t ∧ log t/log (1/ε) < hi := by
  let y := fun i : Fin n => gapRatio g i.succ
  let A := ‖gapRatio g‖
  let B := 2*(|g 0|/(2*π))
  let Z := 2*π/|g 0|
  have hp := abs_pos.mpr hg
  have hB : 0<B := by dsimp only [B]; positivity
  have hZ : 0<Z := div_pos two_pi_pos hp
  have hA : 0<1+A := by dsimp only [A]; positivity
  have hclock := scaled_integer_time hn hy (one_div_pos.mpr hB) (mul_pos hA hK)
  have hupper := scaled_integer_time hn hy hZ hK
  have hscale : Tendsto (fun ε : ℝ => K*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Continuous (fun ε : ℝ => K*ε) := by fun_prop
      simpa only [mul_zero] using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with ε (he : 0<ε) using mul_pos hK he
  obtain ⟨M,hM⟩ := exists_nat_ge (a/Z)
  have hq := ((tendsto_firstHit_atTop hy).comp hscale).eventually_ge_atTop M
  have hcut : 0 < a*|g 0|/(2*π)/K := div_pos (div_pos (mul_pos ha hp) two_pi_pos) hK
  filter_upwards [hclock.eventually_const_lt hlo,hupper.eventually_lt_const hhi,hq,
    Ioo_mem_nhdsGT hcut,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hlow hu hlate he he'
  let q := firstHit y (K*ε)
  have hqpos : 0 < (firstHit y (((1+A)*K)*ε):ℝ) :=
    Nat.cast_pos.mpr (one_le_firstHit _ (mul_pos (mul_pos hA hK) he.1))
  refine ⟨?_,Z*(q:ℝ),?_,return_at_integer_clock g hg (mul_pos hK he.1),hu⟩
  · intro t hat h
    have hr : K*ε < a*|g 0|/(2*π) := by simpa only [mul_comm K] using (lt_div_iff₀ hK).mp he.2
    have hh := integer_clock_le_of_return g hg ha hat hr h
    change (firstHit y ((1+A)*(K*ε)):ℝ) ≤ B*t at hh
    rw [←mul_assoc] at hh
    have hb : (1/B)*(firstHit y (((1+A)*K)*ε):ℝ) ≤ t := by
      rw [one_div,inv_mul_le_iff₀ hB]
      exact hh
    exact hlow.trans_le (div_le_div_of_nonneg_right
      (log_le_log (mul_pos (one_div_pos.mpr hB) hqpos) hb) (log_pos ((one_lt_div he'.1).mpr he'.2)).le)
  · have hbound : a/Z ≤ (q:ℝ) := hM.trans (Nat.cast_le.mpr hlate)
    simpa only [mul_comm Z] using (div_le_iff₀ hZ).mp hbound

#print axioms optimal_gap_window
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
