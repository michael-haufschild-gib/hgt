import GaloisForLFunctions.HTGeometry.WindingReturnEquivalence
import GaloisForLFunctions.HTGeometry.FirstHitExponentLaw

/-! # Integer clocks for the first simultaneous collision of spectral gaps -/

open Real
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

private theorem close_neg {x r : ℝ} (h : latticeClose x r) : latticeClose (-x) r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨-p,by simpa only [Int.cast_neg,neg_sub_neg,abs_sub_comm] using hp⟩

/-- Waiting for the first ratio hit gives a simultaneous collision of
all physical gaps. Taking the absolute date allows either sign of the
reference gap. -/
theorem return_at_integer_clock {n : ℕ} (g : Fin (n+1) → ℝ) (hg : g 0≠0) {r : ℝ} (hr : 0<r) :
    let y := fun i : Fin n => gapRatio g i.succ
    let q := firstHit y r
    ContinuousReturn g r ((2*π/|g 0|)*(q:ℝ)) := by
  intro y q
  let t := 2*π*(q:ℝ)/g 0
  have hw : WindingReturn g r (q:ℤ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [gapRatio_zero g hg,mul_one]
      exact ⟨(q:ℤ),by rw [sub_self,abs_zero]; exact hr⟩
    · simpa only [Int.cast_natCast] using (firstHit_mem y hr).2 j
  have h := continuousReturn_of_windingReturn g hg hw
  have ht : ContinuousReturn g r t := by simpa only [t,Int.cast_natCast] using h
  have ht' : |t| = (2*π/|g 0|)*(q:ℝ) := by
    rw [abs_div,abs_mul,abs_of_pos two_pi_pos,abs_of_nonneg (Nat.cast_nonneg q)]
    ring
  rw [←ht']
  rcases le_or_gt 0 t with hpos | hneg
  · rwa [abs_of_nonneg hpos]
  · rw [abs_of_neg hneg]
    intro i
    simpa only [gapTurn,neg_mul,neg_div] using close_neg (ht i)

/-- Any collision after a positive origin supplies a nonzero anchor winding.
Its absolute value bounds the first ratio hit and grows at most linearly
in the physical date. -/
theorem integer_clock_le_of_return {n : ℕ} (g : Fin (n+1) → ℝ) (hg : g 0≠0)
    {a r t : ℝ} (ha : 0<a) (hat : a≤t) (hr : r<a*|g 0|/(2*π))
    (h : ContinuousReturn g r t) :
    let y := fun i : Fin n => gapRatio g i.succ
    let A := ‖gapRatio g‖
    (firstHit y ((1+A)*r):ℝ) ≤ 2*(|g 0|/(2*π))*t := by
  intro y A
  have hA (i) : |gapRatio g i| ≤ A := norm_le_pi_norm (gapRatio g) i
  obtain ⟨q,hq,hw⟩ := exists_windingReturn_of_continuousReturn g hg hA h
  have hbig : r < t*|g 0|/(2*π) := hr.trans_le (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hat (abs_nonneg _)) two_pi_pos.le)
  have hq₀ : q ≠ 0 := by
    intro hzero
    rw [hzero,Int.cast_zero,sub_zero,gapTurn,abs_div,abs_mul,abs_of_pos (ha.trans_le hat),abs_of_pos two_pi_pos] at hq
    exact hbig.asymm hq
  have hnat : (q.natAbs:ℝ)=|(q:ℝ)| := by rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  have hhit : ∀ i : Fin n, latticeClose ((q.natAbs:ℝ)*y i) ((1+A)*r) := by
    intro i
    rw [hnat,mul_comm (1+A) r]
    rcases le_or_gt (0:ℝ) q with hpos | hneg
    · rw [abs_of_nonneg hpos]; exact hw i.succ
    · rw [abs_of_neg hneg,neg_mul]; exact close_neg (hw i.succ)
  have hn : firstHit y ((1+A)*r) ≤ q.natAbs := Nat.sInf_le ⟨Int.natAbs_pos.mpr hq₀,hhit⟩
  have hbound := abs_winding_le_of_continuousReturn g hq
  rw [abs_of_pos (ha.trans_le hat)] at hbound
  apply (Nat.cast_le.mpr hn).trans
  rw [hnat]
  calc |(q:ℝ)| ≤ t*|g 0|/(2*π)+r := hbound
       _ ≤ t*|g 0|/(2*π)+t*|g 0|/(2*π) := add_le_add le_rfl hbig.le
       _ = _ := by ring

#print axioms return_at_integer_clock
#print axioms integer_clock_le_of_return
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
