import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.FirstPeriods
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.GeometricScales

/-! # Doubly exponential first scalar waits from one specified late antipode -/

open Set MeasureTheory Filter Real Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open SharpOccupation
noncomputable section

/-- For each b above the physical arc fraction, the whole continuous
window of b^(-D) periods is free of zero-gate visits with probability
at least 1−c^(D−3). The late-winding limit precedes the prefix-size limit. -/
theorem gaussian_first_wait_after_late_antipode {ε b : ℝ}
    (hε : ε∈Ioo (0:ℝ) (sqrt 2)) (hxb : physicalArc ε < b) (hb : b < 1) :
    ∃ c∈Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      pathPauliDisorderLaw.real {ω | firstPeriods k n ε ω ≤ (1/b)^(2^(k+3))} < c^(2^(k+3)-3) := by
  let x := physicalArc ε
  have hx := (physicalArc_spec hε.1 hε.2).1
  obtain ⟨y,hxy,hy'⟩ := exists_between (lt_min hxb hx.2)
  have hy := hx.1.trans hxy
  have hyb := hy'.trans_le (min_le_left ..)
  let δ := y-x
  have hd : 0 < δ := sub_pos.mpr hxy
  have he : x+δ=y := by dsimp only [δ]; ring
  obtain ⟨c,hc,hsize⟩ := grid_count_decay hy hyb hb hd
  let d (k : ℕ) := 2^(k+3)-3
  have hk (k : ℕ) : k ≤ d k := by
    have := Nat.lt_two_pow_self (n:=k+3)
    dsimp only [d]
    omega
  have hD (k : ℕ) : d k+3=2^(k+3) := by
    have := Nat.lt_two_pow_self (n:=k+3)
    dsimp only [d]
    omega
  have htop : Tendsto d atTop atTop := tendsto_atTop_mono hk tendsto_id
  refine ⟨c,hc,?_⟩
  filter_upwards [htop.eventually hsize] with k hrate
  let D := 2^(k+3)
  let M := ⌈(1/b)^D/δ⌉₊
  let p := ((d k:ℝ)+2)*y^(d k)
  have hp : 0 < p := mul_pos (by positivity) (pow_pos hy _)
  have hcard : Fintype.card (Outside (topLevel k) 0)=d k+1 := by
    rw [outside_card _ _ (top_pos k).ne.symm,Fintype.card_fin,←hD k]
    omega
  have hmass : (Fintype.card (Outside (topLevel k) 0):ℝ≥0∞)*
      ENNReal.ofReal (x+δ)^(Fintype.card (Outside (topLevel k) 0)-1) < ENNReal.ofReal p := by
    rw [hcard,he,Nat.add_sub_cancel,←ENNReal.ofReal_pow hy.le,←ENNReal.ofReal_natCast,
      ←ENNReal.ofReal_mul (Nat.cast_nonneg (α:=ℝ) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff hp).mpr
    apply mul_lt_mul_of_pos_right _ (pow_pos hy _)
    push_cast
    linarith
  have hm := gaussian_window_bound k M hx.1.le hd (he.trans_le (hy'.le.trans (min_le_right ..))) hmass
  have hM : (1/b)^D ≤ (M:ℝ)*δ := (div_le_iff₀ hd).mp (Nat.le_ceil _)
  filter_upwards [hm] with n hn
  have hle := (measure_mono (μ:=pathPauliDisorderLaw)
    (show {ω | firstPeriods k n ε ω ≤ (1/b)^D}⊆{ω | firstPeriods k n ε ω ≤ (M:ℝ)*δ} from fun _ hh => hh.trans hM)).trans
    ((first_wait_measure_le k n hε ((M:ℝ)*δ)).trans hn)
  have hv := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hle
  change pathPauliDisorderLaw.real _ ≤ _ at hv
  simp only [ENNReal.toReal_mul,Nat.cast_add,Nat.cast_one,ENNReal.toReal_ofReal hp.le] at hv
  apply hv.trans_lt
  change ((M:ℝ)+1)*(((d k:ℝ)+2)*y^(d k)) < c^(d k)
  rw [←mul_assoc]
  simpa only [hD k,D,M] using hrate

#print axioms gaussian_first_wait_after_late_antipode
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
