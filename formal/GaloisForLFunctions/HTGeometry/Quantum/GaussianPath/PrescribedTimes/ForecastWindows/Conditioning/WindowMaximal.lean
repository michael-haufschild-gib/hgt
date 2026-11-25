import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! # A weak bound for the worst resolution of a one-dimensional forecast -/

open Set MeasureTheory Metric
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section

/-- Centers admitting at least one window with mass greater than L times
its radius. This allows arbitrarily narrow windows and laws with atoms. -/
def excessCenters (ν : Measure ℝ) (L : ℝ) : Set ℝ :=
  {t | ∃ h> (0:ℝ), L*h<ν.real (ball t h)}

/-- The bad centers have total length at most 8/L for every probability
law. Disjoint bad balls pay for fourfold enlargements covering the centers. -/
theorem volume_excessCenters (ν : Measure ℝ) [IsProbabilityMeasure ν] {L : ℝ} (hL : 0<L) :
    volume (excessCenters ν L)≤ENNReal.ofReal (8/L) := by
  classical
  let S := excessCenters ν L
  choose r hr hm using fun p : S => p.property
  have hcap (p : S) : r p≤1/L := (le_div_iff₀ hL).mpr
    (by rw [mul_comm]; exact (hm p).le.trans measureReal_le_one)
  obtain ⟨u,_,hd,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ:Set S) Subtype.val r (1/L) (fun p _ => hcap p) 4 (by norm_num)
  have hc := hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun p _ => ⟨p.val,mem_ball_self (hr p)⟩)
  letI : Countable u := hc.to_subtype
  let B (p : u) := ball p.val.val (r p.val)
  let G (p : u) := ball p.val.val (4*r p.val)
  have hsub : S⊆⋃ p : u, G p := by
    intro t ht
    let p : S := ⟨t,ht⟩
    obtain ⟨j,hj,hh⟩ := hcover p (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hh (mem_ball_self (hr p))⟩
  have hd' : Pairwise (Function.onFun Disjoint B) := fun p q hpq =>
    hd p.property q.property (Subtype.val_injective.ne hpq)
  have hmass (p : u) : volume (G p)≤ENNReal.ofReal (8/L)*ν (B p) := by
    change volume (ball _ _)≤_
    rw [Real.volume_ball,←ofReal_measureReal (measure_ne_top ν (B p)),←ENNReal.ofReal_mul (by positivity : 0≤8/L)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (hm p.val).le (by positivity : 0≤8/L)
    exact (show 2*(4*r p.val)=8/L*(L*r p.val) by field_simp [hL.ne']; ring).trans_le h
  calc
    volume S ≤ volume (⋃ p : u, G p) := measure_mono hsub
    _ ≤ ∑' p : u, volume (G p) := measure_iUnion_le _
    _ ≤ ∑' p : u, ENNReal.ofReal (8/L)*ν (B p) := ENNReal.tsum_le_tsum hmass
    _ = ENNReal.ofReal (8/L)*ν (⋃ p : u, B p) := by
      rw [ENNReal.tsum_mul_left,measure_iUnion hd' (fun _ => isOpen_ball.measurableSet)]
    _ ≤ ENNReal.ofReal (8/L) := by
      simpa only [mul_one] using mul_le_mul_right (prob_le_one : ν (⋃ p : u, B p)≤1) (ENNReal.ofReal (8/L))

#print axioms volume_excessCenters
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
