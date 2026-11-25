import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.PhysicalTicks
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.ScalarFloor

/-! # A deadline for the kth positive scalar return on any sampling clock -/

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
open SharpOccupation
noncomputable section

/-- The half-width scalar arc gives a uniform lower count on every finite
record, even when the period is selected after observing the spectrum. -/
theorem scalar_tick_floor {N : ℕ} (H : selfAdjoint (Register N)) {e : ℝ} (he : e∈Ioo (0:ℝ) 2)
    (h : ℝ) (n : ℕ) :
    (n:ℝ)*zeroGateArcDensity (2^N) (physicalArc e/2) ≤ ((affordableTicks H 0 e h n).card:ℝ) := by
  classical
  let i : Fin N → Bool := fun _ => false
  let f := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i
  let z (k : ℕ) := finiteClockPhasePoint f ((k:ℝ)*h)
  have hx := (FiniteRecords.physicalArc_full he).1
  let r : Icc (0:ℝ) (1/2) := ⟨physicalArc e/2,(half_pos hx.1).le,by linarith only [hx.2]⟩
  let A := relativeEnclosingUnitArc i r
  let Q (k : ℕ) := (k:ℝ)*h ∈ visitSet H 0 e
  have hd (y) (u v : ℕ) (hvu : v≤u) (hu : z u+y∈A) (hv : z v+y∈A) : Q (u-v) := by
    change ((u-v:ℕ):ℝ)*h ∈ visitSet H 0 e
    rw [Nat.cast_sub hvu,sub_mul]
    exact shifted_scalar_difference H i he y _ _ hu hv
  have ht := translated_tick_floor z A (isClosed_relativeEnclosingUnitArc i r).measurableSet Q hd n
  have hm := relativeUnitArcMass_eq_power i r
  rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hm
  change (n:ℝ)*relativeUnitArcMass i r ≤ ((affordableTicks H 0 e h n).card:ℝ) at ht
  rwa [hm] at ht

/-- Write p = D(x/2)^(D−1). At least k distinct positive ticks among
the first floor(k/p) are scalar-affordable. Counting starts at one. -/
theorem kth_scalar_tick {N : ℕ} (H : selfAdjoint (Register N)) {e : ℝ} (he : e∈Ioo (0:ℝ) 2)
    (h : ℝ) (k : ℕ) :
    let p := zeroGateArcDensity (2^N) (physicalArc e/2)
    k ≤ ((affordableTicks H 0 e h (⌊(k:ℝ)/p⌋₊+1)).erase 0).card := by
  intro p
  have hx := (FiniteRecords.physicalArc_full he).1.1
  have hp : 0<p := mul_pos (by exact_mod_cast (pow_pos (by omega : 0<2) N))
    (pow_pos (half_pos hx) _)
  let n := ⌊(k:ℝ)/p⌋₊+1
  have hn : (k:ℝ)/p < (n:ℝ) := by
    simpa only [n,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one ((k:ℝ)/p)
  have hc : k < (affordableTicks H 0 e h n).card := by
    exact_mod_cast ((div_lt_iff₀ hp).mp hn).trans_le (scalar_tick_floor H he h n)
  by_cases h0 : 0∈affordableTicks H 0 e h n
  · rw [Finset.card_erase_of_mem h0]
    omega
  · rw [Finset.erase_eq_of_notMem h0]
    exact hc.le

#print axioms scalar_tick_floor
#print axioms kth_scalar_tick
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
