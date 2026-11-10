import GaloisForLFunctions.VerifiedHeightRungs.WindowEntries
import GaloisForLFunctions.SquareRootThreshold.EvenAndOddTwoBumpTestsDecideTheCriticalLine
import Mathlib.Data.Nat.Find

/-!
# Prime two-bump signs from a verified height

The cubic spline has radius four. Its two-bump packet at separation
`log p` fits in aperture `4 + log p / 2`. The finite maximum of the
admissible integer apertures gives an explicit, unbounded prime rung.
-/

open Set Filter Topology
open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.VerifiedHeightRungs

/-- Height sufficient for every cubic-spline two-bump packet at lags up to `log n`. -/
def primePacketHeight (n : ℕ) : ℝ := windowHeightOfOne (4 + Real.log n / 2)

/-- Largest certified integer cutoff below the height itself; zero if none is certified. -/
def primePacketRung (T : ℝ) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => primePacketHeight n ≤ T) ⌊T⌋₊

/-- Every fixed prime cutoff is eventually included in the explicit rung. -/
theorem primePacketRung_cofinal (n : ℕ) :
    ∀ T : ℝ, max (n : ℝ) (primePacketHeight n) ≤ T → n ≤ primePacketRung T := by
  classical
  intro T hT
  exact Nat.le_findGreatest (Nat.le_floor ((le_max_left _ _).trans hT))
    ((le_max_right _ _).trans hT)

/-- The explicit prime cutoffs tend to infinity with the verified height. -/
theorem tendsto_primePacketRung : Tendsto primePacketRung atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  filter_upwards [eventually_ge_atTop (max (n : ℝ) (primePacketHeight n))] with T hT
  exact primePacketRung_cofinal n T hT

/-- A two-bump packet of a radius-four spline has aperture `4 + v/2`. -/
theorem tsupport_twoBump_spline_subset {v : ℝ} (hv : 0 ≤ v) (τ : ℂ) :
    tsupport (twoBump (boxSpline 1 3) v τ) ⊆ Icc (-(4 + v / 2)) (4 + v / 2) := by
  have hbs : ∀ u, boxSpline 1 3 u ≠ 0 → |u| ≤ 4 := by
    intro u hu
    have h := boxSpline_support one_pos 3 u hu
    norm_num at h
    exact h
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have ht' : twoBump (boxSpline 1 3) v τ t ≠ 0 := ht
  rw [twoBump_apply] at ht'
  by_cases h1 : boxSpline 1 3 (t + v / 2) = 0
  · have h2 : boxSpline 1 3 (t - v / 2) ≠ 0 := fun h => ht' (by rw [h1, h]; ring)
    obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h2)
    exact ⟨by linarith only [h3, hv], by linarith only [h4]⟩
  · obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h1)
    exact ⟨by linarith only [h3], by linarith only [h4, hv]⟩

/-- A verified height certifies both signs, and every complex coefficient, at every prime below its rung. -/
theorem prime_twoBump_nonneg_of_rhVerifiedThrough {T : ℝ} (hRH : RHVerifiedThrough T)
    {p : ℕ} (hp : p.Prime) (hpT : p ≤ primePacketRung T) (τ : ℂ) :
    0 ≤ (zetaZeroConfig.W (twoBump (boxSpline 1 3) (Real.log p) τ)
      (twoBump (boxSpline 1 3) (Real.log p) τ)).re := by
  classical
  let P := primePacketRung T
  have hPpos : 0 < P := hp.pos.trans_le hpT
  have hheight : primePacketHeight P ≤ T :=
    (Nat.findGreatest_eq_iff.mp (show
      Nat.findGreatest (fun n => primePacketHeight n ≤ T) ⌊T⌋₊ = P from rfl)).2.1
      (Nat.ne_of_gt hPpos)
  have hlogP : 0 ≤ Real.log P :=
    Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hPpos))
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlogs : Real.log p ≤ Real.log P :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpT)
  apply re_W_nonneg_of_rhVerifiedThrough (a := 4 + Real.log P / 2)
    (by linarith only [hlogP]) hheight hRH
    (contDiff_bumpTest (contDiff_boxSpline one_pos 2) (Real.log p) ![1, τ])
  exact (tsupport_twoBump_spline_subset hlogp τ).trans
    (Icc_subset_Icc (by linarith only [hlogs]) (by linarith only [hlogs]))

#print axioms primePacketRung_cofinal
#print axioms tendsto_primePacketRung
#print axioms prime_twoBump_nonneg_of_rhVerifiedThrough

end GaloisForLFunctions.VerifiedHeightRungs
