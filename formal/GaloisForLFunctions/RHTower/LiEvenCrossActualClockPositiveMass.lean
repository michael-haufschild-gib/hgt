import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelGrowth
import GaloisForLFunctions.RHTower.LiClockVolterraPositiveMass
import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentClockLimit
/-!
# Divergent positive mass and cofinal corridors of the actual LI clock

The exact theta-source Volterra identity and escape of its weighted Borel degree force divergent
positive-part mass of the literal complete-source clock. Positive clock values occur beyond every
threshold and yield eventual positive actual currents along their prescribed shrinking masses.
No reciprocal-moment sign hypothesis or RH premise enters the source capstones.
-/

open MeasureTheory Filter Topology Set
namespace RHTower
noncomputable section

/-- Exact source logarithmic-degree lower bound for accumulated positive clock mass. -/
theorem liEvenCrossActualClock_logDegree_le_clockPositiveMass
    {t : ℝ} (ht : 0 < t) :
    t * deriv liEvenCrossActualClockBorelKernel t / liEvenCrossActualClockBorelKernel t ≤
      8 * ∫ w in (0 : ℝ)..(t^2/16), max (liEvenCrossActualCurrentClockSeries w) 0 := by
  have h := liClockVolterra_positivePartIntegral_ge_ratio
    continuous_liEvenCrossActualClockResponse continuous_liEvenCrossActualClockBorelKernel
    (fun t _ => liEvenCrossActualClockBorelKernel_pos t)
    (fun _a ha _b _hb hab => liEvenCrossActualClockBorelKernel_mono ha hab)
    (fun _t ht => liEvenCrossActualClockResponse_volterra ht) ht
  rw [liEvenCrossActualClockBorel_mul_deriv]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, max (liEvenCrossActualClockResponse s) 0 := h
    _ = _ := by
      simpa only [liEvenCrossActualClockResponse] using
        liClock_positivePartIntegral_eq_eight_mul continuous_liEvenCrossActualCurrentClockSeries ht.le

/-- The literal source response has divergent positive-part mass. -/
theorem liEvenCrossActualClockResponse_positiveMass_tendsto :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t,
      max (liEvenCrossActualClockResponse s) 0) atTop atTop := by
  exact liClockVolterra_tendsto_positivePartIntegral_atTop
    continuous_liEvenCrossActualClockResponse continuous_liEvenCrossActualClockBorelKernel
    (fun t _ => liEvenCrossActualClockBorelKernel_pos t)
    (fun _a ha _b _hb hab => liEvenCrossActualClockBorelKernel_mono ha hab)
    (fun _t ht => liEvenCrossActualClockResponse_volterra ht)
    liEvenCrossActualClockBorelWeighted_div_kernel_tendsto_atTop

/-- Positive-part mass of the literal complete-source clock tends to infinity. -/
theorem liEvenCrossActualCurrentClockSeries_positiveMass_tendsto :
    Tendsto (fun w : ℝ => ∫ z in (0 : ℝ)..w,
      max (liEvenCrossActualCurrentClockSeries z) 0) atTop atTop := by
  exact liClock_tendsto_positivePartIntegral_atTop continuous_liEvenCrossActualCurrentClockSeries
    liEvenCrossActualClockResponse_positiveMass_tendsto

/-- Actual clock values are strictly positive beyond every real threshold. -/
theorem liEvenCrossActualCurrentClockSeries_positive_cofinally :
    ∀ W : ℝ, ∃ w > W, 0 < liEvenCrossActualCurrentClockSeries w :=
  liClock_positive_cofinally_of_tendsto_positivePartIntegral
    continuous_liEvenCrossActualCurrentClockSeries
    liEvenCrossActualCurrentClockSeries_positiveMass_tendsto

/-- A positive clock value yields eventual positive actual currents along its shrinking-mass corridor. -/
theorem liEvenCrossSquareMassAdjacentCurrent_eventually_pos_of_clockSeries_pos
    {w : ℝ} (hw : 0 < w) (hS : 0 < liEvenCrossActualCurrentClockSeries w) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < liEvenCrossSquareMassAdjacentCurrent (w / ((n + 1 : ℕ) : ℝ)^2) n := by
  have hNat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi := tendsto_inv_atTop_zero.comp hNat
  have hvzero : Tendsto (fun n : ℕ => w / ((n + 1 : ℕ) : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, inv_pow, div_eq_mul_inv, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      using (tendsto_const_nhds (x := w)).mul (hi.pow 2)
  have hvpos (n : ℕ) : 0 < w / ((n + 1 : ℕ) : ℝ)^2 := by positivity
  have hv : Tendsto (fun n : ℕ => w / ((n + 1 : ℕ) : ℝ)^2)
      atTop (𝓝[Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hvzero, Eventually.of_forall hvpos⟩
  have hclock : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^2 *
      (w / ((n + 1 : ℕ) : ℝ)^2)) atTop (𝓝 w) := by
    have heq : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^2 *
        (w / ((n + 1 : ℕ) : ℝ)^2)) = (fun _n : ℕ => w) := by
      funext n
      have hn : (((n + 1 : ℕ) : ℝ)^2) ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact tendsto_const_nhds
  have hl := tendsto_liEvenCrossSquareMassAdjacentCurrent_clock hv hclock
  have hp : ∀ᶠ n : ℕ in atTop,
      0 < liEvenCrossSquareMassAdjacentCurrent (w / ((n + 1 : ℕ) : ℝ)^2) n := by
    filter_upwards [hl.eventually (lt_mem_nhds hS)] with n hn
    have hd : 0 < 2 * ((n + 1 : ℕ) : ℝ)^2 := by positivity
    simpa only [zero_mul] using (lt_div_iff₀ hd).mp hn
  exact eventually_atTop.mp hp

/-- Positive actual-current corridors exist beyond every clock threshold. -/
theorem liEvenCrossSquareMassAdjacentCurrent_positiveCorridors_cofinally :
    ∀ W : ℝ, ∃ w > W, 0 < w ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < liEvenCrossSquareMassAdjacentCurrent (w / ((n + 1 : ℕ) : ℝ)^2) n := by
  intro W
  obtain ⟨w, hw, hS⟩ := liEvenCrossActualCurrentClockSeries_positive_cofinally (max W 0)
  have hwW : W < w := lt_of_le_of_lt (le_max_left _ _) hw
  have hw0 : 0 < w := lt_of_le_of_lt (le_max_right _ _) hw
  exact ⟨w, hwW, hw0,
    liEvenCrossSquareMassAdjacentCurrent_eventually_pos_of_clockSeries_pos hw0 hS⟩
end
end RHTower
