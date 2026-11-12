import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailWeightedPrimeAbel
import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeRightTraceHasAGlobalPowerRemainder
import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripTraceCanBeIntegrated

/-!
# The weighted prime error retains its complete right-substrip trace

Exact Abel summation transfers the prime trace to the power-weighted
arithmetic prefix. The elementary power prefix costs a bounded remainder,
and the prime remainder keeps a strict power saving after weighting.
-/

noncomputable section

open Complex Set MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- The weighted arithmetic error after removing its shifted zero trace. -/
def powerTailPrimeRightRemainder (a σ x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, powerTailPrimeDeviation a n) +
    (rightShiftedZeroTrace σ a a x).re

/-- Abel weighting of the linear main term has an exact elementary primitive. -/
theorem weightedAbelRemainder_id {a x : ℝ} (ha1 : a < 1) (hx : 1 ≤ x) :
    weightedAbelRemainder a id x = x ^ (1 - a) / (1 - a) - a / (1 - a) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hd : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha1)
  have hhead : x ^ (-a) * x = x ^ (1 - a) := by
    have hh := (Real.rpow_add hx0 (-a) 1).symm
    simpa only [Real.rpow_one, show -a + 1 = 1 - a by ring] using hh
  have hI : (∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * id t) =
      (x ^ (1 - a) - 1) / (1 - a) := by
    have he (t : ℝ) (ht : t ∈ Ioc (1 : ℝ) x) : t ^ (-a - 1) * id t = t ^ (-a) := by
      have hh := (Real.rpow_add (zero_lt_one.trans ht.1) (-a - 1) 1).symm
      simpa only [id_eq, Real.rpow_one, sub_add_cancel] using hh
    rw [setIntegral_congr_fun measurableSet_Ioc he,
      ← intervalIntegral.integral_of_le hx,
      integral_rpow (Or.inl (by linarith only [ha1] : (-1 : ℝ) < -a)),
      show -a + 1 = 1 - a by ring, Real.one_rpow]
  rw [weightedAbelRemainder, id_eq, hhead, hI]
  field_simp <;> ring

/-- Replacing the linear main term by its actual arithmetic power prefix
costs a constant, uniformly along the positive half-line. -/
theorem abs_weightedAbelRemainder_id_sub_powerTailPrefix_le {a x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : 1 ≤ x) :
    |weightedAbelRemainder a id x - powerTailPrefix a x| ≤ (1 + a) / (1 - a) := by
  have hd : 0 < 1 - a := sub_pos.mpr ha1
  have hp := powerTailPrefix_sub_integral_bounds ha ha1 (zero_le_one.trans hx)
  have hprefix : |x ^ (1 - a) / (1 - a) - powerTailPrefix a x| ≤ 1 / (1 - a) := by
    rw [abs_sub_comm]
    exact abs_le.mpr ⟨hp.1, hp.2.trans (by positivity)⟩
  have he : weightedAbelRemainder a id x - powerTailPrefix a x =
      (x ^ (1 - a) / (1 - a) - powerTailPrefix a x) - a / (1 - a) := by
    rw [weightedAbelRemainder_id ha1 hx]
    ring
  rw [he]
  calc
    _ ≤ |x ^ (1 - a) / (1 - a) - powerTailPrefix a x| + |a / (1 - a)| := abs_sub _ _
    _ ≤ 1 / (1 - a) + a / (1 - a) :=
      add_le_add hprefix (le_of_eq (abs_of_pos (div_pos ha hd)))
    _ = _ := by ring

/-- The full prime-trace remainder has an integrable weighted Abel kernel. -/
theorem integrableOn_weightedPrimeRightTraceRemainder {a σ β x : ℝ}
    (haσ : a < σ) (hσ : 1 / 2 < σ) (hσβ : σ < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (hx : 1 ≤ x) :
    IntegrableOn (fun t => t ^ (-a - 1) * primeRightTraceRemainder σ β t) (Ioc 1 x) := by
  obtain ⟨κ, C, hσκ, _, _, hb⟩ :=
    exists_global_power_bound_primeRightTraceRemainder hσ hσβ hβ1 hβ
  exact integrableOn_powerWeightedIntegrand (haσ.trans hσκ)
    (aestronglyMeasurable_primeRightTraceRemainder hσ hβ) hb hx

/-- The actual weighted prime prefix has the shifted zero trace, a weighted
prime remainder, and only the forced elementary and endpoint constants. -/
theorem powerTailPrimeRightRemainder_eq {a σ β x : ℝ}
    (ha : 0 ≤ a) (haσ : a < σ) (hσ : 1 / 2 < σ) (hσβ : σ < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (hx : 1 ≤ x) :
    powerTailPrimeRightRemainder a σ x =
      weightedAbelRemainder a (primeRightTraceRemainder σ β) x +
        (weightedAbelRemainder a id x - powerTailPrefix a x) -
        (rightShiftedZeroTrace σ 0 0 1).re + (rightShiftedZeroTrace σ a a 1).re := by
  have ha1 : a < 1 := (haσ.trans hσβ).trans_le hβ1
  have hiid : IntegrableOn (fun t => t ^ (-a - 1) * id t) (Ioc (1 : ℝ) x) :=
    integrableOn_powerWeightedIntegrand (κ := 1) (C := 1) ha1
      measurable_id.aestronglyMeasurable
      (fun t ht => by simp only [id_eq, Real.rpow_one, one_mul,
        abs_of_nonneg (zero_le_one.trans ht), le_refl]) hx
  have hiQ := integrableOn_real_weightedRightZeroTrace hσ ha hx
  have hiR := integrableOn_weightedPrimeRightTraceRemainder haσ hσ hσβ hβ1 hβ hx
  have hR (t : ℝ) (ht : 1 ≤ t) : primeRightTraceRemainder σ β t =
      Chebyshev.psi t - t + (rightShiftedZeroTrace σ 0 0 t).re := by
    rw [primeRightTraceRemainder,
      rightShiftedZeroTrace_zero_eq_normalized (β := β) (zero_lt_one.trans_le ht)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hI : (∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * Chebyshev.psi t) =
      (∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * id t) -
        (∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * (rightShiftedZeroTrace σ 0 0 t).re) +
        ∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * primeRightTraceRemainder σ β t := by
    calc
      _ = ∫ t in Ioc (1 : ℝ) x,
          (t ^ (-a - 1) * id t - t ^ (-a - 1) * (rightShiftedZeroTrace σ 0 0 t).re) +
            t ^ (-a - 1) * primeRightTraceRemainder σ β t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp only
        rw [hR t ht.1.le]
        dsimp only [id_eq]
        ring
      _ = _ := by
        have hadd := integral_add (hiid.sub hiQ) hiR
        simp only [Pi.sub_apply] at hadd
        rw [hadd, integral_sub hiid hiQ]
  have hψ : weightedAbelRemainder a Chebyshev.psi x =
      weightedAbelRemainder a id x -
        weightedAbelRemainder a (fun t => (rightShiftedZeroTrace σ 0 0 t).re) x +
        weightedAbelRemainder a (primeRightTraceRemainder σ β) x := by
    unfold weightedAbelRemainder
    rw [hI]
    dsimp only [id_eq]
    linear_combination -(x ^ (-a)) * hR x hx
  have hQ : weightedAbelRemainder a (fun t => (rightShiftedZeroTrace σ 0 0 t).re) x =
      (rightShiftedZeroTrace σ a a x).re + (rightShiftedZeroTrace σ 0 0 1).re -
        (rightShiftedZeroTrace σ a a 1).re := rightShiftedZeroTrace_abel_real hσ ha hx
  have hs : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, powerTailPrimeDeviation a n) =
      weightedAbelRemainder a Chebyshev.psi x - powerTailPrefix a x :=
    sum_powerTailPrimeDeviation_eq_abel a hx
  rw [powerTailPrimeRightRemainder, hs, hψ, hQ]
  ring

/-- The exact weighted prime trace has a globally power-saving remainder,
with no common gap below the bounding zero line. -/
theorem exists_power_bound_powerTailPrimeRightRemainder {a σ β : ℝ}
    (ha : 0 < a) (haσ : a < σ) (hσ : 1 / 2 < σ) (hσβ : σ < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    ∃ κ C : ℝ, σ < κ ∧ κ < β ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |powerTailPrimeRightRemainder a σ x| ≤ C * x ^ (κ - a) := by
  obtain ⟨κ, C, hσκ, hκβ, hC, hb⟩ :=
    exists_global_power_bound_primeRightTraceRemainder hσ hσβ hβ1 hβ
  have ha1 : a < 1 := (haσ.trans hσβ).trans_le hβ1
  have hd1 : 0 < 1 - a := sub_pos.mpr ha1
  have hdκ : 0 < κ - a := sub_pos.mpr (haσ.trans hσκ)
  let D := C * (1 + a / (κ - a))
  let B := (1 + a) / (1 - a) + |(rightShiftedZeroTrace σ 0 0 1).re| +
    |(rightShiftedZeroTrace σ a a 1).re|
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨κ, D + B, hσκ, hκβ, add_nonneg hD hB, ?_⟩
  intro x hx
  have hW := abs_weightedAbelRemainder_le ha.le (haσ.trans hσκ) hC hb hx
  have hE := abs_weightedAbelRemainder_id_sub_powerTailPrefix_le ha ha1 hx
  have htriangle : |powerTailPrimeRightRemainder a σ x| ≤
      |weightedAbelRemainder a (primeRightTraceRemainder σ β) x| +
        |weightedAbelRemainder a id x - powerTailPrefix a x| +
        |(rightShiftedZeroTrace σ 0 0 1).re| + |(rightShiftedZeroTrace σ a a 1).re| := by
    rw [powerTailPrimeRightRemainder_eq ha.le haσ hσ hσβ hβ1 hβ hx]
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    apply (abs_sub _ _).trans
    exact add_le_add (abs_add_le _ _) le_rfl
  have hBx : B ≤ B * x ^ (κ - a) :=
    le_mul_of_one_le_right hB (Real.one_le_rpow hx hdκ.le)
  calc
    _ ≤ D * x ^ (κ - a) + B := by
      dsimp only [D, B]
      linarith only [htriangle, hW, hE]
    _ ≤ D * x ^ (κ - a) + B * x ^ (κ - a) := add_le_add le_rfl hBx
    _ = _ := by ring

/-- At a subcritical power boundary, retaining a right band leaves an
arithmetic error below the contact normalization exponent. -/
theorem exists_power_bound_powerTailPrimeRightRemainder_at_boundary {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 1 / 2 < σ) (hσβ : σ < 1 - a)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a) :
    ∃ κ C : ℝ, σ < κ ∧ κ < 1 - a ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |powerTailPrimeRightRemainder a σ x| ≤ C * x ^ (κ - a) :=
  exists_power_bound_powerTailPrimeRightRemainder ha (ha2.trans hσ) hσ hσβ
    (by linarith only [ha]) hβ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
