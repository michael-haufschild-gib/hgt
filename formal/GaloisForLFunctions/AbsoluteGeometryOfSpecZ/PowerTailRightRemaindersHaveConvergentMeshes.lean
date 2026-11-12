import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrimeErrorKeepsItsRightTrace
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRiemannSumsAcrossJumps

/-!
# Convergent harmonic meshes after removing the right-substrip trace

The arithmetic staircase and zero trace can each have a nonintegrable
endpoint. Their exact difference has a strictly smaller power exponent.
The cutoff criterion therefore applies to the difference itself and pays
the normalized harmonic convolution without discarding its constant limit.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- In inverse coordinates the exact arithmetic remainder has convergent
right meshes, although its two summands need not be integrable separately. -/
theorem riemannOn_powerTailPrimeRightRemainder {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 1 / 2 < σ) (hσβ : σ < 1 - a)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a) :
    RiemannOn (fun t : ℝ => t ^ (-(2 * a)) * powerTailPrimeRightRemainder a σ (1 / t)) := by
  obtain ⟨κ, C, hσκ, hκβ, _, hB⟩ :=
    exists_power_bound_powerTailPrimeRightRemainder_at_boundary ha ha2 hσ hσβ hβ
  have hexp : 0 < a + κ := by linarith only [ha, hσ, hσκ]
  have hexp1 : a + κ < 1 := by linarith only [hκβ]
  let Q : ℝ → ℝ := fun x => (rightShiftedZeroTrace σ a a (max 1 x)).re
  have hQc : Continuous Q := by
    have hcomplex : Continuous (fun x : ℝ => rightShiftedZeroTrace σ a a (max 1 x)) :=
      (continuousOn_rightShiftedZeroTrace hσ ha.le).comp_continuous
        (continuous_const.max continuous_id) (fun x => by
          change (1 : ℝ) ≤ max 1 x
          exact le_max_left _ _)
    exact Complex.continuous_re.comp hcomplex
  let g : ℝ → ℝ := fun t => -(t ^ (-(2 * a)) * Q (1 / t))
  have hgm : Measurable g :=
    ((measurable_id.pow_const (-(2 * a))).mul
      (hQc.measurable.comp (measurable_const.div measurable_id))).neg
  have hgc : ContinuousOn g (Ioc 0 1) := by
    intro t ht
    have hp : ContinuousAt (fun x : ℝ => x ^ (-(2 * a))) t :=
      continuousAt_id.rpow_const (Or.inl ht.1.ne')
    have hinv : ContinuousAt (fun x : ℝ => 1 / x) t :=
      continuousAt_const.div continuousAt_id ht.1.ne'
    have hq : ContinuousAt (fun x : ℝ => Q (1 / x)) t := hQc.continuousAt.comp hinv
    have hg : ContinuousAt g t := (hp.mul hq).neg
    exact hg.continuousWithinAt
  have he (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      arithmeticPowerProfile (2 * a) (powerTailPrimeDeviation a) t - g t =
        t ^ (-(2 * a)) * powerTailPrimeRightRemainder a σ (1 / t) := by
    have htinv : 1 ≤ 1 / t := (le_div_iff₀ ht.1).mpr (by simpa only [one_mul] using ht.2)
    dsimp only [arithmeticPowerProfile, powerTailPrimeRightRemainder, g, Q]
    rw [max_eq_right htinv]
    ring
  have hb (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      |arithmeticPowerProfile (2 * a) (powerTailPrimeDeviation a) t - g t| ≤
        C * t ^ (-(a + κ)) := by
    have htinv : 1 ≤ 1 / t := (le_div_iff₀ ht.1).mpr (by simpa only [one_mul] using ht.2)
    rw [he t ht, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    calc
      _ ≤ t ^ (-(2 * a)) * (C * (1 / t) ^ (κ - a)) :=
        mul_le_mul_of_nonneg_left (hB (1 / t) htinv) (Real.rpow_nonneg ht.1.le _)
      _ = C * t ^ (-(a + κ)) := by
        rw [Real.div_rpow zero_le_one ht.1.le, Real.one_rpow, one_div,
          ← Real.rpow_neg ht.1.le]
        calc
          _ = C * (t ^ (-(2 * a)) * t ^ (-(κ - a))) := by ring
          _ = _ := by rw [← Real.rpow_add ht.1]; congr 2; ring
  exact (riemannOn_arithmeticPowerProfile_sub_continuous
    (by linarith only [ha] : 0 ≤ 2 * a) hexp hexp1 hgm hgc hb).congr he

/-- The harmonic convolution of the exact remainder converges to its
inverse-coordinate integral. No uniform gap beneath the boundary is used. -/
theorem tendsto_normalized_powerTailPrimeRightRemainder {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 1 / 2 < σ) (hσβ : σ < 1 - a)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * a - 1) *
      ∑ m ∈ Finset.Icc 1 N, powerTailWeight (2 * a) m *
        powerTailPrimeRightRemainder a σ ((N : ℝ) / m)) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        t ^ (-(2 * a)) * powerTailPrimeRightRemainder a σ (1 / t))) := by
  have h := (riemannOn_powerTailPrimeRightRemainder ha ha2 hσ hσβ hβ).2
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact tailRiemannSum_inverse_power_eq (2 * a) (powerTailPrimeRightRemainder a σ) hN

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
