import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKernel
import GaloisForLFunctions.RHTower.ThetaWignerCenterMix

/-!
# Geometric–deficit split of the theta tail first-moment kernel

In the orbit-shift parametrization `u = x + t + 2s` the theta tail first-moment kernel is

`k(x,t) = ∫_{s>0} (x + t + 2s)·Φ(x+s)·Φ(t+s) ds`.

Splitting the affine weight by the arithmetic–geometric mean identity
`a + b = 2√(ab) + (√a − √b)²` at `a = x+s`, `b = t+s` decomposes the kernel exactly into

`k = 2·(geometric part) + (deficit part)`,

where the geometric part `∫ √((x+s)(t+s))·Φ(x+s)Φ(t+s) ds` is a manifestly positive-semidefinite
kernel — its quadratic form on any finite nonnegative node system is the integral of a square of
the single nonnegative family `s ↦ √(y+s)·Φ(y+s)` — while the deficit part is entrywise
nonnegative with identically vanishing diagonal.  All positivity of the kernel therefore rides on
the geometric part dominating the negative directions of the short-range deficit.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Geometric (arithmetic–geometric mean) part of the theta tail kernel. -/
def thetaTailGeometricKernel (x t : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.sqrt ((x + s) * (t + s)) *
    (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))

/-- Deficit part of the theta tail kernel: the square-root displacement weight. -/
def thetaTailDeficitKernel (x t : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (Real.sqrt (x + s) - Real.sqrt (t + s)) ^ 2 *
    (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))

/-- Shift of a half-line integral to base point zero. -/
private theorem integral_Ioi_eq_comp_add (g : ℝ → ℝ) (a : ℝ) :
    ∫ u in Ioi a, g u = ∫ v in Ioi (0 : ℝ), g (a + v) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_add_right_eq_self
      (fun u => Set.indicator (Ioi a) g u) a]
  congr 1
  funext v
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (by simp only [mem_Ioi]; linarith : v + a ∈ Ioi a),
      Set.indicator_of_mem (mem_Ioi.mpr hv), add_comm]
  · rw [Set.indicator_of_notMem (by simp only [mem_Ioi]; intro h; exact hv (by linarith)),
      Set.indicator_of_notMem (by simpa using hv)]

/-- **Orbit-shift parametrization of the theta tail kernel.** -/
theorem thetaTailFirstMomentKernel_eq_orbitShift (x t : ℝ) :
    thetaTailFirstMomentKernel x t =
      ∫ s in Ioi (0 : ℝ), (x + t + 2 * s) *
        (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) := by
  unfold thetaTailFirstMomentKernel
  rw [integral_Ioi_eq_comp_add _ (x + t)]
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun v => thetaTailFirstMomentIntegrand x t (x + t + v)) 0 (by norm_num : (0 : ℝ) < 2)
  rw [mul_zero] at hscale
  rw [show (∫ v in Ioi (0 : ℝ), thetaTailFirstMomentIntegrand x t (x + t + v)) =
      2 * ∫ s in Ioi (0 : ℝ), thetaTailFirstMomentIntegrand x t (x + t + 2 * s) by
    rw [hscale, smul_eq_mul]
    ring]
  rw [show (1 : ℝ) / 2 * (2 * ∫ s in Ioi (0 : ℝ),
      thetaTailFirstMomentIntegrand x t (x + t + 2 * s)) =
      ∫ s in Ioi (0 : ℝ), thetaTailFirstMomentIntegrand x t (x + t + 2 * s) by ring]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold thetaTailFirstMomentIntegrand
  rw [show (x + t + 2 * s + x - t) / 2 = x + s by ring,
    show (x + t + 2 * s - x + t) / 2 = t + s by ring]
  ring

private theorem continuous_orbitFactor (y : ℝ) :
    Continuous fun s : ℝ => thetaCuspFullSource (y + s) :=
  contDiff_thetaCuspFullSource.continuous.comp (continuous_const.add continuous_id)

private theorem expConstant_nonneg : 0 ≤ thetaCuspDerivativeExpConstant 0 := by
  have h := abs_thetaCuspFullSource_le_exp_neg_abs 0
  simp only [abs_zero, neg_zero, Real.exp_zero, mul_one] at h
  exact le_trans (abs_nonneg _) h

/-- Exponential majorant for the parametrized total integrand. -/
private theorem integrableOn_orbitTotal {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    IntegrableOn (fun s => (x + t + 2 * s) *
      (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))) (Ioi (0 : ℝ)) := by
  set C : ℝ := thetaCuspDerivativeExpConstant 0 with hCdef
  have hC : 0 ≤ C := expConstant_nonneg
  have hmaj : IntegrableOn
      (fun s => C ^ 2 * Real.exp (-x - t) *
        ((x + t) * Real.exp (-2 * s) + 2 * Real.exp (-s))) (Ioi (0 : ℝ)) := by
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-2 * s)) (Ioi (0 : ℝ)) :=
      exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 2)
    have h1 : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi (0 : ℝ)) := by
      simpa using exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)
    exact (((h2.const_mul (x + t)).add (h1.const_mul 2)).const_mul _)
  refine Integrable.mono' hmaj ?_ ?_
  · exact (((continuous_const.add (continuous_const.mul continuous_id)).mul
      ((continuous_orbitFactor x).mul (continuous_orbitFactor t)))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hxs : 0 ≤ x + s := by linarith
    have hts : 0 ≤ t + s := by linarith
    have hbx := abs_thetaCuspFullSource_le_exp_neg_abs (x + s)
    have hbt := abs_thetaCuspFullSource_le_exp_neg_abs (t + s)
    rw [abs_of_nonneg hxs] at hbx
    rw [abs_of_nonneg hts] at hbt
    have hw : 0 ≤ x + t + 2 * s := by linarith
    have habs : ‖(x + t + 2 * s) *
        (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))‖ =
        (x + t + 2 * s) * (|thetaCuspFullSource (x + s)| * |thetaCuspFullSource (t + s)|) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw]
    rw [habs]
    have hstep : (x + t + 2 * s) *
        (|thetaCuspFullSource (x + s)| * |thetaCuspFullSource (t + s)|) ≤
        (x + t + 2 * s) * (C * Real.exp (-(x + s)) * (C * Real.exp (-(t + s)))) := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact mul_le_mul hbx hbt (abs_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have hexp : Real.exp (-(x + s)) * Real.exp (-(t + s)) =
        Real.exp (-x - t) * Real.exp (-2 * s) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hs_le : s * Real.exp (-2 * s) ≤ Real.exp (-s) := by
      have hexps : s ≤ Real.exp s := le_trans (by linarith) (Real.add_one_le_exp s)
      calc s * Real.exp (-2 * s) ≤ Real.exp s * Real.exp (-2 * s) :=
            mul_le_mul_of_nonneg_right hexps (Real.exp_pos _).le
        _ = Real.exp (-s) := by rw [← Real.exp_add]; ring_nf
    have hsplit : (x + t + 2 * s) * Real.exp (-2 * s) ≤
        (x + t) * Real.exp (-2 * s) + 2 * Real.exp (-s) := by
      have h2s : 2 * s * Real.exp (-2 * s) ≤ 2 * Real.exp (-s) := by nlinarith
      nlinarith [Real.exp_pos (-2 * s)]
    calc (x + t + 2 * s) * (C * Real.exp (-(x + s)) * (C * Real.exp (-(t + s)))) =
          C ^ 2 * Real.exp (-x - t) * ((x + t + 2 * s) * Real.exp (-2 * s)) := by
            rw [show C * Real.exp (-(x + s)) * (C * Real.exp (-(t + s))) =
              C ^ 2 * (Real.exp (-(x + s)) * Real.exp (-(t + s))) by ring, hexp]
            ring
      _ ≤ C ^ 2 * Real.exp (-x - t) * ((x + t) * Real.exp (-2 * s) + 2 * Real.exp (-s)) := by
            apply mul_le_mul_of_nonneg_left hsplit (by positivity)

/-- Pointwise arithmetic–geometric bound of the geometric integrand by the total integrand. -/
private theorem geometric_le_total {x t s : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (hs : 0 < s) :
    Real.sqrt ((x + s) * (t + s)) *
      (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) ≤
    (x + t + 2 * s) * (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) := by
  have hxs : 0 ≤ x + s := by linarith
  have hts : 0 ≤ t + s := by linarith
  have hP : 0 ≤ thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s) :=
    mul_nonneg (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
      (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
  have hamgm : Real.sqrt ((x + s) * (t + s)) ≤ x + t + 2 * s := by
    rw [Real.sqrt_mul hxs]
    nlinarith [Real.sq_sqrt hxs, Real.sq_sqrt hts, Real.sqrt_nonneg (x + s),
      Real.sqrt_nonneg (t + s), sq_nonneg (Real.sqrt (x + s) - Real.sqrt (t + s))]
  exact mul_le_mul_of_nonneg_right hamgm hP

private theorem integrableOn_orbitGeometric {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    IntegrableOn (fun s => Real.sqrt ((x + s) * (t + s)) *
      (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (integrableOn_orbitTotal hx ht) ?_ ?_
  · exact ((Real.continuous_sqrt.comp
      ((continuous_const.add continuous_id).mul (continuous_const.add continuous_id))).mul
      ((continuous_orbitFactor x).mul (continuous_orbitFactor t))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hP : 0 ≤ thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s) :=
      mul_nonneg (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
        (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hP)]
    exact geometric_le_total hx ht hs0

private theorem integrableOn_orbitDeficit {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    IntegrableOn (fun s => (Real.sqrt (x + s) - Real.sqrt (t + s)) ^ 2 *
      (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (integrableOn_orbitTotal hx ht) ?_ ?_
  · exact (((Real.continuous_sqrt.comp (continuous_const.add continuous_id)).sub
      (Real.continuous_sqrt.comp (continuous_const.add continuous_id))).pow 2).mul
      ((continuous_orbitFactor x).mul (continuous_orbitFactor t)) |>.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hxs : 0 ≤ x + s := by linarith
    have hts : 0 ≤ t + s := by linarith
    have hP : 0 ≤ thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s) :=
      mul_nonneg (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
        (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hP)]
    have hdef : (Real.sqrt (x + s) - Real.sqrt (t + s)) ^ 2 ≤ x + t + 2 * s := by
      nlinarith [Real.sq_sqrt hxs, Real.sq_sqrt hts, Real.sqrt_nonneg (x + s),
        Real.sqrt_nonneg (t + s), Real.sqrt_nonneg ((x + s) * (t + s)),
        Real.sqrt_mul hxs (t + s), mul_nonneg (Real.sqrt_nonneg (x + s)) (Real.sqrt_nonneg (t + s))]
    exact mul_le_mul_of_nonneg_right hdef hP

/-- **Geometric–deficit split.**  On nonnegative nodes the theta tail kernel is exactly twice
the geometric kernel plus the deficit kernel. -/
theorem thetaTailFirstMomentKernel_eq_geometric_add_deficit {x t : ℝ}
    (hx : 0 ≤ x) (ht : 0 ≤ t) :
    thetaTailFirstMomentKernel x t =
      2 * thetaTailGeometricKernel x t + thetaTailDeficitKernel x t := by
  rw [thetaTailFirstMomentKernel_eq_orbitShift]
  have hsplit : ∀ s ∈ Ioi (0 : ℝ),
      (x + t + 2 * s) * (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) =
      2 * (Real.sqrt ((x + s) * (t + s)) *
          (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s))) +
        (Real.sqrt (x + s) - Real.sqrt (t + s)) ^ 2 *
          (thetaCuspFullSource (x + s) * thetaCuspFullSource (t + s)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hxs : 0 ≤ x + s := by linarith
    have hts : 0 ≤ t + s := by linarith
    have hkey : x + t + 2 * s =
        2 * Real.sqrt ((x + s) * (t + s)) +
          (Real.sqrt (x + s) - Real.sqrt (t + s)) ^ 2 := by
      rw [Real.sqrt_mul hxs]
      nlinarith [Real.sq_sqrt hxs, Real.sq_sqrt hts]
    rw [hkey]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add ((integrableOn_orbitGeometric hx ht).const_mul 2)
      (integrableOn_orbitDeficit hx ht),
    MeasureTheory.integral_const_mul]
  rfl

/-- **Manifest positivity of the geometric part.**  The quadratic form of the geometric kernel
on any finite nonnegative node system is the integral of a square: the geometric kernel is
positive semidefinite by construction, with no arithmetic input. -/
theorem thetaTailGeometricKernel_quadraticForm_nonneg
    {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (a : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * thetaTailGeometricKernel (x i) (x j) := by
  have hterm : ∀ i j, a i * a j * thetaTailGeometricKernel (x i) (x j) =
      ∫ s in Ioi (0 : ℝ),
        (a i * (Real.sqrt (x i + s) * thetaCuspFullSource (x i + s))) *
        (a j * (Real.sqrt (x j + s) * thetaCuspFullSource (x j + s))) := by
    intro i j
    unfold thetaTailGeometricKernel
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [Real.sqrt_mul (by linarith [hx i] : (0 : ℝ) ≤ x i + s)]
    ring
  have hint : ∀ i j, IntegrableOn (fun s =>
      (a i * (Real.sqrt (x i + s) * thetaCuspFullSource (x i + s))) *
      (a j * (Real.sqrt (x j + s) * thetaCuspFullSource (x j + s)))) (Ioi (0 : ℝ)) := by
    intro i j
    refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_orbitGeometric (hx i) (hx j)).const_mul (a i * a j))
      (fun s hs => ?_) measurableSet_Ioi
    have hs0 : (0 : ℝ) < s := hs
    rw [Real.sqrt_mul (by linarith [hx i] : (0 : ℝ) ≤ x i + s)]
    ring
  calc (0 : ℝ) ≤ ∫ s in Ioi (0 : ℝ),
        (∑ i, a i * (Real.sqrt (x i + s) * thetaCuspFullSource (x i + s))) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
    _ = ∫ s in Ioi (0 : ℝ), ∑ i, ∑ j,
        (a i * (Real.sqrt (x i + s) * thetaCuspFullSource (x i + s))) *
        (a j * (Real.sqrt (x j + s) * thetaCuspFullSource (x j + s))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ∫ s in Ioi (0 : ℝ),
        (a i * (Real.sqrt (x i + s) * thetaCuspFullSource (x i + s))) *
        (a j * (Real.sqrt (x j + s) * thetaCuspFullSource (x j + s))) := by
        rw [MeasureTheory.integral_finsetSum _ fun i _ =>
          MeasureTheory.integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ =>
          MeasureTheory.integral_finsetSum _ fun j _ => hint i j
    _ = ∑ i, ∑ j, a i * a j * thetaTailGeometricKernel (x i) (x j) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hterm i j).symm

/-- The deficit kernel has identically vanishing diagonal. -/
theorem thetaTailDeficitKernel_self (x : ℝ) : thetaTailDeficitKernel x x = 0 := by
  unfold thetaTailDeficitKernel
  simp

/-- The deficit kernel is entrywise nonnegative. -/
theorem thetaTailDeficitKernel_nonneg (x t : ℝ) : 0 ≤ thetaTailDeficitKernel x t := by
  refine setIntegral_nonneg measurableSet_Ioi fun s _ => ?_
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
      (HedenmalmThetaSource.thetaCuspFullSource_pos _).le)

/-- The geometric kernel is symmetric. -/
theorem thetaTailGeometricKernel_comm (x t : ℝ) :
    thetaTailGeometricKernel x t = thetaTailGeometricKernel t x := by
  unfold thetaTailGeometricKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [mul_comm (x + s), mul_comm (thetaCuspFullSource (x + s))]

/-- The deficit kernel is symmetric. -/
theorem thetaTailDeficitKernel_comm (x t : ℝ) :
    thetaTailDeficitKernel x t = thetaTailDeficitKernel t x := by
  unfold thetaTailDeficitKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [show Real.sqrt (x + s) - Real.sqrt (t + s) =
      -(Real.sqrt (t + s) - Real.sqrt (x + s)) by ring, neg_sq,
    mul_comm (thetaCuspFullSource (x + s))]

end

end RHTower
