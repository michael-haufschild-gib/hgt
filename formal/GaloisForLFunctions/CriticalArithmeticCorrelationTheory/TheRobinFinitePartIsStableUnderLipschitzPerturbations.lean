import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheMixedRobinExpansionSurvivesActualOverlap

/-!
# Lipschitz control of the finite Robin part

Factoring the difference of squared increments removes the singular factor
`1/y` before integration. The finite part is controlled by the Lipschitz
constant of the profile difference and the original absolute masses.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis

private theorem integrableOn_robinDensity {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (W : ℝ) :
    IntegrableOn (fun y => (∫ u, (f u - f (u + y)) ^ 2) / (2 * y)) (Ioc 0 W) := by
  obtain ⟨L, _hL, hLip⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    (hf.of_le (by norm_num)) hfc
  have hm : StronglyMeasurable (fun y => ∫ u, (f u - f (u + y)) ^ 2) := by
    have hc : Continuous fun p : ℝ × ℝ => (f p.2 - f (p.2 + p.1)) ^ 2 := by
      have h := hf.continuous
      fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  apply Measure.integrableOn_of_bounded (M := L * ∫ u, |f u|)
    (measure_Ioc_lt_top).ne
    ((hm.measurable.div (measurable_const.mul measurable_id)).aestronglyMeasurable)
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  refine Filter.Eventually.of_forall fun y hy => ?_
  change ‖(∫ u, (f u - f (u + y)) ^ 2) / (2 * y)‖ ≤ L * ∫ u, |f u|
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (integral_nonneg fun u => sq_nonneg _) (by linarith only [hy.1]))]
  have h := integral_sub_shift_sq_le_lipschitz hf.continuous hfc (fun u v => hLip v u) y
  rw [abs_of_pos hy.1] at h
  rw [div_le_iff₀ (by linarith only [hy.1])]
  nlinarith only [h]

private theorem abs_square_increment_integral_sub_le {f g : ℝ → ℝ} {L y : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hL : 0 ≤ L)
    (hLip : ∀ u v, |(f u - g u) - (f v - g v)| ≤ L * |u - v|) (hy : 0 < y) :
    |(∫ u, (f u - f (u + y)) ^ 2) - (∫ u, (g u - g (u + y)) ^ 2)| ≤
      2 * L * y * ((∫ u, |f u|) + ∫ u, |g u|) := by
  have hfQ := _root_.RHTower.WeilMarkovPole.integrable_sub_shift_sq hf hfc y
  have hgQ := _root_.RHTower.WeilMarkovPole.integrable_sub_shift_sq hg hgc y
  have hfA : Integrable (fun u => |f u|) := (hf.integrable_of_hasCompactSupport hfc).abs
  have hgA : Integrable (fun u => |g u|) := (hg.integrable_of_hasCompactSupport hgc).abs
  have hfS := hfA.comp_add_right y
  have hgS := hgA.comp_add_right y
  have hfAS : Integrable (fun u => |f u| + |f (u + y)|) := hfA.add hfS
  have hfgAS : Integrable (fun u => |f u| + |f (u + y)| + |g u|) := hfAS.add hgA
  have hpoint : ∀ u,
      |(f u - f (u + y)) ^ 2 - (g u - g (u + y)) ^ 2| ≤
        (L * y) * (|f u| + |f (u + y)| + |g u| + |g (u + y)|) := by
    intro u
    have hd : |(f u - g u) - (f (u + y) - g (u + y))| ≤ L * y := by
      have h := hLip u (u + y)
      simpa only [show u - (u + y) = -y by ring, abs_neg, abs_of_pos hy] using h
    have hfsub : |f u - f (u + y)| ≤ |f u| + |f (u + y)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f u) (-f (u + y))
    have hgsub : |g u - g (u + y)| ≤ |g u| + |g (u + y)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (g u) (-g (u + y))
    have hs : |(f u - f (u + y)) + (g u - g (u + y))| ≤
        |f u| + |f (u + y)| + |g u| + |g (u + y)| := by
      have h := (abs_add_le (f u - f (u + y)) (g u - g (u + y))).trans
        (add_le_add hfsub hgsub)
      simpa only [add_assoc] using h
    rw [show (f u - f (u + y)) ^ 2 - (g u - g (u + y)) ^ 2 =
      ((f u - g u) - (f (u + y) - g (u + y))) *
        ((f u - f (u + y)) + (g u - g (u + y))) by ring, abs_mul]
    exact mul_le_mul hd hs (abs_nonneg _) (mul_nonneg hL hy.le)
  rw [← integral_sub hfQ hgQ]
  calc
    _ ≤ ∫ u, |(f u - f (u + y)) ^ 2 - (g u - g (u + y)) ^ 2| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u, (L * y) * (|f u| + |f (u + y)| + |g u| + |g (u + y)|) :=
      integral_mono (hfQ.sub hgQ).abs (((hfA.add hfS).add hgA).add hgS |>.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add hfgAS hgS,
        integral_add hfAS hgA, integral_add hfA hfS,
        integral_add_right_eq_self (fun u => |f u|) y,
        integral_add_right_eq_self (fun u => |g u|) y]
      ring

/-- The singular Robin density has a finite perturbation cost determined by
the Lipschitz constant of the difference, uniformly in its translations. -/
theorem abs_bumpRobin_sub_le_lipschitz_difference {f g : ℝ → ℝ} {W L : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hLip : ∀ u v, |(f u - g u) - (f v - g v)| ≤ L * |u - v|) :
    |bumpRobin f W - bumpRobin g W| ≤
      W * L * ((∫ u, |f u|) + ∫ u, |g u|) := by
  have hfD := integrableOn_robinDensity hf hfc W
  have hgD := integrableOn_robinDensity hg hgc W
  have hpoint : ∀ y ∈ Ioc 0 W,
      |(∫ u, (f u - f (u + y)) ^ 2) / (2 * y) -
        (∫ u, (g u - g (u + y)) ^ 2) / (2 * y)| ≤
          L * ((∫ u, |f u|) + ∫ u, |g u|) := by
    intro y hy
    rw [← sub_div, abs_div, abs_of_pos (by linarith only [hy.1] : 0 < 2 * y),
      div_le_iff₀ (by linarith only [hy.1])]
    have h := abs_square_increment_integral_sub_le hf.continuous hfc hg.continuous hgc hL hLip hy.1
    nlinarith only [h]
  unfold bumpRobin
  rw [← integral_sub hfD hgD]
  calc
    _ ≤ ∫ y in Ioc 0 W,
        |(∫ u, (f u - f (u + y)) ^ 2) / (2 * y) -
          (∫ u, (g u - g (u + y)) ^ 2) / (2 * y)| := abs_integral_le_integral_abs
    _ ≤ ∫ _ in Ioc 0 W, L * ((∫ u, |f u|) + ∫ u, |g u|) :=
      setIntegral_mono_on (hfD.sub hgD).abs (integrableOn_const (by simp))
        measurableSet_Ioc hpoint
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hW, sub_zero]
      ring

private theorem integral_abs_add_le {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ u, |f u + g u|) ≤ (∫ u, |f u|) + ∫ u, |g u| := by
  have hfA : Integrable (fun u => |f u|) := (hf.integrable_of_hasCompactSupport hfc).abs
  have hgA : Integrable (fun u => |g u|) := (hg.integrable_of_hasCompactSupport hgc).abs
  rw [← integral_add hfA hgA]
  exact integral_mono ((hf.add hg).integrable_of_hasCompactSupport (hfc.add hgc)).abs
    (hfA.add hgA) (fun u => abs_add_le _ _)

/-- The finite mixed Robin part is stable under profile perturbation with a
bound independent of the displacement, including every overlapping pair. -/
theorem abs_mixedBumpRobin_shift_sub_le {f g : ℝ → ℝ} {W L : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hLip : ∀ u v, |(f u - g u) - (f v - g v)| ≤ L * |u - v|) (a : ℝ) :
    |mixedBumpRobin f (fun u => f (u - a)) W -
      mixedBumpRobin g (fun u => g (u - a)) W| ≤
        2 * W * L * ((∫ u, |f u|) + ∫ u, |g u|) := by
  have hfS : ContDiff ℝ 2 (fun u => f (u - a)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  have hgS : ContDiff ℝ 2 (fun u => g (u - a)) :=
    hg.comp (contDiff_id.sub contDiff_const)
  have hfcS := hfc.comp_homeomorph (Homeomorph.subRight a)
  have hgcS := hgc.comp_homeomorph (Homeomorph.subRight a)
  have hLp : ∀ u v,
      |((f u + f (u - a)) - (g u + g (u - a))) -
        ((f v + f (v - a)) - (g v + g (v - a)))| ≤ (2 * L) * |u - v| := by
    intro u v
    have h₁ := hLip u v
    have h₂ := hLip (u - a) (v - a)
    rw [sub_sub_sub_cancel_right] at h₂
    rw [show ((f u + f (u - a)) - (g u + g (u - a))) -
      ((f v + f (v - a)) - (g v + g (v - a))) =
        ((f u - g u) - (f v - g v)) +
          ((f (u - a) - g (u - a)) - (f (v - a) - g (v - a))) by ring]
    exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)
  have hLm : ∀ u v,
      |((-f u + f (u - a)) - (-g u + g (u - a))) -
        ((-f v + f (v - a)) - (-g v + g (v - a)))| ≤ (2 * L) * |u - v| := by
    intro u v
    have h₁ := hLip u v
    have h₂ := hLip (u - a) (v - a)
    rw [sub_sub_sub_cancel_right] at h₂
    rw [show ((-f u + f (u - a)) - (-g u + g (u - a))) -
      ((-f v + f (v - a)) - (-g v + g (v - a))) =
        -((f u - g u) - (f v - g v)) +
          ((f (u - a) - g (u - a)) - (f (v - a) - g (v - a))) by ring]
    have h := abs_add_le (-((f u - g u) - (f v - g v)))
      ((f (u - a) - g (u - a)) - (f (v - a) - g (v - a)))
    rw [abs_neg] at h
    exact (h.trans (add_le_add h₁ h₂)).trans_eq (by ring)
  have hpf : (∫ u, |f u + f (u - a)|) ≤ 2 * ∫ u, |f u| := by
    have h := integral_abs_add_le hf.continuous hfc hfS.continuous hfcS
    rw [integral_sub_right_eq_self (fun u => |f u|) a] at h
    linarith only [h]
  have hpg : (∫ u, |g u + g (u - a)|) ≤ 2 * ∫ u, |g u| := by
    have h := integral_abs_add_le hg.continuous hgc hgS.continuous hgcS
    rw [integral_sub_right_eq_self (fun u => |g u|) a] at h
    linarith only [h]
  have hmf : (∫ u, |-f u + f (u - a)|) ≤ 2 * ∫ u, |f u| := by
    have h := integral_abs_add_le hf.continuous.neg hfc.neg hfS.continuous hfcS
    change (∫ u, |-f u + f (u - a)|) ≤ (∫ u, |-f u|) + ∫ u, |f (u - a)| at h
    simp only [abs_neg, integral_sub_right_eq_self (fun u => |f u|) a] at h
    linarith only [h]
  have hmg : (∫ u, |-g u + g (u - a)|) ≤ 2 * ∫ u, |g u| := by
    have h := integral_abs_add_le hg.continuous.neg hgc.neg hgS.continuous hgcS
    change (∫ u, |-g u + g (u - a)|) ≤ (∫ u, |-g u|) + ∫ u, |g (u - a)| at h
    simp only [abs_neg, integral_sub_right_eq_self (fun u => |g u|) a] at h
    linarith only [h]
  have hp := abs_bumpRobin_sub_le_lipschitz_difference (hf.add hfS) (hfc.add hfcS)
    (hg.add hgS) (hgc.add hgcS) hW (by positivity : 0 ≤ 2 * L) hLp
  have hm := abs_bumpRobin_sub_le_lipschitz_difference (hf.neg.add hfS) (hfc.neg.add hfcS)
    (hg.neg.add hgS) (hgc.neg.add hgcS) hW (by positivity : 0 ≤ 2 * L) hLm
  have hmassp := mul_le_mul_of_nonneg_left (add_le_add hpf hpg)
    (mul_nonneg hW (by positivity : 0 ≤ 2 * L))
  have hmassm := mul_le_mul_of_nonneg_left (add_le_add hmf hmg)
    (mul_nonneg hW (by positivity : 0 ≤ 2 * L))
  have heq : mixedBumpRobin f (fun u => f (u - a)) W -
      mixedBumpRobin g (fun u => g (u - a)) W =
      ((bumpRobin (fun u => f u + f (u - a)) W - bumpRobin (fun u => g u + g (u - a)) W) -
        (bumpRobin (fun u => -f u + f (u - a)) W - bumpRobin (fun u => -g u + g (u - a)) W)) / 4 := by
    unfold mixedBumpRobin
    ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have htriangle := abs_add_le
    (bumpRobin (fun u => f u + f (u - a)) W - bumpRobin (fun u => g u + g (u - a)) W)
    (-(bumpRobin (fun u => -f u + f (u - a)) W - bumpRobin (fun u => -g u + g (u - a)) W))
  rw [abs_neg, ← sub_eq_add_neg] at htriangle
  linarith only [htriangle, hp, hm, hmassp, hmassm]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_bumpRobin_sub_le_lipschitz_difference
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_mixedBumpRobin_shift_sub_le
