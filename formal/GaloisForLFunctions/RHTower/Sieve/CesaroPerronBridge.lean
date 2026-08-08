import GaloisForLFunctions.RHTower.Sieve.CesaroKernelPrimitives
import GaloisForLFunctions.RHTower.Sieve.PerronLemma

/-!
# The Cesàro kernel is the logarithmic average of the sharp-cutoff kernel

`(y^s − 1)/s² = ∫_1^y (u^s/s)·du/u` for every `s ≠ 0`, because `∫_1^y u^{s−1}du = (y^s − 1)/s`.
Integrating that identity over the truncated line and interchanging — legitimate on a compact box, the
integrand being continuous once the cutoff variable is clamped away from zero — gives

`∫_{|t| ≤ T} (y^s − 1)/s² dt = ∫_1^y (∫_{|t| ≤ T} u^s/s dt)·du/u`.

So the truncated Cesàro kernel integral is the exact logarithmic average of the truncated sharp-cutoff
kernel integral, and every estimate for the latter transfers to the former by averaging.  Since the
sharp kernel integral is `1 + O(u^σ/(T log u))` above the cutoff and `O(u^σ/(T|log u|))` below it, the
average is `log y + (an average of those errors)`, and the average of `1/|log u|` in `du/u` is finite
where the pointwise value is not — which is why the Cesàro route needs no near-diagonal analysis.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **Fubini on a box for a continuous vector-valued integrand.**  The complex-valued counterpart of
`interval_integral_swap_of_continuous`. -/
theorem interval_integral_swap_of_continuous_vec {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ → ℝ → ℂ} (hF : Continuous (Function.uncurry F)) :
    (∫ u in a..b, ∫ t in c..d, F u t) = ∫ t in c..d, ∫ u in a..b, F u t := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := ⟨by simp [Real.volume_Ioc]⟩
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc c d)) := ⟨by simp [Real.volume_Ioc]⟩
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hcd, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_integral_swap ?_
  refine MeasureTheory.Integrable.mono' (integrable_const C) hF.aestronglyMeasurable ?_
  rw [MeasureTheory.Measure.prod_restrict]
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  exact hC p ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩

/-- The integrand of the averaging identity, with the cutoff variable clamped away from zero so that it
is continuous on the whole plane. -/
def cesaroBox (σ : ℝ) : ℝ → ℝ → ℂ := fun u t =>
  ((max u 1 : ℝ) : ℂ) ^ (((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I)

theorem continuous_cesaroBox {σ : ℝ} (hσ : 0 < σ) :
    Continuous (Function.uncurry (cesaroBox σ)) := by
  have hbase : Continuous fun p : ℝ × ℝ => (((max p.1 1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.max continuous_const)
  have hexp : Continuous fun p : ℝ × ℝ => ((σ : ℂ) + (p.2 : ℝ) * I - 1) :=
    (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)).sub continuous_const
  have hden : Continuous fun p : ℝ × ℝ => ((σ : ℂ) + (p.2 : ℝ) * I) :=
    continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hnum : Continuous fun p : ℝ × ℝ =>
      (((max p.1 1 : ℝ) : ℂ)) ^ ((σ : ℂ) + (p.2 : ℝ) * I - 1) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hslit : (((max p.1 1 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      simp only [Complex.ofReal_re]
      exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact hbase.continuousAt.cpow hexp.continuousAt hslit
  exact hnum.div hden fun p => line_ne_zero hσ p.2

/-- **The Cesàro kernel integral is the logarithmic average of the sharp-cutoff kernel integral.** -/
theorem integral_cesaro_eq_integral_perron {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {y : ℝ}
    (hy : 1 ≤ y) :
    (∫ t in (-T)..T,
        (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
      = ∫ u in (1 : ℝ)..y, (∫ t in (-T)..T,
          ((u : ℂ)) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) / (u : ℂ) := by
  have hFubini := interval_integral_swap_of_continuous_vec hy (by linarith : -T ≤ T)
    (continuous_cesaroBox hσ)
  have hinner : ∀ t : ℝ, (∫ u in (1 : ℝ)..y, cesaroBox σ u t)
      = (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2 := by
    intro t
    have hs := line_ne_zero hσ t
    have hcongr : (∫ u in (1 : ℝ)..y, cesaroBox σ u t)
        = ∫ u in (1 : ℝ)..y,
            ((u : ℂ)) ^ (((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hy, Set.mem_Icc] at hu
      rw [cesaroBox, max_eq_left hu.1]
    rw [hcongr, intervalIntegral.integral_div, integral_cpow_sub_one_eq hs hy]
    field_simp
  have houter : ∀ u ∈ Set.uIcc (1 : ℝ) y, (∫ t in (-T)..T, cesaroBox σ u t)
      = (∫ t in (-T)..T,
          ((u : ℂ)) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) / (u : ℂ) := by
    intro u hu
    rw [Set.uIcc_of_le hy, Set.mem_Icc] at hu
    have hupos : (0 : ℝ) < u := by linarith [hu.1]
    have hu0 : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hupos.ne'
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [cesaroBox, max_eq_left hu.1, Complex.cpow_sub _ _ hu0, Complex.cpow_one]
    ring
  have h1 : (∫ t in (-T)..T, ∫ u in (1 : ℝ)..y, cesaroBox σ u t)
      = ∫ t in (-T)..T,
          (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2 :=
    intervalIntegral.integral_congr fun t _ => hinner t
  have h2 : (∫ u in (1 : ℝ)..y, ∫ t in (-T)..T, cesaroBox σ u t)
      = ∫ u in (1 : ℝ)..y, (∫ t in (-T)..T,
          ((u : ℂ)) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) / (u : ℂ) :=
    intervalIntegral.integral_congr houter
  rw [← h1, ← hFubini, h2]

/-- **The Cesàro Perron kernel as an average of the sharp-cutoff Perron kernel.**  Normalised form of
the averaging identity: the `1/2π`-scaled Cesàro integral is the logarithmic average of
`perronVertical`. -/
theorem perron_cesaro_eq_average {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {y : ℝ} (hy : 1 ≤ y) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ)
        * ∫ t in (-T)..T,
            (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2
      = ∫ u in (1 : ℝ)..y, perronVertical σ T u / (u : ℂ) := by
  rw [integral_cesaro_eq_integral_perron hσ hT hy, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [perronVertical]
  ring

end RHTower.Sieve
end
