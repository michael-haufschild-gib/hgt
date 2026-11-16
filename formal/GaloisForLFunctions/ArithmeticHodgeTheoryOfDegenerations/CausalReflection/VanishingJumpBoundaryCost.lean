import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExactJumpBoundaryControl
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing boundary cost for finite jump energy

The terminal moment tends to zero by local integrability. Multiplying it
by the Lévy tail still gives a vanishing quantity: each fixed crossing
jump sees vanishing terminal mass, and the full jump-energy density is
an integrable majorant. The logarithmically weighted moment also tends
to zero, strengthening the boundary estimate to a little-o condition.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open _root_.RHTower WeilLevyPoleGauss WeilLevyCoshCrossover

/-- Locally integrable densities have vanishing mass on shrinking terminal intervals. -/
theorem terminal_moment_tendsto_zero {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo (-1) 0)) :
    Tendsto (fun d : ℝ => ∫ u in Ioo (-d) 0, g u) (𝓝[>] 0) (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (μ := volume.restrict (Ioo (-1 : ℝ) 0))
    (F := fun d : ℝ => (Ioo (-d) 0).indicator g) (f := fun _ => (0 : ℝ))
    (fun u => ‖g u‖)
    (Eventually.of_forall fun d => hg.aestronglyMeasurable.indicator measurableSet_Ioo)
    (Eventually.of_forall fun d => Eventually.of_forall fun u => by
      by_cases hu : u ∈ Ioo (-d) 0
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu, norm_zero]
        exact norm_nonneg _)
    hg.norm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have he : ∀ᶠ d : ℝ in 𝓝[>] 0, d < -u :=
        (eventually_lt_nhds (neg_pos.mpr hu.2)).filter_mono nhdsWithin_le_nhds
      apply Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℝ)) ?_ tendsto_const_nhds
      filter_upwards [he] with d hd
      rw [indicator_of_notMem (show u ∉ Ioo (-d) 0 by
        intro h; linarith only [h.1, hd])])
  have he : ∀ᶠ d : ℝ in 𝓝[>] 0, d < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  apply Filter.Tendsto.congr' (f₁ := fun d : ℝ =>
    ∫ u in Ioo (-1 : ℝ) 0, (Ioo (-d) 0).indicator g u) ?_
    (by simpa only [integral_zero] using hlim)
  filter_upwards [he] with d hd
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo (-d) 0 ⊆ Ioo (-1 : ℝ) 0 from
      fun u hu => ⟨by linarith only [hu.1, hd], hu.2⟩)]

/-- A vanishing factor kills a moving tail when one integrable density dominates the products. -/
theorem tail_integral_mul_tendsto_zero_of_domination {w J M : ℝ → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hJ : IntegrableOn J (Ioi 0)) (hJn : ∀ x : ℝ, 0 < x → 0 ≤ J x)
    (hM : Tendsto M (𝓝[>] 0) (𝓝 0))
    (hb : ∀ d : ℝ, 0 < d → ∀ x : ℝ, d < x → ‖w x * M d‖ ≤ J x) :
    Tendsto (fun d : ℝ => (∫ x in Ioi d, w x) * M d) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := self_mem_nhdsWithin
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun d : ℝ => (Ioi d).indicator (fun x => w x * M d))
    (f := fun _ => (0 : ℝ)) J
    (Eventually.of_forall fun d => (hw.mul_const (M d)).indicator measurableSet_Ioi)
    (by
      filter_upwards [hpos] with d hd
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      by_cases hdx : d < x
      · rw [indicator_of_mem (show x ∈ Ioi d from hdx)]
        exact hb d hd x hdx
      · rw [indicator_of_notMem (show x ∉ Ioi d from hdx), norm_zero]
        exact hJn x hx)
    hJ (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hl : Tendsto (fun d : ℝ => w x * M d) (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hM)
      apply Filter.Tendsto.congr' (f₁ := fun d : ℝ => w x * M d) ?_ hl
      filter_upwards [(eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with d hd
      rw [indicator_of_mem (show x ∈ Ioi d from hd)])
  apply Filter.Tendsto.congr' (f₁ := fun d : ℝ =>
    ∫ x in Ioi (0 : ℝ), (Ioi d).indicator (fun x => w x * M d) x) ?_
    (by simpa only [integral_zero] using hlim)
  filter_upwards [hpos] with d hd
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (show Ioi d ⊆ Ioi (0 : ℝ) from fun x hx => lt_trans hd hx),
    integral_mul_const]

/-- Finite nonnegative jump energy forces the exact terminal boundary cost to vanish. -/
theorem CriticalHalfLineEnergyDomain.jump_boundary_exact_tendsto_zero
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {K : ℝ → ℝ → ℝ}
    (hK : ∀ a b, 0 ≤ K a b)
    (hi : ∀ x : ℝ, 0 < x → Integrable (fun u => K (F u) (F (u + x))))
    (hJ : IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u, K (F u) (F (u + x))) (Ioi 0)) :
    Tendsto (fun d : ℝ => archLevyAntideriv d * (∫ u in Ioo (-d) 0, K (F u) 0))
      (𝓝[>] 0) (𝓝 0) := by
  have hg : IntegrableOn (fun u => K (F u) 0) (Ioo (-1) 0) := by
    refine (hi 1 (by norm_num)).integrableOn.congr_fun ?_ measurableSet_Ioo
    intro u hu
    change K (F u) (F (u + 1)) = K (F u) 0
    rw [hF.support (u + 1) (by linarith only [hu.1])]
  have hlim := tail_integral_mul_tendsto_zero_of_domination
    (w := archLevyDensity)
    (J := fun x => archLevyDensity x * ∫ u, K (F u) (F (u + x)))
    (M := fun d => ∫ u in Ioo (-d) 0, K (F u) 0)
    (continuousOn_archLevyDensity.aestronglyMeasurable measurableSet_Ioi) hJ
    (fun x hx => mul_nonneg (archLevyDensity_pos hx).le
      (integral_nonneg fun u => hK (F u) (F (u + x))))
    (terminal_moment_tendsto_zero hg) (by
      intro d hd x hdx
      have hx : 0 < x := lt_trans hd hdx
      have hN : 0 ≤ ∫ u in Ioo (-d) 0, K (F u) 0 :=
        integral_nonneg fun u => hK (F u) 0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos hx).le hN)]
      apply mul_le_mul_of_nonneg_left _ (archLevyDensity_pos hx).le
      calc
        _ = ∫ u in Ioo (-d) 0, K (F u) (F (u + x)) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro u hu
          change K (F u) 0 = K (F u) (F (u + x))
          rw [hF.support (u + x) (by linarith only [hu.1, hdx])]
        _ ≤ _ := setIntegral_le_integral (hi x hx)
          (Eventually.of_forall fun u => hK (F u) (F (u + x))))
  apply Filter.Tendsto.congr' (f₁ := fun d : ℝ =>
    (∫ x in Ioi d, archLevyDensity x) * (∫ u in Ioo (-d) 0, K (F u) 0)) ?_ hlim
  filter_upwards [show ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d from self_mem_nhdsWithin] with d hd
  rw [integral_archLevyDensity_Ioi hd]

/-- A vanishing exact boundary cost implies a vanishing logarithmically weighted moment. -/
theorem logarithmic_moment_tendsto_zero_of_exact_cost {M : ℝ → ℝ}
    (hM : ∀ d : ℝ, 0 < d → 0 ≤ M d)
    (hlim : Tendsto (fun d : ℝ => archLevyAntideriv d * M d) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun d : ℝ => Real.log (2 / d) * M d) (𝓝[>] 0) (𝓝 0) := by
  have hdpos : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := self_mem_nhdsWithin
  have hdsmall : ∀ᶠ d : ℝ in 𝓝[>] 0, d < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have htwice : Tendsto (fun d : ℝ => 2 * (archLevyAntideriv d * M d))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul 2
  refine squeeze_zero' ?_ ?_ htwice
  · filter_upwards [hdpos, hdsmall] with d hd hd1
    exact mul_nonneg (Real.log_nonneg ((one_le_div hd).mpr (by linarith only [hd1]))) (hM d hd)
  · filter_upwards [hdpos, hdsmall] with d hd hd1
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (log_two_div_le_twice_archLevyAntideriv hd hd1.le) (hM d hd)

#print axioms CriticalHalfLineEnergyDomain.jump_boundary_exact_tendsto_zero
#print axioms logarithmic_moment_tendsto_zero_of_exact_cost

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
end
