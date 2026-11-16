import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.PositiveJumpBoundaryControl
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.ArithmeticIncidencePositivity.ArchimedeanBumpBridgeAndSelfEnergyAsymptotic

/-!
# Exact Lévy tails control terminal moments

Every jump longer than `d` carries the interval `(-d, 0)` outside the
supporting half-line. Integrating the full Lévy density gives the boundary
coefficient `archLevyAntideriv d`. This coefficient strictly exceeds its
first exponential mode and dominates `log(2/d) / 2` when `0 < d ≤ 1`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open _root_.RHTower WeilLevyPoleGauss WeilLevyCoshCrossover

/-- The full Lévy tail strictly improves the first exponential boundary coefficient. -/
theorem archLevyAntideriv_gt_firstMode {d : ℝ} (hd : 0 < d) :
    2 * Real.exp (-d / 2) < archLevyAntideriv d := by
  have h1 := integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) d
  have h5 := integrableOn_exp_mul_Ioi (by norm_num : -(5 / 2 : ℝ) < 0) d
  have h := setIntegral_mono_on (h1.add h5) (integrableOn_archLevyDensity_Ioi hd)
    measurableSet_Ioi (fun x hx => by
      change Real.exp (-(1 / 2 : ℝ) * x) + Real.exp (-(5 / 2 : ℝ) * x) ≤ archLevyDensity x
      simpa only [show -(1 / 2 : ℝ) * x = -x / 2 by ring,
        show -(5 / 2 : ℝ) * x = -5 * x / 2 by ring] using
          archLevyDensity_ge_twoMode (lt_trans hd hx))
  simp only [Pi.add_apply] at h
  rw [integral_add h1 h5,
    integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(5 / 2 : ℝ) < 0),
    integral_archLevyDensity_Ioi hd] at h
  have he : 0 < Real.exp (-(5 / 2 : ℝ) * d) := Real.exp_pos _
  rw [show -(1 / 2 : ℝ) * d = -d / 2 by ring] at h
  norm_num only [neg_div, div_neg, neg_neg] at h
  linarith only [h, he]

/-- A logarithmic lower bound for the exact boundary coefficient on collars of width at most one. -/
theorem log_two_div_le_twice_archLevyAntideriv {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    Real.log (2 / d) ≤ 2 * archLevyAntideriv d := by
  have h := ArithmeticIncidencePositivity.log_one_div_le_two_mul_archLevyAntideriv
    (show 0 < d / 2 by positivity) (show d / 2 ≤ 1 / 2 by linarith only [hd1])
  simpa only [show 1 / (d / 2) = 2 / d by ring,
    show 2 * (d / 2) = d by ring] using h

/-- The exact Lévy tail controls every finite nonnegative terminal jump moment. -/
theorem CriticalHalfLineEnergyDomain.jump_boundary_exact_lower
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {K : ℝ → ℝ → ℝ}
    (hK : ∀ a b, 0 ≤ K a b)
    (hi : ∀ x : ℝ, 0 < x → Integrable (fun u => K (F u) (F (u + x))))
    (hJ : IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u, K (F u) (F (u + x))) (Ioi 0)) {d : ℝ} (hd : 0 < d) :
    archLevyAntideriv d * (∫ u in Ioo (-d) 0, K (F u) 0) ≤
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, K (F u) (F (u + x)) := by
  have hinner (x : ℝ) (hx : d ≤ x) :
      (∫ u in Ioo (-d) 0, K (F u) 0) ≤ ∫ u, K (F u) (F (u + x)) := by
    calc
      _ = ∫ u in Ioo (-d) 0, K (F u) (F (u + x)) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        change K (F u) 0 = K (F u) (F (u + x))
        rw [hF.support (u + x) (by linarith only [hu.1, hx])]
      _ ≤ _ := setIntegral_le_integral (hi x (lt_of_lt_of_le hd hx))
        (Eventually.of_forall fun u => hK (F u) (F (u + x)))
  have hs : Ioi d ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans hd hx
  have htail := setIntegral_mono_on
    ((integrableOn_archLevyDensity_Ioi hd).mul_const (∫ u in Ioo (-d) 0, K (F u) 0))
    (hJ.mono_set hs) measurableSet_Ioi (fun x hx =>
      mul_le_mul_of_nonneg_left (hinner x hx.le) (archLevyDensity_pos (lt_trans hd hx)).le)
  rw [integral_mul_const, integral_archLevyDensity_Ioi hd] at htail
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun x =>
      archLevyDensity x * ∫ u, K (F u) (F (u + x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (archLevyDensity_pos hx).le
      (integral_nonneg fun u => hK (F u) (F (u + x)))
  exact htail.trans (setIntegral_mono_set hJ hn (Eventually.of_forall fun x hx => hs hx))

#print axioms archLevyAntideriv_gt_firstMode
#print axioms log_two_div_le_twice_archLevyAntideriv
#print axioms CriticalHalfLineEnergyDomain.jump_boundary_exact_lower

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
end
