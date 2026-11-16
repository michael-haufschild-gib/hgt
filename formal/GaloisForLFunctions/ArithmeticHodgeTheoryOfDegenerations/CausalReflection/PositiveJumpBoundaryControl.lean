import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation

/-!
# Terminal moments controlled by nonnegative jump energies

For jumps longer than `d`, every point in `(-d, 0)` lands beyond the
supporting half-line. The first exponential mode of the Gamma Levy
density therefore gives the explicit boundary coefficient `2 exp(-d/2)`.
The estimate applies to any nonnegative jump kernel whose actual inner
and outer integrals are finite.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open _root_.RHTower

/-- An exact exponential tail coefficient for jumps crossing a terminal interval. -/
private theorem integral_halfExp_tail (d : ℝ) :
    (∫ x in Ioi d, Real.exp (-(1 / 2 : ℝ) * x)) = 2 * Real.exp (-d / 2) := by
  rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
  rw [show -(1 / 2 : ℝ) * d = -d / 2 by ring]
  ring

/-- Crossing jumps control the terminal moment of any nonnegative finite jump kernel. -/
theorem CriticalHalfLineEnergyDomain.jump_boundary_lower
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {K : ℝ → ℝ → ℝ}
    (hK : ∀ a b, 0 ≤ K a b)
    (hi : ∀ x : ℝ, 0 < x → Integrable (fun u => K (F u) (F (u + x))))
    (hJ : IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u, K (F u) (F (u + x))) (Ioi 0)) {d : ℝ} (hd : 0 < d) :
    (2 * Real.exp (-d / 2)) * (∫ u in Ioo (-d) 0, K (F u) 0) ≤
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, K (F u) (F (u + x)) := by
  have hN : 0 ≤ ∫ u in Ioo (-d) 0, K (F u) 0 :=
    integral_nonneg fun u => hK (F u) 0
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
  have he : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x)) (Ioi d) :=
    integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) d
  have htail := setIntegral_mono_on
    (he.mul_const (∫ u in Ioo (-d) 0, K (F u) 0)) (hJ.mono_set hs)
    measurableSet_Ioi (fun x hx => by
      have hmode := WeilLevyPoleGauss.archLevyDensity_ge_oneMode (lt_trans hd hx)
      rw [show -x / 2 = -(1 / 2 : ℝ) * x by ring] at hmode
      exact mul_le_mul hmode (hinner x (le_of_lt hx)) hN
        (archLevyDensity_pos (lt_trans hd hx)).le)
  rw [integral_mul_const, integral_halfExp_tail] at htail
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun x =>
      archLevyDensity x * ∫ u, K (F u) (F (u + x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (archLevyDensity_pos hx).le
      (integral_nonneg fun u => hK (F u) (F (u + x)))
  exact htail.trans (setIntegral_mono_set hJ hn (Eventually.of_forall fun x hx => hs hx))

#print axioms CriticalHalfLineEnergyDomain.jump_boundary_lower

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
end
