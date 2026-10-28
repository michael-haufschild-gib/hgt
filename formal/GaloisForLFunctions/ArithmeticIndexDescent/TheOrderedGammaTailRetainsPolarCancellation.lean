import GaloisForLFunctions.ArithmeticIndexDescent.TouchingCellsPayTheFullMixedSource
import GaloisForLFunctions.RHTower.CHMDStage6PolarDoubleZeroAndContinuumLogMomentCollapse

/-!
# Pole cancellation across an ordered source boundary

The first Gamma exponential is exactly one polar term of the ordered cross block. The
remaining Gamma tail is the original boundary kernel conjugated by exponential
distance weights. Its mixed loss is therefore localized near the boundary;
the surviving global pole and signed prime interaction remain explicit.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate
open RHTower RHTower.WeilSpectral Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private theorem sectionCorr_eq_crossCorr_swap (f g : ℝ → ℝ) (h : ℝ) :
    sectionCorr f g h = RHTower.crossCorr g f h := by
  unfold sectionCorr RHTower.crossCorr
  rw [← integral_add_right_eq_self (μ := volume) (fun u => g u * f (u - h)) h]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [add_sub_cancel_right, mul_comm]

private theorem crossCorr_ordered_eq_zero {f g : ℝ → ℝ} {b h : ℝ}
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) (hh : h ≤ 0) :
    RHTower.crossCorr g f h = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  change g u * f (u - h) = 0
  by_cases hu : u ≤ b
  · rw [hright u hu, zero_mul]
  · rw [hleft (u - h) (by linarith only [le_of_not_ge hu, hh]), mul_zero]

/-- The first Gamma exponential is precisely the inward polar product. -/
theorem integral_exp_neg_half_sourceCollar_of_ordered {f g : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    (∫ h in Ioi (0 : ℝ), Real.exp (-h / 2) * sourceCollarCorrelation f g h) =
      poleA f * poleB g := by
  have he : (∫ h in Ioi (0 : ℝ), Real.exp (-h / 2) * sourceCollarCorrelation f g h) =
      ∫ h, Real.exp ((-1 / 2 : ℝ) * h) * RHTower.crossCorr g f h := by
    calc
      _ = ∫ h in Ioi (0 : ℝ), Real.exp ((-1 / 2 : ℝ) * h) * RHTower.crossCorr g f h := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro h hh
        dsimp only
        rw [sourceCollarCorrelation_ordered hleft hright hh.le]
        change Real.exp (-h / 2) * sectionCorr f g h = _
        rw [sectionCorr_eq_crossCorr_swap]
        congr 2
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by
        rw [crossCorr_ordered_eq_zero hleft hright (le_of_not_gt hh), mul_zero]
  rw [he, CHMDStage6.integral_exp_mul_crossCorr_eq hg hgc hf hfc (-1 / 2)]
  have hB : (∫ t : ℝ, g t * Real.exp ((-1 / 2 : ℝ) * t)) = poleB g := by
    unfold poleB
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    ring
  have hA : (∫ t : ℝ, f t * Real.exp (-(-1 / 2 : ℝ) * t)) = poleA f := by
    unfold poleA
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    ring
  rw [hB, hA, mul_comm]

/-- The Gamma tail after removing its first rank-one exponential. -/
def orderedGammaTail (f g : ℝ → ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), Real.exp (-2 * h) * archLevyDensity h *
    sourceCollarCorrelation f g h

/-- The actual Gamma density recursively splits into one exponential and its damped tail. -/
theorem archLevyDensity_first_mode {h : ℝ} (hh : 0 < h) :
    archLevyDensity h = Real.exp (-h / 2) + Real.exp (-2 * h) * archLevyDensity h := by
  have hd : 0 < 1 - Real.exp (-2 * h) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hh]))
  have hm : archLevyDensity h * (1 - Real.exp (-2 * h)) = Real.exp (-h / 2) := by
    exact div_mul_cancel₀ _ hd.ne'
  nlinarith only [hm]

private theorem integrableOn_exp_sourceCollar_ordered {f g : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    IntegrableOn (fun h => Real.exp (-h / 2) * sourceCollarCorrelation f g h) (Ioi 0) := by
  have hc : Continuous (fun h => Real.exp (-h / 2) * RHTower.crossCorr g f h) :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      (CHMDStage6.continuous_crossCorr_of_hasCompactSupport hg hf hfc)
  have hs : HasCompactSupport (fun h => Real.exp (-h / 2) * RHTower.crossCorr g f h) :=
    (CHMDStage6.hasCompactSupport_crossCorr_of_hasCompactSupport hgc hfc).mul_left
  refine (hc.integrable_of_hasCompactSupport hs).integrableOn.congr_fun
    (fun h hh => ?_) measurableSet_Ioi
  dsimp only
  rw [sourceCollarCorrelation_ordered hleft hright hh.le]
  change _ = Real.exp (-h / 2) * sectionCorr f g h
  rw [sectionCorr_eq_crossCorr_swap]

/-- Full Gamma interaction splits into the exact inward pole product and a localized tail. -/
theorem sourceGammaCollar_eq_pole_add_tail {f g : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    (∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation f g h) =
      poleA f * poleB g + orderedGammaTail f g := by
  have hfg (u : ℝ) : f u * g u = 0 := by
    by_cases hu : b ≤ u
    · rw [hleft u hu, zero_mul]
    · rw [hright u (le_of_not_ge hu), mul_zero]
  have hi := integrableOn_sourceCollar_of_disjoint hf hfc hg hgc hfg
  have he := integrableOn_exp_sourceCollar_ordered hf.continuous hfc hg.continuous hgc hleft hright
  have ht : IntegrableOn (fun h => Real.exp (-2 * h) * archLevyDensity h *
      sourceCollarCorrelation f g h) (Ioi 0) := by
    refine (hi.sub he).congr_fun (fun h hh => ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]
    linear_combination sourceCollarCorrelation f g h * archLevyDensity_first_mode hh
  calc
    _ = (∫ h in Ioi (0 : ℝ), Real.exp (-h / 2) * sourceCollarCorrelation f g h) +
        orderedGammaTail f g := by
      rw [orderedGammaTail, ← integral_add he ht]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h hh
      dsimp only
      linear_combination sourceCollarCorrelation f g h * archLevyDensity_first_mode hh
    _ = _ := by rw [integral_exp_neg_half_sourceCollar_of_ordered
      hf.continuous hfc hg.continuous hgc hleft hright]

/-- One ordered polar product cancels before the actual prime and Gamma source is estimated. -/
theorem realWeilForm_ordered_pole_cancellation (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) :
    realWeilForm f g = poleB f.1 * poleA g.1 -
      (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f.1) (cx g.1))).re - orderedGammaTail f.1 g.1 := by
  have hfg (u : ℝ) : f.1 u * g.1 u = 0 := by
    by_cases hu : b ≤ u
    · rw [hleft u hu, zero_mul]
    · rw [hright u (le_of_not_ge hu), mul_zero]
  rw [realWeilForm_eq_source_parts,
    archCross_eq_neg_sourceCollar_of_disjoint f.2.1 f.2.2 g.2.1 g.2.2 hfg,
    sourceGammaCollar_eq_pole_add_tail f.2.1 f.2.2 g.2.1 g.2.2 hleft hright]
  ring

/-- Ordinary square mass after exponential decay in the left boundary distance. -/
def leftBoundaryMass (b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sectionMass (fun u => Real.exp (2 * (u - b)) * f u)

/-- Ordinary square mass after exponential decay in the right boundary distance. -/
def rightBoundaryMass (b : ℝ) (g : ℝ → ℝ) : ℝ :=
  sectionMass (fun u => Real.exp (-2 * (u - b)) * g u)

private theorem sourceCollarCorrelation_boundary_tilt {f g : ℝ → ℝ} {b h : ℝ}
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) (hh : 0 ≤ h) :
    sourceCollarCorrelation (fun u => Real.exp (2 * (u - b)) * f u)
      (fun u => Real.exp (-2 * (u - b)) * g u) h =
      Real.exp (-2 * h) * sourceCollarCorrelation f g h := by
  have hl : ∀ u, b ≤ u → Real.exp (2 * (u - b)) * f u = 0 := by
    intro u hu
    rw [hleft u hu, mul_zero]
  have hr : ∀ u, u ≤ b → Real.exp (-2 * (u - b)) * g u = 0 := by
    intro u hu
    rw [hright u hu, mul_zero]
  rw [sourceCollarCorrelation_ordered hl hr hh,
    sourceCollarCorrelation_ordered hleft hright hh, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  have he : Real.exp (2 * (u - b)) * Real.exp (-2 * (u + h - b)) =
      Real.exp (-2 * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (2 * (u - b)) * Real.exp (-2 * (u + h - b))) * (f u * g (u + h)) := by ring
    _ = _ := by rw [he]

/-- After exact pole cancellation, Gamma charges only mass close to the touching boundary. -/
theorem abs_orderedGammaTail_le_boundaryMass {f g : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    |orderedGammaTail f g| ≤ Real.pi * (leftBoundaryMass b f + rightBoundaryMass b g) := by
  let F : ℝ → ℝ := fun u => Real.exp (2 * (u - b)) * f u
  let G : ℝ → ℝ := fun u => Real.exp (-2 * (u - b)) * g u
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  have hGc : Continuous G := by dsimp only [G]; fun_prop
  have hFs : HasCompactSupport F := hfc.mul_left
  have hGs : HasCompactSupport G := hgc.mul_left
  have hFl : ∀ u, b ≤ u → F u = 0 := by
    intro u hu
    dsimp only [F]
    rw [hleft u hu, mul_zero]
  have hGr : ∀ u, u ≤ b → G u = 0 := by
    intro u hu
    dsimp only [G]
    rw [hright u hu, mul_zero]
  have he : orderedGammaTail f g =
      ∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation F G h := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    dsimp only [F, G]
    rw [sourceCollarCorrelation_boundary_tilt hleft hright hh.le]
    ring
  rw [he]
  exact abs_sourceGammaCollar_le_of_ordered hFc hFs hGc hGs hFl hGr

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integral_exp_neg_half_sourceCollar_of_ordered
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sourceGammaCollar_eq_pole_add_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.realWeilForm_ordered_pole_cancellation
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_orderedGammaTail_le_boundaryMass
