import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSectionSpace
import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding
import GaloisForLFunctions.RHTower.CHMDMasslessContinuationPieces

/-!
# The mixed Gamma cost across a support gap

For signed real tests separated by a positive distance, the mixed Gamma term
has no singular near-diagonal contribution. Its exact collar formula and the
correlation mass bound give a uniform square-mass estimate over all profiles.
The constant is the integrable tail of the actual archimedean Lévy density.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate
open Zeta23 RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private theorem compact_square {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport fun u => f u ^ 2 := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  filter_upwards [hf] with u hu
  simp only [hu, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]

private theorem sourceGammaSquare_integrable {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r := by
  have hFc := (cx_contDiff hf).continuous
  have hFs := cx_hasCompactSupport hfc
  have hk (r : ℝ) : paperFT (EF.weilTest (cx f) (cx f)) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    rw [EF.paperFT_weilTest hFc hFc hFs hFs, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  refine (LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    (cx_contDiff hf) hFs (cx_contDiff hf) hFs).re.congr (Eventually.of_forall fun r => ?_)
  change (paperFT (EF.weilTest (cx f) (cx f)) r * (EF.gammaBracket r : ℂ)).re = _
  rw [hk, Complex.ofReal_re]

/-- Polarization of the scalar Lévy identity, retaining absolute integrability. -/
private theorem sourceArchCross_jump {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x))) (Ioi 0) ∧
    (1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r =
      EF.gammaBracket 0 * (∫ u, f u * g u) +
        ∫ x in Ioi (0 : ℝ), archLevyDensity x *
          ∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x)) := by
  let p : ℝ → ℝ := fun u => f u + g u
  let m : ℝ → ℝ := fun u => f u - g u
  have hp : ContDiff ℝ 2 p := hf.add hg
  have hm : ContDiff ℝ 2 m := hf.sub hg
  have hpc : HasCompactSupport p := hfc.add hgc
  have hmc : HasCompactSupport m := hfc.sub hgc
  have ip := sourceGammaSquare_integrable hp hpc
  have im := sourceGammaSquare_integrable hm hmc
  have hpol (r : ℝ) : ‖paperFT (cx p) r‖ ^ 2 * EF.gammaBracket r -
      ‖paperFT (cx m) r‖ ^ 2 * EF.gammaBracket r =
      4 * ((paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r) := by
    obtain ⟨hP, hM⟩ := paperFT_ofReal_add_and_sub
      (hf.continuous.integrable_of_hasCompactSupport hfc)
      (hg.continuous.integrable_of_hasCompactSupport hgc) r
    obtain ⟨hnP, hnM⟩ := norm_add_and_sub_sq_eq
      (paperFT (fun u => (f u : ℂ)) r) (paperFT (fun u => (g u : ℂ)) r)
    change ‖paperFT (fun u => ((f u + g u : ℝ) : ℂ)) r‖ ^ 2 * _ -
      ‖paperFT (fun u => ((f u - g u : ℝ) : ℂ)) r‖ ^ 2 * _ = _
    rw [hP, hM]
    change ‖paperFT (fun u => (f u : ℂ)) r + paperFT (fun u => (g u : ℂ)) r‖ ^ 2 *
      EF.gammaBracket r -
      ‖paperFT (fun u => (f u : ℂ)) r - paperFT (fun u => (g u : ℂ)) r‖ ^ 2 *
      EF.gammaBracket r =
      4 * ((paperFT (fun u => (f u : ℂ)) r *
        conj (paperFT (fun u => (g u : ℂ)) r)).re * EF.gammaBracket r)
    rw [hnP, hnM]
    ring
  obtain ⟨iP, eP⟩ := integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hp.continuous
    (hp.continuous.integrable_of_hasCompactSupport hpc)
    ((hp.continuous.pow 2).integrable_of_hasCompactSupport (compact_square hpc)) ip
  obtain ⟨iM, eM⟩ := integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hm.continuous
    (hm.continuous.integrable_of_hasCompactSupport hmc)
    ((hm.continuous.pow 2).integrable_of_hasCompactSupport (compact_square hmc)) im
  have ishift (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) (x : ℝ) :
      Integrable fun u => (φ u - φ (u + x)) ^ 2 :=
    ((hc.sub (hc.comp (continuous_id.add continuous_const))).pow 2).integrable_of_hasCompactSupport
      (compact_square (hs.sub (hs.comp_homeomorph (Homeomorph.addRight x))))
  have hshift (x : ℝ) :
      (∫ u, (f u - f (u + x)) * (g u - g (u + x))) =
      (1 / 4 : ℝ) * ((∫ u, (p u - p (u + x)) ^ 2) -
        ∫ u, (m u - m (u + x)) ^ 2) := by
    rw [← integral_sub (ishift p hp.continuous hpc x) (ishift m hm.continuous hmc x),
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [p, m]
    ring
  have ic : IntegrableOn (fun x => archLevyDensity x *
      ∫ u, (f u - f (u + x)) * (g u - g (u + x))) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((iP.sub iM).const_mul (1 / 4 : ℝ))
      (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [hshift]
    ring
  refine ⟨ic, ?_⟩
  have hmass : (∫ u, p u ^ 2) - ∫ u, m u ^ 2 = 4 * ∫ u, f u * g u := by
    have ip2 : Integrable (fun u => p u ^ 2) :=
      (hp.continuous.pow 2).integrable_of_hasCompactSupport (compact_square hpc)
    have im2 : Integrable (fun u => m u ^ 2) :=
      (hm.continuous.pow 2).integrable_of_hasCompactSupport (compact_square hmc)
    rw [← integral_sub ip2 im2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [p, m]
    ring
  have hlev :
      (∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, (p u - p (u + x)) ^ 2) -
      (∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, (m u - m (u + x)) ^ 2) =
      4 * ∫ x in Ioi (0 : ℝ), archLevyDensity x *
        ∫ u, (f u - f (u + x)) * (g u - g (u + x)) := by
    rw [← integral_sub iP iM, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [hshift]
    ring
  have hspec : (1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r =
      (1 / 4) * ((1 / (2 * Real.pi)) *
        (∫ r : ℝ, ‖paperFT (cx p) r‖ ^ 2 * EF.gammaBracket r) -
        (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT (cx m) r‖ ^ 2 * EF.gammaBracket r) := by
    rw [← mul_sub, ← integral_sub ip im]
    have hi : (∫ r : ℝ, ‖paperFT (cx p) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (cx m) r‖ ^ 2 * EF.gammaBracket r) =
        4 * ∫ r : ℝ, (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hpol)
    rw [hi]
    ring
  rw [hspec]
  change (1 / 4) * ((1 / (2 * Real.pi)) *
    (∫ r : ℝ, ‖paperFT (fun u => (p u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
    (1 / (2 * Real.pi)) *
    (∫ r : ℝ, ‖paperFT (fun u => (m u : ℂ)) r‖ ^ 2 * EF.gammaBracket r)) = _
  rw [eP, eM]
  linear_combination (1 / 4 : ℝ) * EF.gammaBracket 0 * hmass + (1 / 4 : ℝ) * hlev

private theorem sourceArchCross_disjoint {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hfg : ∀ u, f u * g u = 0) :
    (1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r =
      -∫ x in Ioi (0 : ℝ), archLevyDensity x *
        ∫ u, f u * g (u + x) + f (u + x) * g u := by
  rw [(sourceArchCross_jump hf hfc hg hgc).2,
    show (∫ u, f u * g u) = 0 by simp only [hfg, integral_zero],
    mul_zero, zero_add, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [← mul_neg, ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  linear_combination hfg u + hfg (u + x)

/-- The two oriented mixed correlations in the archimedean source. -/
def sourceCollarCorrelation (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u, f u * g (u + x) + f (u + x) * g u

theorem sourceCollarCorrelation_eq (f g : ℝ → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ) :
    sourceCollarCorrelation f g x = sectionCorr f g x + sectionCorr g f x := by
  have h1 : Integrable (fun u => f u * g (u + x)) := by
    simpa only [sub_zero] using integrable_section_product hf hfc hg 0 x
  have h2 : Integrable (fun u => f (u + x) * g u) := by
    simpa only [sub_zero, mul_comm] using integrable_section_product hg hgc hf 0 x
  rw [sourceCollarCorrelation, integral_add h1 h2]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)

/-- The bound is independent of the support widths and of profile derivatives. -/
theorem abs_sourceCollarCorrelation_le (f g : ℝ → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ) :
    |sourceCollarCorrelation f g x| ≤ sectionMass f + sectionMass g := by
  rw [sourceCollarCorrelation_eq f g hf hfc hg hgc x]
  have h1 := abs_sectionCorr_le hf hfc hg hgc x
  have h2 := abs_sectionCorr_le hg hgc hf hfc x
  have ht := abs_add_le (sectionCorr f g x) (sectionCorr g f x)
  linarith only [h1, h2, ht]

/-- A geometric support gap kills every shorter mixed jump. -/
theorem sourceCollarCorrelation_eq_zero_of_gap {f g : ℝ → ℝ} {d x : ℝ}
    (hgap : ∀ u v, f u ≠ 0 → g v ≠ 0 → d < |u - v|)
    (hx : |x| ≤ d) : sourceCollarCorrelation f g x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  have h1 : f u * g (u + x) = 0 := by
    by_cases hf : f u = 0
    · rw [hf, zero_mul]
    · by_cases hg : g (u + x) = 0
      · rw [hg, mul_zero]
      · have hh := hgap u (u + x) hf hg
        rw [show u - (u + x) = -x by ring, abs_neg] at hh
        exact (not_lt_of_ge hx hh).elim
  have h2 : f (u + x) * g u = 0 := by
    by_cases hf : f (u + x) = 0
    · rw [hf, zero_mul]
    · by_cases hg : g u = 0
      · rw [hg, mul_zero]
      · have hh := hgap (u + x) u hf hg
        rw [show u + x - u = x by ring] at hh
        exact (not_lt_of_ge hx hh).elim
  simp only [h1, h2, add_zero, Pi.zero_apply]

theorem integrableOn_sourceCollar_of_disjoint {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hfg : ∀ u, f u * g u = 0) :
    IntegrableOn (fun x => archLevyDensity x * sourceCollarCorrelation f g x) (Ioi 0) := by
  have hi := (sourceArchCross_jump hf hfc hg hgc).1.neg
  refine hi.congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [Pi.neg_apply, ← mul_neg, ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  change -((f u - f (u + x)) * (g u - g (u + x))) =
    f u * g (u + x) + f (u + x) * g u
  linear_combination -(hfg u) - (hfg (u + x))

/-- The exact collar across a gap is paid by the tail of the Lévy density. -/
theorem abs_sourceGammaCollar_le_of_gap {f g : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgap : ∀ u v, f u ≠ 0 → g v ≠ 0 → d < |u - v|) :
    |∫ x in Ioi (0 : ℝ), archLevyDensity x * sourceCollarCorrelation f g x| ≤
      (∫ x in Ioi d, archLevyDensity x) * (sectionMass f + sectionMass g) := by
  have hfg (u : ℝ) : f u * g u = 0 := by
    by_cases hf0 : f u = 0
    · rw [hf0, zero_mul]
    · by_cases hg0 : g u = 0
      · rw [hg0, mul_zero]
      · have hh := hgap u u hf0 hg0
        simp only [sub_self, abs_zero] at hh
        exact (not_lt_of_ge hd.le hh).elim
  have hsub : Ioi d ⊆ Ioi (0 : ℝ) := fun _ hx => hd.trans hx
  have hi := (integrableOn_sourceCollar_of_disjoint hf hfc hg hgc hfg).mono_set hsub
  have htail := CHMDLightCone.integrableOn_archLevyDensity_Ioi hd
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    (fun x hx => by
      rw [sourceCollarCorrelation_eq_zero_of_gap hgap
        (by rw [abs_of_pos hx.1]; exact le_of_not_gt hx.2), mul_zero])]
  calc
    |∫ x in Ioi d, archLevyDensity x * sourceCollarCorrelation f g x| ≤
        ∫ x in Ioi d, |archLevyDensity x * sourceCollarCorrelation f g x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioi d, archLevyDensity x * (sectionMass f + sectionMass g) := by
      apply integral_mono_ae hi.abs (htail.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [abs_mul, abs_of_pos (archLevyDensity_pos (hd.trans hx))]
      exact mul_le_mul_of_nonneg_left
        (abs_sourceCollarCorrelation_le f g hf.continuous hfc hg.continuous hgc x)
        (archLevyDensity_pos (hd.trans hx)).le
    _ = _ := integral_mul_const _ _

/-- The full spectral Gamma cross term obeys the same source estimate. -/
theorem abs_archCross_le_of_gap {f g : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgap : ∀ u v, f u ≠ 0 → g v ≠ 0 → d < |u - v|) :
    |(1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r| ≤
      (∫ x in Ioi d, archLevyDensity x) * (sectionMass f + sectionMass g) := by
  have hfg (u : ℝ) : f u * g u = 0 := by
    by_cases hf0 : f u = 0
    · rw [hf0, zero_mul]
    · by_cases hg0 : g u = 0
      · rw [hg0, mul_zero]
      · have hh := hgap u u hf0 hg0
        simp only [sub_self, abs_zero] at hh
        exact (not_lt_of_ge hd.le hh).elim
  rw [sourceArchCross_disjoint hf hfc hg hgc hfg, abs_neg]
  exact abs_sourceGammaCollar_le_of_gap hd hf hfc hg hgc hgap

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_sourceGammaCollar_le_of_gap
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_archCross_le_of_gap
