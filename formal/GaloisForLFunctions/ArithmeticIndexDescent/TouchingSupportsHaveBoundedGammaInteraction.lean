import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaBoundaryPairing
import GaloisForLFunctions.ArithmeticIndexDescent.SeparatedSupportsRemoveTheGammaSingularity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Gamma payment across touching ordered supports

The literal half-line Hankel operator bounds the Gamma collar without a positive
support gap. The transfer keeps arbitrary signed continuous compact profiles and
the exact normalization of the archimedean source.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped InnerProduct ComplexConjugate
open RHTower Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private theorem zeroExtension_halfLine_of_nonpos (v : SoninL2)
    (hv : ∀ᵐ x : ℝ, x ≤ 0 → v x = 0) :
    suzukiPositiveZeroExtension (soninHalfLine v) = v := by
  apply Lp.ext
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp (coeFn_soninHalfLine v)
  filter_upwards [suzukiPositiveZeroExtension_ae (soninHalfLine v), hh, hv]
    with x he hh hv
  rw [he]
  change (Ioi (0 : ℝ)).indicator (fun t => soninHalfLine v t) x = v x
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    exact hh hx
  · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    exact (hv (le_of_not_gt hx)).symm

private theorem reflect_zeroExtension_halfLine (u : SoninL2)
    (hu : ∀ᵐ x : ℝ, 0 ≤ x → u x = 0) :
    l2Reflection (suzukiPositiveZeroExtension (soninHalfLine (l2Reflection u))) = u := by
  have hr : ∀ᵐ x : ℝ, x ≤ 0 → l2Reflection u x = 0 := by
    have hs :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae.eventually hu
    filter_upwards [l2Reflection_ae u, hs] with x hx hs
    intro hneg
    rw [hx]
    exact hs (by linarith only [hneg])
  rw [zeroExtension_halfLine_of_nonpos (l2Reflection u) hr, l2Reflection_involutive]

/-- The actual mixed translation integral is bounded across a sharp ordered boundary. -/
theorem norm_gammaBoundaryPair_le (u v : SoninL2)
    (hu : ∀ᵐ x : ℝ, 0 ≤ x → u x = 0)
    (hv : ∀ᵐ x : ℝ, x ≤ 0 → v x = 0) :
    IntegrableOn (fun h : ℝ => (ccmGammaTranslationDensity h : ℂ) *
      inner ℂ (logTranslationCLM h v) u) (Ioi 0) ∧
    ‖∫ h in Ioi (0 : ℝ), (ccmGammaTranslationDensity h : ℂ) *
      inner ℂ (logTranslationCLM h v) u‖ ≤
        Real.pi * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  let F := soninHalfLine (l2Reflection u)
  let G := soninHalfLine v
  have hu' : l2Reflection (suzukiPositiveZeroExtension F) = u :=
    reflect_zeroExtension_halfLine u hu
  have hv' : suzukiPositiveZeroExtension G = v :=
    zeroExtension_halfLine_of_nonpos v hv
  have hFn : ‖F‖ = ‖u‖ := by
    calc
      ‖F‖ = ‖suzukiPositiveZeroExtension F‖ := (norm_suzukiPositiveZeroExtension F).symm
      _ = ‖l2Reflection (suzukiPositiveZeroExtension F)‖ :=
        (l2ReflectionIsometry.norm_map _).symm
      _ = ‖u‖ := congrArg norm hu'
  have hGn : ‖G‖ = ‖v‖ := by rw [← norm_suzukiPositiveZeroExtension, hv']
  have hi := integrableOn_ccmGamma_oppositeHalfLines F G
  rw [hu', hv'] at hi
  refine ⟨hi, ?_⟩
  have he := integral_ccmGamma_oppositeHalfLines F G
  rw [hu', hv'] at he
  rw [he]
  calc
    ‖inner ℂ G (ccmGammaBoundaryCLM F)‖ ≤ ‖G‖ * ‖ccmGammaBoundaryCLM F‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖G‖ * ((2 * Real.pi) * ‖F‖) :=
      mul_le_mul_of_nonneg_left
        ((ccmGammaBoundaryCLM.le_opNorm F).trans
          (mul_le_mul_of_nonneg_right norm_ccmGammaBoundaryCLM_le (norm_nonneg F)))
        (norm_nonneg G)
    _ ≤ Real.pi * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      rw [hFn, hGn]
      nlinarith only [mul_nonneg Real.pi_pos.le (sq_nonneg (‖u‖ - ‖v‖))]

/-- A literal real compact profile in the existing complex Lebesgue L² carrier. -/
def realProfileL2 (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) : SoninL2 :=
  ((Complex.continuous_ofReal.comp hf).memLp_of_hasCompactSupport
    (cx_hasCompactSupport hc) : MemLp (cx f) 2 volume).toLp _

theorem realProfileL2_ae (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (realProfileL2 f hf hc : ℝ → ℂ) =ᵐ[volume] cx f :=
  MemLp.coeFn_toLp _

theorem norm_realProfileL2_sq (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ‖realProfileL2 f hf hc‖ ^ 2 = sectionMass f := by
  rw [realProfileL2, norm_sq_toLp_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [] with x
  change ‖(f x : ℂ)‖ ^ 2 = f x ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem inner_translate_realProfile (f g : ℝ → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (h : ℝ) :
    inner ℂ (logTranslationCLM h (realProfileL2 g hg hgc)) (realProfileL2 f hf hfc) =
      ((∫ u : ℝ, f u * g (u + h) : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  have ht := (realProfileL2_ae g hg hgc).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htranslate : (logTranslationCLM h (realProfileL2 g hg hgc) : ℝ → ℂ) =ᵐ[volume]
      fun u => realProfileL2 g hg hgc (u + h) :=
    Lp.coeFn_compMeasurePreserving (realProfileL2 g hg hgc)
      (MellinL2.realTranslation_measurePreserving h)
  apply integral_congr_ae
  filter_upwards [htranslate, realProfileL2_ae f hf hfc, ht] with u hu hf hg
  rw [hu, hf]
  change realProfileL2 g _ _ (u + h) = (g (u + h) : ℂ) at hg
  rw [hg, RCLike.inner_apply, Complex.conj_ofReal]
  change (f u : ℂ) * (g (u + h) : ℂ) = ((f u * g (u + h) : ℝ) : ℂ)
  exact (Complex.ofReal_mul _ _).symm

/-- One orientation vanishes even when the two closed supports meet. -/
theorem sourceCollarCorrelation_ordered {f g : ℝ → ℝ} {b h : ℝ}
    (hf : ∀ u, b ≤ u → f u = 0) (hg : ∀ u, u ≤ b → g u = 0) (hh : 0 ≤ h) :
    sourceCollarCorrelation f g h = ∫ u, f u * g (u + h) := by
  apply integral_congr_ae
  filter_upwards [] with u
  have hz : f (u + h) * g u = 0 := by
    by_cases hu : u ≤ b
    · rw [hg u hu, mul_zero]
    · rw [hf (u + h) (by linarith only [le_of_not_ge hu, hh]), zero_mul]
  rw [hz, add_zero]

/-- The sharp Gamma boundary pays arbitrary real profiles by their ordinary square masses. -/
theorem abs_sourceGammaCollar_le_of_ordered_zero {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, 0 ≤ u → f u = 0) (hright : ∀ u, u ≤ 0 → g u = 0) :
    |∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation f g h| ≤
      Real.pi * (sectionMass f + sectionMass g) := by
  have hfl : ∀ᵐ u : ℝ, 0 ≤ u → realProfileL2 f hf hfc u = 0 := by
    filter_upwards [realProfileL2_ae f hf hfc] with u hu
    intro hpos
    rw [hu]
    change (f u : ℂ) = 0
    rw [hleft u hpos, Complex.ofReal_zero]
  have hgr : ∀ᵐ u : ℝ, u ≤ 0 → realProfileL2 g hg hgc u = 0 := by
    filter_upwards [realProfileL2_ae g hg hgc] with u hu
    intro hneg
    rw [hu]
    change (g u : ℂ) = 0
    rw [hright u hneg, Complex.ofReal_zero]
  have hb := (norm_gammaBoundaryPair_le (realProfileL2 f hf hfc)
    (realProfileL2 g hg hgc) hfl hgr).2
  have he : (∫ h in Ioi (0 : ℝ), (ccmGammaTranslationDensity h : ℂ) *
      inner ℂ (logTranslationCLM h (realProfileL2 g hg hgc)) (realProfileL2 f hf hfc)) =
      ((∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation f g h : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    dsimp only
    rw [inner_translate_realProfile, sourceCollarCorrelation_ordered hleft hright hh.le,
      ← Complex.ofReal_mul]
    congr 2
    simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul]
  rw [he, Complex.norm_real, Real.norm_eq_abs, norm_realProfileL2_sq,
    norm_realProfileL2_sq] at hb
  exact hb

/-- Translating both profiles leaves the literal collar unchanged. -/
theorem sourceCollarCorrelation_translate (f g : ℝ → ℝ) (b h : ℝ) :
    sourceCollarCorrelation (fun u => f (u + b)) (fun u => g (u + b)) h =
      sourceCollarCorrelation f g h := by
  unfold sourceCollarCorrelation
  have he := integral_add_right_eq_self (μ := volume)
    (fun u => f u * g (u + h) + f (u + h) * g u) b
  convert he using 1
  congr 1
  ext u
  simp only [add_right_comm u h b]

/-- The Gamma mass bound is uniform over every touching boundary and all support widths. -/
theorem abs_sourceGammaCollar_le_of_ordered {f g : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    |∫ h in Ioi (0 : ℝ), archLevyDensity h * sourceCollarCorrelation f g h| ≤
      Real.pi * (sectionMass f + sectionMass g) := by
  have hb := abs_sourceGammaCollar_le_of_ordered_zero
    (hf.comp (continuous_add_const b)) (hfc.comp_homeomorph (Homeomorph.addRight b))
    (hg.comp (continuous_add_const b)) (hgc.comp_homeomorph (Homeomorph.addRight b))
    (fun u hu => hleft (u + b) (by linarith only [hu]))
    (fun u hu => hright (u + b) (by linarith only [hu]))
  change |∫ h in Ioi (0 : ℝ), archLevyDensity h *
    sourceCollarCorrelation (fun u => f (u + b)) (fun u => g (u + b)) h| ≤
      Real.pi * (sectionMass (fun u => f (u + b)) + sectionMass (fun u => g (u + b))) at hb
  simp_rw [sourceCollarCorrelation_translate] at hb
  have hmf : sectionMass (fun u => f (u + b)) = sectionMass f :=
    integral_add_right_eq_self (fun u => f u ^ 2) b
  have hmg : sectionMass (fun u => g (u + b)) = sectionMass g :=
    integral_add_right_eq_self (fun u => g u ^ 2) b
  rw [hmf, hmg] at hb
  exact hb

/-- The C² spectral cross term is the negative literal collar on disjoint supports. -/
theorem archCross_eq_neg_sourceCollar_of_disjoint {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hfg : ∀ u, f u * g u = 0) :
    (1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r =
      -∫ x in Ioi (0 : ℝ), archLevyDensity x * sourceCollarCorrelation f g x := by
  let p : ℝ → ℝ := fun u => f u + g u
  let m : ℝ → ℝ := fun u => f u - g u
  have hp : ContDiff ℝ 2 p := hf.add hg
  have hm : ContDiff ℝ 2 m := hf.sub hg
  have hpc : HasCompactSupport p := hfc.add hgc
  have hmc : HasCompactSupport m := hfc.sub hgc
  have ip := integrable_normSq_paperFT_mul_gammaBracket hp hpc
  have im := integrable_normSq_paperFT_mul_gammaBracket hm hmc
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
  have hspec : archForm p - archForm m =
      4 * ((1 / (2 * Real.pi)) * ∫ r : ℝ,
        (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r) := by
    unfold archForm
    rw [← mul_sub, ← integral_sub ip im]
    have hi : (∫ r : ℝ, ‖paperFT (cx p) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (cx m) r‖ ^ 2 * EF.gammaBracket r) =
        4 * ∫ r : ℝ, (paperFT (cx f) r * conj (paperFT (cx g) r)).re *
          EF.gammaBracket r := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hpol)
    change (1 / (2 * Real.pi)) * (∫ r : ℝ,
      ‖paperFT (cx p) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (cx m) r‖ ^ 2 * EF.gammaBracket r) = _
    rw [hi]
    ring
  have hmass : (∫ u, p u ^ 2) = ∫ u, m u ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [p, m]
    nlinarith only [hfg u]
  have ishift (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) (x : ℝ) :
      Integrable fun u => (φ u - φ (u + x)) ^ 2 := by
    have hcs : HasCompactSupport (fun u => φ u - φ (u + x)) :=
      hs.sub (hs.comp_homeomorph (Homeomorph.addRight x))
    have hc' : Continuous (fun u => φ u - φ (u + x)) :=
      hc.sub (hc.comp (continuous_add_const x))
    have hcs2 : HasCompactSupport (fun u => (φ u - φ (u + x)) ^ 2) :=
      HasCompactSupport.comp_left (f := fun u => φ u - φ (u + x))
        (g := fun t : ℝ => t ^ 2) hcs (by norm_num)
    have hc2 : Continuous (fun u => (φ u - φ (u + x)) ^ 2) := hc'.pow 2
    exact hc2.integrable_of_hasCompactSupport hcs2
  have hshift (x : ℝ) :
      (∫ u, (p u - p (u + x)) ^ 2) - ∫ u, (m u - m (u + x)) ^ 2 =
      -4 * sourceCollarCorrelation f g x := by
    rw [← integral_sub (ishift p hp.continuous hpc x) (ishift m hm.continuous hmc x),
      sourceCollarCorrelation, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [p, m]
    linear_combination 4 * hfg u + 4 * hfg (u + x)
  have hlev : levyEnergy p - levyEnergy m =
      -4 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * sourceCollarCorrelation f g x := by
    rw [levyEnergy, levyEnergy, ← integral_sub
      (integrableOn_levyIntegrand hp hpc) (integrableOn_levyIntegrand hm hmc),
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [← mul_sub, hshift]
    ring
  have he : archForm p - archForm m = levyEnergy p - levyEnergy m := by
    rw [archForm_eq_levyEnergy hp hpc, archForm_eq_levyEnergy hm hmc, hmass]
    ring
  rw [hspec, hlev] at he
  linarith only [he]

/-- The complete spectral Gamma term obeys a gap-independent sharp-boundary mass bound. -/
theorem abs_archCross_le_of_ordered {f g : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    |(1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r| ≤
      Real.pi * (sectionMass f + sectionMass g) := by
  have hfg (u : ℝ) : f u * g u = 0 := by
    by_cases hu : b ≤ u
    · rw [hleft u hu, zero_mul]
    · rw [hright u (le_of_not_ge hu), mul_zero]
  rw [archCross_eq_neg_sourceCollar_of_disjoint hf hfc hg hgc hfg, abs_neg]
  exact abs_sourceGammaCollar_le_of_ordered hf.continuous hfc hg.continuous hgc hleft hright

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_gammaBoundaryPair_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_sourceGammaCollar_le_of_ordered
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.archCross_eq_neg_sourceCollar_of_disjoint
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_archCross_le_of_ordered
