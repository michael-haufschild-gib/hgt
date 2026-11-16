import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadIsAHardyTransform
import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeHeadsAreHardyTransforms

/-!
# Square-integrable vertical traces of the left continuation

After damping beyond the Euler boundary, the archimedean Hankel profile, the
translated prime profiles and both exponential charges lie in the same half-line
Hilbert space. Their exact sum represents the meromorphic continuation by a
Laplace transform. Plancherel gives uniform vertical square bounds on every
closed half-plane strictly left of the zero strip.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

theorem memLp_dampedLevyHeadProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : 0 ≤ c) :
    MemLp (fun s => levyHeadProfile F s*expRay (c : ℂ) s) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have h := memLp_levyHeadProfile hF
  refine h.mono (h.aestronglyMeasurable.mul (continuous_expRay _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [norm_mul,norm_expRay,ofReal_re]
  have he : Real.exp (-(c*s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc (mem_Ioi.mp hs).le))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg _)

/-- The archimedean part of the left continuation's half-line profile. -/
def dampedLevyHeadDatumLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : 0 ≤ c) : Lp ℂ 2 halfLineLaplaceMeasure :=
  (memLp_dampedLevyHeadProfile hF hc).toLp (fun s => levyHeadProfile F s*expRay (c : ℂ) s)

theorem laplaceRay_dampedLevyHeadDatumLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 < z.re) :
    laplaceRay (dampedLevyHeadDatumLp hF hc) z = levyHeadTerm F (-(z+c)) := by
  rw [levyHeadTerm_neg_eq_laplaceRay hF (by simp only [add_re,ofReal_re]; linarith only [hz,hc])]
  unfold laplaceRay
  refine integral_congr_ae ?_
  filter_upwards [(memLp_dampedLevyHeadProfile hF hc).coeFn_toLp] with s hs
  rw [show (dampedLevyHeadDatumLp hF hc : ℝ → ℂ) s = levyHeadProfile F s*expRay (c : ℂ) s from hs]
  simp only [expRay]
  rw [mul_assoc,← Complex.exp_add]
  congr 2
  ring

private def primeHeadHardyDatum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) : Lp ℂ 2 halfLineLaplaceMeasure :=
  primeHeadProfileLp hF hc

/-- The left continuation's profile: archimedean and prime parts minus its two exponential charges. -/
def leftContinuationDatum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c) (W₀ : ℝ) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  (-(1 : ℂ)/(criticalAliasCoefficient W₀ : ℂ)) •
    (dampedLevyHeadDatumLp hF (by linarith only [hc0]) + primeHeadHardyDatum hF hc -
      negativeHalfLineLaplace (cx F) (1/2) •
        halfLineLaplaceFeature ((c+1/2 : ℝ) : ℂ) (by simp only [ofReal_re]; linarith only [hc0]) -
      negativeHalfLineLaplace (cx F) (-(1/2)) •
        halfLineLaplaceFeature ((c-1/2 : ℝ) : ℂ) (by simp only [ofReal_re]; linarith only [hc0]))

/-- Beyond the zero strip, the continuation is the Laplace transform of an explicit `L²` profile. -/
theorem stateMeromorphic_eq_laplaceRay_left {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c)
    {z : ℂ} (hz : 0 < z.re) :
    stateMeromorphic W₀ F (-(z+c)-8) = laplaceRay (leftContinuationDatum hF hc hc0 W₀) z := by
  have hcn : 0 ≤ c := by linarith only [hc0]
  have hp : 0 < ((c+1/2 : ℝ) : ℂ).re := by simp only [ofReal_re]; linarith only [hc0]
  have hm : 0 < ((c-1/2 : ℝ) : ℂ).re := by simp only [ofReal_re]; linarith only [hc0]
  have ha : inner ℂ (halfLineLaplaceFeature z hz) (dampedLevyHeadDatumLp hF hcn) =
      levyHeadTerm F (-(z+c)) := by
    change halfLineLaplaceTransform _ z hz = _
    exact (halfLineLaplaceTransform_eq_laplaceRay _ hz).trans
      (laplaceRay_dampedLevyHeadDatumLp hF hcn hz)
  have hb : inner ℂ (halfLineLaplaceFeature z hz) (primeHeadHardyDatum hF hc) =
      primeHead F (-(z+c)) := by
    change halfLineLaplaceTransform _ z hz = _
    exact (halfLineLaplaceTransform_eq_laplaceRay _ hz).trans
      (laplaceRay_primeHeadProfile hF hc hc0 hz)
  have hplus : inner ℂ (halfLineLaplaceFeature z hz)
      (halfLineLaplaceFeature ((c+1/2 : ℝ) : ℂ) hp) = 1/(z+((c+1/2 : ℝ) : ℂ)) := by
    simpa only [RCLike.star_def,Complex.conj_ofReal] using inner_halfLineLaplaceFeature hz hp
  have hminus : inner ℂ (halfLineLaplaceFeature z hz)
      (halfLineLaplaceFeature ((c-1/2 : ℝ) : ℂ) hm) = 1/(z+((c-1/2 : ℝ) : ℂ)) := by
    simpa only [RCLike.star_def,Complex.conj_ofReal] using inner_halfLineLaplaceFeature hz hm
  have hw : (-(z+c)-8).re < -(17/2) := by
    change -(z.re+c)-8 < -(17/2 : ℝ)
    linarith only [hz,hc0]
  symm
  rw [← halfLineLaplaceTransform_eq_laplaceRay _ hz]
  change inner ℂ (halfLineLaplaceFeature z hz) (leftContinuationDatum hF hc hc0 W₀) = _
  simp only [leftContinuationDatum,inner_smul_right,inner_sub_right,inner_add_right]
  rw [ha,hb,hplus,hminus,stateMeromorphic_eq_left hw,
    show -(z+(c : ℂ))-8+8 = -(z+c) by ring,leftRemainder]
  rw [show (-(z+(c : ℂ)))-1/2 = -(z+((c+1/2 : ℝ) : ℂ)) by push_cast; ring,
    show (-(z+(c : ℂ)))+1/2 = -(z+((c-1/2 : ℝ) : ℂ)) by push_cast; ring,
    div_neg,div_neg]
  simp only [div_eq_mul_inv,one_mul]
  ring

/-- The Hilbert-space representation gives an inverse-square-root bound uniformly in height. -/
theorem norm_stateMeromorphic_left_le {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c)
    {w : ℂ} (hw : w.re < -c-8) :
    ‖stateMeromorphic W₀ F w‖ ≤ rayL2Norm (leftContinuationDatum hF hc hc0 W₀) /
      Real.sqrt (2*(-w.re-c-8)) := by
  let z : ℂ := -w-(c : ℂ)-8
  have hz : 0 < z.re := by
    change 0 < -w.re-c-8
    linarith only [hw]
  have he : -(z+(c : ℂ))-8 = w := by dsimp only [z]; ring
  have h := norm_laplaceRay_le (Lp.memLp (leftContinuationDatum hF hc hc0 W₀)) hz
  rw [← stateMeromorphic_eq_laplaceRay_left hF hc hc0 hz,he] at h
  exact h

/-- The reflected continuation is a Hardy function on every half-plane beyond the Euler boundary. -/
theorem isHalfPlaneHardy_leftContinuation {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c) :
    IsHalfPlaneHardy (fun z => stateMeromorphic W₀ F (-(z+c)-8))
      (∫ s in Ioi (0 : ℝ), ‖(leftContinuationDatum hF hc hc0 W₀ : ℝ → ℂ) s‖^2) := by
  have h := isHalfPlaneHardy_laplaceRay (Lp.memLp (leftContinuationDatum hF hc hc0 W₀))
  have he : EqOn (fun z => stateMeromorphic W₀ F (-(z+c)-8))
      (laplaceRay (leftContinuationDatum hF hc hc0 W₀)) {z : ℂ | 0 < z.re} :=
    fun z hz => stateMeromorphic_eq_laplaceRay_left hF hc hc0 hz
  have heq (σ : ℝ) (hσ : 0 < σ) :
      (fun ξ => stateMeromorphic W₀ F (-(rayLine σ ξ+c)-8)) =
        fun ξ => laplaceRay (leftContinuationDatum hF hc hc0 W₀) (rayLine σ ξ) :=
    funext fun ξ => he (by simpa only [mem_setOf_eq,rayLine_re] using hσ)
  refine ⟨h.holo.congr he, ?_, ?_⟩
  · intro σ hσ
    rw [heq σ hσ]
    exact h.memLp σ hσ
  · intro σ hσ
    simp_rw [congrFun (heq σ hσ)]
    exact h.bound σ hσ

/-- Every closed half-plane strictly left of the zero strip has uniformly bounded vertical `L²` mass. -/
theorem exists_bound_vertical_stateMeromorphic_left {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, x ≤ -(17/2)-δ →
      MemLp (fun ξ => stateMeromorphic W₀ F (rayLine x ξ)) 2 volume ∧
        (∫ ξ : ℝ, ‖stateMeromorphic W₀ F (rayLine x ξ)‖^2) ≤ M := by
  let c : ℝ := 1/2 + min (δ/2) (1/2)
  have hc0 : 1/2 < c := by
    dsimp only [c]
    have hm : 0 < min (δ/2) (1/2 : ℝ) := lt_min (by linarith only [hδ]) (by norm_num)
    linarith only [hm]
  have hc : c ≤ 4 := by
    dsimp only [c]
    linarith only [min_le_right (δ/2) (1/2 : ℝ)]
  have hct : c < 1/2+δ := by
    dsimp only [c]
    linarith only [min_le_left (δ/2) (1/2 : ℝ),hδ]
  have h := isHalfPlaneHardy_leftContinuation (W₀ := W₀) hF hc hc0
  let M : ℝ := ∫ s in Ioi (0 : ℝ), ‖(leftContinuationDatum hF hc hc0 W₀ : ℝ → ℂ) s‖^2
  refine ⟨M,integral_nonneg (fun s => sq_nonneg
    ‖(leftContinuationDatum hF hc hc0 W₀ : ℝ → ℂ) s‖),fun x hx => ?_⟩
  let σ : ℝ := -x-c-8
  have hσ : 0 < σ := by dsimp only [σ]; linarith only [hx,hct]
  have he (ξ : ℝ) : stateMeromorphic W₀ F (-(rayLine σ (-ξ)+c)-8) =
      stateMeromorphic W₀ F (rayLine x ξ) := by
    congr 1
    dsimp only [rayLine,σ]
    push_cast
    ring
  constructor
  · have hm := (h.memLp σ hσ).comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    refine hm.ae_eq (Eventually.of_forall fun ξ => ?_)
    exact he ξ
  · have hi : (∫ ξ : ℝ, ‖stateMeromorphic W₀ F (rayLine x ξ)‖^2) =
        ∫ ξ : ℝ, ‖stateMeromorphic W₀ F (-(rayLine σ ξ+c)-8)‖^2 := by
      calc
        _ = ∫ ξ : ℝ, ‖stateMeromorphic W₀ F (-(rayLine σ (-ξ)+c)-8)‖^2 :=
          integral_congr_ae (Eventually.of_forall fun ξ =>
            congrArg (fun q : ℂ => ‖q‖^2) (he ξ).symm)
        _ = _ := integral_neg_eq_self
          (fun ξ : ℝ => ‖stateMeromorphic W₀ F (-(rayLine σ ξ+c)-8)‖^2) volume
    rw [hi]
    exact h.bound σ hσ

end GaloisForLFunctions.ExclusionOfTheCriticalState
