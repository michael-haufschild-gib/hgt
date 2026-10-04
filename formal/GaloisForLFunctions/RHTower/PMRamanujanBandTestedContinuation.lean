import GaloisForLFunctions.RHTower.PMRamanujanBandResidueTest
import GaloisForLFunctions.RHTower.PMRamanujanBandTestedScale
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Continuation of the complete compactly tested band identity

The complete arithmetic kernel is holomorphic on an explicit ordinate tube.
Compact L2 testing preserves holomorphy, using actual compact domination.
Under the proposed normalized-profile convergence, analytic uniqueness extends
the literal source identity from its initial half-plane to the critical boundary
approach. At a zeta zero its kernel is the full audited residue numerator.
No convergence, spectral escape, or RH-producing energy estimate is asserted.
-/

open MeasureTheory Set Complex Filter Topology Metric
noncomputable section
namespace RHTower

/-- The complete arithmetic side of the cleared moving-band identity. -/
def pmRamanujanBandClearedKernel (ε : ℝ) (z : ℂ) (τ : ℝ) : ℂ :=
  let s := (1/2 : ℂ)+(τ : ℂ)*I
  let r := (ε : ℂ)+s-z
  pmPowerDampedDivisorDensity ε * (riemannZeta s/s) * ((1-(2 : ℂ)^(-r))/r) *
    (riemannZeta (1+z-s)*pmRamanujanBandEulerCorrection ε z s-riemannZeta z)

theorem pmRamanujanBandClearedKernel_at_zero (ε : ℝ) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (τ : ℝ) :
    pmRamanujanBandClearedKernel ε ρ τ = pmRamanujanBandResidueNumerator ε ρ τ := by
  simp only [pmRamanujanBandClearedKernel, pmRamanujanBandResidueNumerator, hρ, sub_zero]
  ring

theorem continuousAt_pmRamanujanBandClearedKernel {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} {τ : ℝ} (hz : 3/8 < z.re) (hz1 : z ≠ 1) (hτ : τ ≠ z.im) :
    ContinuousAt (fun p : ℂ × ℝ => pmRamanujanBandClearedKernel ε p.1 p.2) (z,τ) := by
  let s : ℂ × ℝ → ℂ := fun p => (1/2 : ℂ)+(p.2 : ℂ)*I
  let r : ℂ × ℝ → ℂ := fun p => (ε : ℂ)+s p-p.1
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hs0 : s (z,τ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [s] at hh
  have hs1 : s (z,τ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [s] at hh
  have hr0 : r (z,τ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp [r,s] at hh
    exact hτ (by linarith)
  have hzs1 : 1+z-s (z,τ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [s] at hh
    exact hτ (by linarith)
  have hζs : ContinuousAt (fun p => riemannZeta (s p)) (z,τ) :=
    (differentiableAt_riemannZeta hs1).continuousAt.comp hs.continuousAt
  have hζzs : ContinuousAt (fun p : ℂ × ℝ => riemannZeta (1+p.1-s p)) (z,τ) :=
    (differentiableAt_riemannZeta hzs1).continuousAt.comp
      (f := fun p : ℂ × ℝ => 1+p.1-s p) (by fun_prop)
  have hζz : ContinuousAt (fun p : ℂ × ℝ => riemannZeta p.1) (z,τ) :=
    (differentiableAt_riemannZeta hz1).continuousAt.comp continuous_fst.continuousAt
  have hmem : (z,s (z,τ)) ∈ pmRamanujanBandEulerDomain := by
    exact ⟨hz, by norm_num [s]⟩
  have hcH : ContinuousAt (fun w : ℂ × ℂ => pmRamanujanBandEulerCorrection ε w.1 w.2)
      (z,s (z,τ)) :=
    (continuousOn_pmRamanujanBandEulerCorrection hε).continuousAt
      (isOpen_pmRamanujanBandEulerDomain.mem_nhds hmem)
  have hH : ContinuousAt (fun p : ℂ × ℝ => pmRamanujanBandEulerCorrection ε p.1 (s p)) (z,τ) := by
    exact ContinuousAt.comp (g := fun w : ℂ × ℂ => pmRamanujanBandEulerCorrection ε w.1 w.2)
      (f := fun p : ℂ × ℝ => (p.1,s p)) (x := (z,τ)) hcH
      (continuous_fst.prodMk hs).continuousAt
  have hn : Continuous (fun p => 1-(2 : ℂ)^(-r p)) := by fun_prop
  change ContinuousAt (fun p => pmPowerDampedDivisorDensity ε * (riemannZeta (s p)/s p) *
    ((1-(2 : ℂ)^(-r p))/r p) *
      (riemannZeta (1+p.1-s p)*pmRamanujanBandEulerCorrection ε p.1 (s p)-riemannZeta p.1)) (z,τ)
  exact ((continuousAt_const.mul (hζs.div hs.continuousAt hs0)).mul
    (hn.continuousAt.div hr.continuousAt hr0)).mul ((hζzs.mul hH).sub hζz)

theorem differentiableAt_pmRamanujanBandClearedKernel {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} {τ : ℝ} (hz : 3/8 < z.re) (hz1 : z ≠ 1) (hτ : τ ≠ z.im) :
    DifferentiableAt ℂ (fun w => pmRamanujanBandClearedKernel ε w τ) z := by
  let s := (1/2 : ℂ)+(τ : ℂ)*I
  have hr0 : (ε : ℂ)+s-z ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp [s] at hh
    exact hτ (by linarith)
  have hzs1 : 1+z-s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [s] at hh
    exact hτ (by linarith)
  have hr : Differentiable ℂ (fun w : ℂ => (ε : ℂ)+s-w) := by fun_prop
  have hn : Differentiable ℂ (fun w : ℂ => 1-(2 : ℂ)^(-((ε : ℂ)+s-w))) := by
    exact (differentiable_const (1 : ℂ)).sub (hr.neg.const_cpow (.inl (by norm_num)))
  have hζ : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1+w-s)) z :=
    (differentiableAt_riemannZeta hzs1).comp z (by fun_prop)
  have hH : DifferentiableAt ℂ (fun w => pmRamanujanBandEulerCorrection ε w s) z :=
    (differentiableOn_pmRamanujanBandEulerCorrection hε (by norm_num [s])).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  change DifferentiableAt ℂ (fun w => pmPowerDampedDivisorDensity ε * (riemannZeta s/s) *
    ((1-(2 : ℂ)^(-((ε : ℂ)+s-w)))/((ε : ℂ)+s-w)) *
      (riemannZeta (1+w-s)*pmRamanujanBandEulerCorrection ε w s-riemannZeta w)) z
  exact (hn.differentiableAt.div hr.differentiableAt hr0).const_mul _ |>.mul
    ((hζ.mul hH).sub (differentiableAt_riemannZeta hz1))

def pmRamanujanBandKernelTube (a : ℝ) : Set ℂ :=
  {z | 3/8 < z.re ∧ 0 < z.im ∧ z.im < a}

theorem isOpen_pmRamanujanBandKernelTube (a : ℝ) : IsOpen (pmRamanujanBandKernelTube a) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

private theorem pmbk_tube_facts {a b : ℝ} {z : ℂ} {τ : ℝ}
    (hz : z ∈ pmRamanujanBandKernelTube a) (hτ : τ ∈ Icc a b) :
    3/8 < z.re ∧ z ≠ 1 ∧ τ ≠ z.im := by
  refine ⟨hz.1, ?_, ?_⟩
  · intro he
    have hh := hz.2.1
    simp [he] at hh
  · exact ne_of_gt (hz.2.2.trans_le hτ.1)

theorem differentiableAt_pmRamanujanBandClearedKernel_test {ε : ℝ} (hε : 0 ≤ ε)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {a b : ℝ} {z : ℂ}
    (hz : z ∈ pmRamanujanBandKernelTube a) :
    DifferentiableAt ℂ (fun w => ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
      (Icc a b).indicator (pmRamanujanBandClearedKernel ε w) τ) z := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_pmRamanujanBandKernelTube a).mem_nhds hz)
  let R := r/2
  have hR : 0 < R := half_pos hr
  have hsub : closedBall z R ⊆ pmRamanujanBandKernelTube a :=
    fun w hw => hrsub ((closedBall_subset_ball (half_lt_self hr)) hw)
  have hc : ContinuousOn (fun p : ℂ × ℝ => pmRamanujanBandClearedKernel ε p.1 p.2)
      ((closedBall z R) ×ˢ Icc a b) := by
    intro p hp
    obtain ⟨hp1,hp2,hp3⟩ := pmbk_tube_facts (hsub hp.1) hp.2
    exact (continuousAt_pmRamanujanBandClearedKernel hε hp1 hp2 hp3).continuousWithinAt
  obtain ⟨M,hM⟩ := (isCompact_closedBall z R |>.prod (isCompact_Icc : IsCompact (Icc a b))).exists_bound_of_continuousOn hc
  let F : ℂ → ℝ → ℂ := fun w τ => (starRingEnd ℂ) (h τ) *
    (Icc a b).indicator (pmRamanujanBandClearedKernel ε w) τ
  let g : ℝ → ℝ := (Icc a b).indicator (fun τ => ‖h τ‖*M)
  have hmeas : ∀ w ∈ ball z R, AEStronglyMeasurable (F w) volume := by
    intro w hw
    have hcτ : ContinuousOn (pmRamanujanBandClearedKernel ε w) (Icc a b) := by
      intro τ hτ
      obtain ⟨hw1,hw2,hw3⟩ := pmbk_tube_facts (hsub (ball_subset_closedBall hw)) hτ
      exact ((continuousAt_pmRamanujanBandClearedKernel hε hw1 hw2 hw3).comp
        (f := fun t : ℝ => (w,t)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    exact (Lp.aestronglyMeasurable h).star.mul
      ((aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
        (hcτ.aestronglyMeasurable measurableSet_Icc))
  have hdiff : ∀ τ : ℝ, DifferentiableOn ℂ (fun w => F w τ) (ball z R) := by
    intro τ
    by_cases hτ : τ ∈ Icc a b
    · intro w hw
      obtain ⟨hw1,hw2,hw3⟩ := pmbk_tube_facts (hsub (ball_subset_closedBall hw)) hτ
      simpa only [F, indicator_of_mem hτ] using
        ((differentiableAt_pmRamanujanBandClearedKernel hε hw1 hw2 hw3).const_mul
          ((starRingEnd ℂ) (h τ))).differentiableWithinAt
    · simpa only [F, indicator_of_notMem hτ, mul_zero] using
        (differentiableOn_const (0 : ℂ) : DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) (ball z R))
  have hbound : ∀ τ : ℝ, ∀ w ∈ ball z R, ‖F w τ‖ ≤ g τ := by
    intro τ w hw
    by_cases hτ : τ ∈ Icc a b
    · simp only [F, g, indicator_of_mem hτ, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hM (w,τ) ⟨ball_subset_closedBall hw,hτ⟩) (norm_nonneg _)
    · simp [F,g,hτ]
  have hhi : IntegrableOn (fun τ : ℝ => h τ) (Icc a b) :=
    ((Lp.memLp h).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)).integrableOn_isCompact isCompact_Icc
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hhi.norm.mul_const M)
  exact GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated hR
    hmeas hdiff hbound hg

theorem pmRamanujanBandTestedScale_cleared_continuation_of_bound
    {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hbound : ∀ X ∈ Ici (1 : ℝ), ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ᵐ τ : ℝ, τ ∉ Icc a b → h τ = 0)
    {z : ℂ} (hz : 1/2 < z.re) (hzi : 0 < z.im) (hza : z.im < a) :
    riemannZeta z *
      (∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X) =
      ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
        (Icc a b).indicator (pmRamanujanBandClearedKernel ε z) τ := by
  let U : Set ℂ := {w | 1/2 < w.re ∧ 0 < w.im ∧ w.im < a}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))
  have hUtube : U ⊆ pmRamanujanBandKernelTube a := by
    intro w hw
    exact ⟨by linarith [hw.1],hw.2⟩
  let L : ℂ → ℂ := fun w => riemannZeta w *
    (∫ X in Ici (1 : ℝ), (X : ℂ)^(-w-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X)
  let R : ℂ → ℂ := fun w => ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
    (Icc a b).indicator (pmRamanujanBandClearedKernel ε w) τ
  have hl : AnalyticOnNhd ℂ L U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro w hw
    have hw1 : w ≠ 1 := by intro he; have hh := hw.2.1; simp [he] at hh
    exact ((differentiableAt_riemannZeta hw1).mul
      (differentiableAt_pmRamanujanBandTestedScale_integral_of_bound ε hbound h hw.1)).differentiableWithinAt
  have hr : AnalyticOnNhd ℂ R U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro w hw
    exact (differentiableAt_pmRamanujanBandClearedKernel_test hε.le h (hUtube hw)).differentiableWithinAt
  have hinitial (w : ℂ) (hw : w ∈ U) (hwr : 1 < w.re) : L w = R w := by
    have hnonzero : ∀ᵐ τ : ℝ, h τ ≠ 0 → (ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-w ≠ 0 := by
      filter_upwards [hsupp] with τ hτ
      intro hh he
      have ht : τ ∈ Icc a b := by by_contra hn; exact hh (hτ hn)
      have he' := congrArg Complex.im he
      simp at he'
      linarith [ht.1,hw.2.2]
    rw [show L w = ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
        pmRamanujanBandClearedKernel ε w τ from
      pmRamanujanBandTestedScale_cleared_eq hε h hbound hwr hnonzero]
    apply integral_congr_ae
    filter_upwards [hsupp] with τ hτ
    by_cases ht : τ ∈ Icc a b
    · rw [indicator_of_mem ht]
    · simp [indicator_of_notMem ht,hτ ht]
  let w₀ : ℂ := 2+(a/2 : ℝ)*I
  have hw₀ : w₀ ∈ U := by
    norm_num [w₀,U]
    exact ha
  have hw₀r : 1 < w₀.re := by norm_num [w₀]
  have hev : L =ᶠ[𝓝 w₀] R := by
    filter_upwards [hU.mem_nhds hw₀,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw₀r] with w hw hwr
    exact hinitial w hw hwr
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr
    ((convex_halfSpace_re_gt (1/2)).inter
      ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_lt a))).isPreconnected
    hw₀ hev ⟨hz,hzi,hza⟩

theorem pmRamanujanBandTestedScale_cleared_continuation
    {ε : ℝ} (hε : 0 < ε) {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F))
    (h : Lp ℂ 2 (volume : Measure ℝ)) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ᵐ τ : ℝ, τ ∉ Icc a b → h τ = 0)
    {z : ℂ} (hz : 1/2 < z.re) (hzi : 0 < z.im) (hza : z.im < a) :
    riemannZeta z *
      (∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X) =
      ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
        (Icc a b).indicator (pmRamanujanBandClearedKernel ε z) τ := by
  obtain ⟨C,_hC,hbound⟩ := exists_bound_pmRamanujanMovingBandMellinVector_of_tendsto hε.le hc
  exact pmRamanujanBandTestedScale_cleared_continuation_of_bound hε hbound h ha hsupp hz hzi hza

end RHTower
