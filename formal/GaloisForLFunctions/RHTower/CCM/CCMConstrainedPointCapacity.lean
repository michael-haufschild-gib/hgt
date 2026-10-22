import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPointCapacity
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation

/-!
# Zero point capacity on the smooth, exactly pole-constrained Gamma domain

Every interior point admits smooth sources with value one, both exact pole moments zero,
and arbitrarily small actual archimedean form norm.  In particular no bounded point-sampling
feature can be controlled by this norm.  This does not rule out nonlocal arithmetic Gram maps.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

private theorem exists_center_source_small (a : SuzukiPositiveAperture)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧ g 0 = 1 ∧ ‖g.toCCMFormVector‖ < ε := by
  let g (n : ℕ) := polarCorrectedSource
    ((polarCenterBump a).shrink (n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n)))
  have hz : IsPolarConstrained a (0 : CCMArchimedeanFormDomain a) := by
    simp [IsPolarConstrained]
  have hnorm (n : ℕ) : ‖(g n).toCCMFormVector‖ ≤
      (1 + polarCorrectionConstant a) *
        ‖((polarCenterBump a).shrink (n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))).toCCMFormVector‖ := by
    simpa only [sub_zero] using norm_polarCorrectedSource_sub_le
      ((polarCenterBump a).shrink (n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))) 0 hz
  have ht : Tendsto (fun n => ‖(g n).toCCMFormVector‖) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) hnorm
    simpa only [mul_zero] using (tendsto_ccmSmoothShrink_norm (polarCenterBump a)).const_mul
      (1 + polarCorrectionConstant a)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨g n, isPolarConstrained_polarCorrectedSource _, ?_, hn⟩
  simp [g, polarCorrectedSource, CCMComplexSmoothInteriorSource.combo_apply,
    polarCenterBump_zero, polarRightBump_zero, polarLeftBump_zero]

/-- Smooth physical translation, in the convention `g(x+h)`. -/
def CCMComplexSmoothInteriorSource.translate {a b : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (h : ℝ) (hab : a.1 + |h| ≤ b.1) :
    CCMComplexSmoothInteriorSource b where
  toFun := fun x => g (x + h)
  smooth := g.smooth.comp (contDiff_id.add contDiff_const)
  hasCompactSupport := g.hasCompactSupport.comp_homeomorph (Homeomorph.addRight h)
  tsupport_subset := by
    intro x hx
    have hx' := g.tsupport_subset
      (tsupport_comp_subset_preimage (g : ℝ → ℂ)
        (continuous_id.add continuous_const) hx)
    change -a.1 < x + h ∧ x + h < a.1 at hx'
    constructor <;> linarith [hx'.1, hx'.2, le_abs_self h, neg_abs_le h]

@[simp] theorem CCMComplexSmoothInteriorSource.translate_apply
    {a b : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a)
    (h : ℝ) (hab : a.1 + |h| ≤ b.1) (x : ℝ) :
    g.translate h hab x = g (x + h) := rfl

theorem CCMComplexSmoothInteriorSource.translate_toCCMFormVector
    {a b : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a)
    (h : ℝ) (hab : a.1 + |h| ≤ b.1) :
    (g.translate h hab).toCCMFormVector =
      ccmArchimedeanFormTranslate h hab g.toCCMFormVector := by
  apply ccmArchimedeanFormEmbedding_injective b
  change (ccmArchimedeanFormToAperture b (g.translate h hab).toCCMFormVector : SoninL2) =
    (ccmArchimedeanFormToAperture b
      (ccmArchimedeanFormTranslate h hab g.toCCMFormVector) : SoninL2)
  rw [ccmArchimedeanFormTranslate_physical]
  let f : SoninL2 := ccmArchimedeanFormToAperture a g.toCCMFormVector
  have htrans : (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + h) :=
    (Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving h)).trans
        (Eventually.of_forall fun _ => rfl)
  have hg := g.toCCMFormVector_physical_coeFn.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [(g.translate h hab).toCCMFormVector_physical_coeFn, htrans, hg]
    with x hx ht hgx
  change ((ccmArchimedeanFormToAperture b
    (g.translate h hab).toCCMFormVector : SoninL2) : ℝ → ℂ) x = logTranslationCLM h f x
  rw [hx, ht]
  exact hgx.symm

/-- The small constrained source can be confined to any prescribed neighbourhood of the point. -/
theorem exists_ccmPolarConstrained_point_one_local_norm_lt
    (a : SuzukiPositiveAperture) (x : ℝ) (hx : |x| < a.1)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧ g x = 1 ∧ ‖g.toCCMFormVector‖ < ε ∧
        ∀ y : ℝ, r ≤ |y - x| → g y = 0 := by
  let b : SuzukiPositiveAperture :=
    ⟨min ((a.1 - |x|) / 2) (r / 2), lt_min (by linarith) (by linarith)⟩
  have hfit : b.1 + |-x| ≤ a.1 := by
    dsimp [b]
    rw [abs_neg]
    linarith [min_le_left ((a.1 - |x|) / 2) (r / 2)]
  obtain ⟨g, hg, hg0, hgn⟩ := exists_center_source_small b ε hε
  refine ⟨g.translate (-x) hfit, ?_, ?_, ?_, ?_⟩
  · rw [CCMComplexSmoothInteriorSource.translate_toCCMFormVector]
    exact hg.translate (-x) hfit
  · simpa only [CCMComplexSmoothInteriorSource.translate_apply, add_neg_cancel] using hg0
  · simpa only [CCMComplexSmoothInteriorSource.translate_toCCMFormVector,
      norm_ccmArchimedeanFormTranslate] using hgn
  · intro y hy
    change g (y + -x) = 0
    by_contra hne
    have hs := g.support_subset hne
    have habs : |y - x| < b.1 := by
      rw [abs_lt]
      simpa only [Set.mem_Ioo, sub_eq_add_neg] using hs
    have hb : b.1 ≤ r / 2 := min_le_right _ _
    linarith

/-- Every strict-interior point has zero capacity even after both exact pole constraints. -/
theorem exists_ccmPolarConstrained_point_one_norm_lt
    (a : SuzukiPositiveAperture) (x : ℝ) (hx : |x| < a.1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧ g x = 1 ∧ ‖g.toCCMFormVector‖ < ε := by
  obtain ⟨g, hg, hx, hn, _⟩ := exists_ccmPolarConstrained_point_one_local_norm_lt
    a x hx 1 zero_lt_one ε hε
  exact ⟨g, hg, hx, hn⟩

/-- No finite constant bounds even one interior point sample in the exact constrained form norm. -/
theorem not_ccmPolarConstrained_point_evaluation_bounded
    (a : SuzukiPositiveAperture) (x : ℝ) (hx : |x| < a.1) :
    ¬ ∃ C : ℝ, ∀ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector → ‖g x‖ ≤ C * ‖g.toCCMFormVector‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨g, hg, hgx, hgn⟩ := exists_ccmPolarConstrained_point_one_norm_lt
    a x hx (1 / (|C| + 1)) (by positivity)
  have hval := hC g hg
  rw [hgx, norm_one] at hval
  have hsmall := (lt_div_iff₀ (show 0 < |C| + 1 by positivity)).mp hgn
  have hle := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg g.toCCMFormVector)
  nlinarith [norm_nonneg g.toCCMFormVector]

/-- The complete signed source quadratic can also be arbitrarily small while the sample is one.
All prime, Gamma and polar cross terms are included through continuity of the actual quadratic. -/
theorem exists_ccmPolarConstrained_point_one_source_small
    (a : SuzukiPositiveAperture) (x : ℝ) (hx : |x| < a.1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧ g x = 1 ∧
        ‖g.toCCMFormVector‖ < ε ∧
        |ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector| < ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt ε hε
  obtain ⟨g, hg, hgx, hgn⟩ := exists_ccmPolarConstrained_point_one_norm_lt
    a x hx (min ε δ) (lt_min hε hδ)
  refine ⟨g, hg, hgx, hgn.trans_le (min_le_left _ _), ?_⟩
  have hdist : dist g.toCCMFormVector (0 : CCMArchimedeanFormDomain a) < δ := by
    simpa only [dist_zero_right] using hgn.trans_le (min_le_right _ _)
  have hq := hd hdist
  simpa only [ccmRestrictedWeilSourceQuadratic_zero, dist_zero_right, Real.norm_eq_abs] using hq

/-- A positive point-sampling term cannot be dominated by the full actual Weil quadratic,
even with an arbitrary finite multiplicative allowance and both exact pole constraints. -/
theorem not_ccmPolarConstrained_point_energy_dominated
    (a : SuzukiPositiveAperture) (x : ℝ) (hx : |x| < a.1) :
    ¬ ∃ C : ℝ, ∀ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector →
        ‖g x‖ ^ 2 ≤ C * |ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector| := by
  rintro ⟨C, hC⟩
  obtain ⟨g, hg, hgx, _, hgq⟩ := exists_ccmPolarConstrained_point_one_source_small
    a x hx (1 / (|C| + 1)) (by positivity)
  have hval := hC g hg
  rw [hgx, norm_one, one_pow] at hval
  have hsmall := (lt_div_iff₀ (show 0 < |C| + 1 by positivity)).mp hgq
  have hle := mul_le_mul_of_nonneg_right (le_abs_self C)
    (abs_nonneg (ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector))
  nlinarith [abs_nonneg (ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector)]

end RHTower
