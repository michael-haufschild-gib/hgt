import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilDilationCriticalLineShift

/-!
# Exact cosine/sine modulation and broad two-cluster mixtures

A cosine/sine pair multiplies autocorrelation by one cosine. Translation
differences retain both cross terms. These identities construct an actual
finitely supported mixture in the full Weil test interface, with smoothness
and nonnegative weights preserved. No nullness or energy sign is assumed.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The two real modulating factors used for exact cosine moments. -/
def cosineProfile (β : ℝ → ℂ) (T : ℝ) (u : ℝ) : ℂ := β u * (Real.cos (T*u) : ℂ)
def sineProfile (β : ℝ → ℂ) (T : ℝ) (u : ℝ) : ℂ := β u * (Real.sin (T*u) : ℂ)
def clusterDifference (β : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ := β u - β (u-L)

theorem contDiff_cosineProfile {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β) (T : ℝ) :
    ContDiff ℝ ∞ (cosineProfile β T) := by
  have ht : ContDiff ℝ ∞ (fun u : ℝ => Real.cos (T*u)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  exact hβ.mul (Complex.ofRealCLM.contDiff.comp ht)

theorem contDiff_sineProfile {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β) (T : ℝ) :
    ContDiff ℝ ∞ (sineProfile β T) := by
  have ht : ContDiff ℝ ∞ (fun u : ℝ => Real.sin (T*u)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  exact hβ.mul (Complex.ofRealCLM.contDiff.comp ht)

theorem contDiff_clusterDifference {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β) (L : ℝ) :
    ContDiff ℝ ∞ (clusterDifference β L) := hβ.sub (hβ.comp (by fun_prop))

theorem hasCompactSupport_cosineProfile {β : ℝ → ℂ} (hβ : HasCompactSupport β) (T : ℝ) :
    HasCompactSupport (cosineProfile β T) := hβ.mul_right

theorem hasCompactSupport_sineProfile {β : ℝ → ℂ} (hβ : HasCompactSupport β) (T : ℝ) :
    HasCompactSupport (sineProfile β T) := hβ.mul_right

theorem hasCompactSupport_clusterDifference {β : ℝ → ℂ} (hβ : HasCompactSupport β) (L : ℝ) :
    HasCompactSupport (clusterDifference β L) :=
  hβ.sub (hβ.comp_homeomorph (Homeomorph.subRight L))

private theorem integrable_correlation {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (y : ℝ) :
    Integrable (fun u => β u * conj (β (u-y))) :=
  (hc.mul (continuous_star.comp (hc.comp (continuous_id.sub continuous_const)))).integrable_of_hasCompactSupport
    hs.mul_right

/-- Cosine/sine pairing preserves every correlation phase exactly. -/
theorem weilTest_cosine_sine_add {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (T y : ℝ) :
    EF.weilTest (cosineProfile β T) (cosineProfile β T) y +
      EF.weilTest (sineProfile β T) (sineProfile β T) y =
        (Real.cos (T*y) : ℂ) * EF.weilTest β β y := by
  rw [weilTest_apply, weilTest_apply, weilTest_apply]
  rw [← integral_add
    (integrable_correlation (by unfold cosineProfile; fun_prop) (hasCompactSupport_cosineProfile hs T) y)
    (integrable_correlation (by unfold sineProfile; fun_prop) (hasCompactSupport_sineProfile hs T) y),
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp only [cosineProfile, sineProfile, map_mul, Complex.conj_ofReal]
    have he : Real.cos (T*u)*Real.cos (T*(u-y)) +
        Real.sin (T*u)*Real.sin (T*(u-y)) = Real.cos (T*y) := by
      rw [← Real.cos_sub]
      congr 1
      ring
    have hec := congrArg (fun x : ℝ => (x : ℂ)) he
    simp only [Complex.ofReal_add, Complex.ofReal_mul] at hec
    linear_combination β u * conj (β (u-y)) * hec

/-- The exact two-cluster autocorrelation, retaining both shifted cross terms. -/
theorem weilTest_clusterDifference {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (L y : ℝ) :
    EF.weilTest (clusterDifference β L) (clusterDifference β L) y =
      2*EF.weilTest β β y - EF.weilTest β β (y-L) - EF.weilTest β β (y+L) := by
  have he : clusterDifference β L = fun u => ∑ n ∈ ({0,1} : Finset ℕ),
      (if n=0 then (1:ℂ) else -1) * β (u - if n=0 then 0 else L) := by
    funext u
    simp [clusterDifference, sub_eq_add_neg]
  rw [he, weilTest_sum_translates hc hs]
  simp only [Finset.sum_pair (by norm_num : (0:ℕ) ≠ 1), ite_true,
    if_neg (by norm_num : ¬(1:ℕ)=0), sub_zero, add_zero, sub_add_cancel,
    map_one, map_neg, one_mul, mul_one, neg_mul, mul_neg, neg_neg]
  ring

/-- An interval-supported profile has autocorrelation radius equal to its interval length. -/
theorem weilTest_eq_zero_outside_interval {β : ℝ → ℂ} {W y : ℝ}
    (hs : tsupport β ⊆ Set.Icc 0 W) (hy : W < |y|) : EF.weilTest β β y = 0 := by
  rw [weilTest_apply]
  have he : (fun u => β u * conj (β (u-y))) = fun _ => (0:ℂ) := by
    funext u
    by_cases hu : β u = 0
    · simp [hu]
    by_cases hv : β (u-y) = 0
    · simp [hv]
    have hu' := hs (subset_tsupport _ hu)
    have hv' := hs (subset_tsupport _ hv)
    have habs : |y| ≤ W := abs_le.mpr ⟨by linarith [hu'.1, hv'.2], by linarith [hu'.2, hv'.1]⟩
    exact False.elim (not_le.mpr hy habs)
  rw [he, integral_zero]

/-- A smooth compact test paired with its explicit smoothness certificate. -/
abbrev JointSmoothTest := {f : WeilTestFn // ContDiff ℝ ∞ f.1}

def cosineProfileTest (f : JointSmoothTest) (T : ℝ) : JointSmoothTest :=
  ⟨⟨cosineProfile f.1.1 T,
      (contDiff_cosineProfile f.2 T).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
      hasCompactSupport_cosineProfile f.1.2.2 T⟩,
    contDiff_cosineProfile f.2 T⟩

def sineProfileTest (f : JointSmoothTest) (T : ℝ) : JointSmoothTest :=
  ⟨⟨sineProfile f.1.1 T,
      (contDiff_sineProfile f.2 T).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
      hasCompactSupport_sineProfile f.1.2.2 T⟩,
    contDiff_sineProfile f.2 T⟩

def clusterDifferenceTest (f : JointSmoothTest) (L : ℝ) : JointSmoothTest :=
  ⟨⟨clusterDifference f.1.1 L,
      (contDiff_clusterDifference f.2 L).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
      hasCompactSupport_clusterDifference f.1.2.2 L⟩,
    contDiff_clusterDifference f.2 L⟩

/-- Literal autocorrelation of the weighted modulated profile family. -/
def jointProfileSample {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (w t : ι → ℝ) (y : ℝ) : ℂ :=
  EF.weilTest f.1.1 f.1.1 y + ∑ i, (w i : ℂ) *
    (EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) y +
      EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) y)

theorem jointProfileSample_eq {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (w t : ι → ℝ) (y : ℝ) :
    jointProfileSample f w t y = EF.weilTest f.1.1 f.1.1 y *
      ((1 + ∑ i, w i * Real.cos (t i*y) : ℝ) : ℂ) := by
  simp only [jointProfileSample, weilTest_cosine_sine_add f.2.continuous f.1.2.2]
  push_cast
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem jointProfileSample_neg {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (w t : ι → ℝ) (y : ℝ) : jointProfileSample f w t (-y) = conj (jointProfileSample f w t y) := by
  rw [jointProfileSample_eq, jointProfileSample_eq, weilTest_self_neg]
  simp only [mul_neg, Real.cos_neg, map_mul, Complex.conj_ofReal]

/-- The actual finite two-cluster test mixture; repeated tests merge their weights. -/
def jointClusterMixture {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (L : ℝ) (w t : ι → ℝ) : WeilTestFn →₀ ℝ :=
  Finsupp.single (clusterDifferenceTest f L).1 1 +
    ∑ i, (Finsupp.single (clusterDifferenceTest (cosineProfileTest f (t i)) L).1 (w i) +
      Finsupp.single (clusterDifferenceTest (sineProfileTest f (t i)) L).1 (w i))

theorem jointClusterMixture_nonneg {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (L : ℝ) (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (g : WeilTestFn) :
    0 ≤ jointClusterMixture f L w t g := by
  have h : 0 ≤ jointClusterMixture f L w t := add_nonneg
    (Finsupp.single_nonneg.mpr zero_le_one)
    (Finset.sum_nonneg fun i _ => add_nonneg
      (Finsupp.single_nonneg.mpr (hw i)) (Finsupp.single_nonneg.mpr (hw i)))
  exact h g

theorem jointClusterMixture_sum {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (L : ℝ) (w t : ι → ℝ) (F : WeilTestFn → ℂ) :
    (jointClusterMixture f L w t).sum (fun g r => (r : ℂ)*F g) =
      F (clusterDifferenceTest f L).1 + ∑ i, (w i : ℂ) *
        (F (clusterDifferenceTest (cosineProfileTest f (t i)) L).1 +
          F (clusterDifferenceTest (sineProfileTest f (t i)) L).1) := by
  change (Finsupp.linearCombination ℝ F) (jointClusterMixture f L w t) = _
  simp only [jointClusterMixture, map_add, map_sum, Finsupp.linearCombination_single,
    one_smul, Complex.real_smul, mul_add]

theorem jointClusterMixture_autocorrelation {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (L : ℝ) (w t : ι → ℝ) (y : ℝ) :
    (jointClusterMixture f L w t).sum (fun g r => (r : ℂ)*EF.weilTest g.1 g.1 y) =
      2*jointProfileSample f w t y - jointProfileSample f w t (y-L) -
        jointProfileSample f w t (y+L) := by
  rw [jointClusterMixture_sum]
  have hcos i : Continuous (cosineProfile f.1.1 (t i)) := (contDiff_cosineProfile f.2 _).continuous
  have hsin i : Continuous (sineProfile f.1.1 (t i)) := (contDiff_sineProfile f.2 _).continuous
  simp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest,
    weilTest_clusterDifference f.2.continuous f.1.2.2,
    weilTest_clusterDifference (hcos _) (hasCompactSupport_cosineProfile f.1.2.2 _),
    weilTest_clusterDifference (hsin _) (hasCompactSupport_sineProfile f.1.2.2 _),
    jointProfileSample]
  have he : (∑ i, (w i : ℂ) *
      (2*EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) y -
        EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) (y-L) -
        EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) (y+L) +
       (2*EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) y -
        EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) (y-L) -
        EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) (y+L)))) =
      2*(∑ i, (w i : ℂ)*(EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) y +
        EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) y)) -
      (∑ i, (w i : ℂ)*(EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) (y-L) +
        EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) (y-L))) -
      (∑ i, (w i : ℂ)*(EF.weilTest (cosineProfile f.1.1 (t i)) (cosineProfile f.1.1 (t i)) (y+L) +
        EF.weilTest (sineProfile f.1.1 (t i)) (sineProfile f.1.1 (t i)) (y+L))) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linear_combination he

end RHTower.WeilWorkPBAP
