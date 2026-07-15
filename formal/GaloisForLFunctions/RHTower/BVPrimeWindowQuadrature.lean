import GaloisForLFunctions.HTGeometry.BoundedVariationRiemannSum
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bounded-variation multiplicative prime windows

This file defines the concrete window class used by the bounded-variation divisor-tomography
theorem and proves the analytic input behind its quadrature remainder.  The Mellin weight is
clamped to the support interval before multiplication by the window.  Because the window vanishes
off that interval, this is exactly the ordinary Mellin integrand, while the clamped factor is
globally Lipschitz and avoids any artificial singularity at the origin.
-/

open Complex Filter Finset MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace RHTower

/-- A complex multiplicative window, supported away from zero, whose extension by zero has bounded
variation on the real line.  Integrability is recorded explicitly because mathlib does not yet
derive Bochner integrability of complex BV maps from `BoundedVariationOn`. -/
structure CompactBVPrimeWindow where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  toFun : ℝ → ℂ
  eq_zero_off_support : ∀ x, x ∉ Set.Icc lower upper → toFun x = 0
  integrable : Integrable toFun volume
  boundedVariation : BoundedVariationOn toFun Set.univ

instance : CoeFun CompactBVPrimeWindow (fun _ ↦ ℝ → ℂ) :=
  ⟨CompactBVPrimeWindow.toFun⟩

namespace CompactBVPrimeWindow

theorem lower_le_upper (W : CompactBVPrimeWindow) : W.lower ≤ W.upper :=
  W.lower_lt_upper.le

theorem upper_pos (W : CompactBVPrimeWindow) : 0 < W.upper :=
  W.lower_pos.trans W.lower_lt_upper

@[simp]
theorem zero_eq (W : CompactBVPrimeWindow) : W 0 = 0 := by
  apply W.eq_zero_off_support
  simp only [Set.mem_Icc, not_and_or]
  exact Or.inl (not_le.mpr W.lower_pos)

/-- A BV window is bounded by its total variation, using the zero value to the left of its support
as the base point. -/
theorem norm_le_totalVariation (W : CompactBVPrimeWindow) (x : ℝ) :
    ‖W x‖ ≤ (eVariationOn W Set.univ).toReal := by
  have h := W.boundedVariation.dist_le (Set.mem_univ x) (Set.mem_univ 0)
  simpa only [W.zero_eq, dist_eq_norm, sub_zero] using h

/-- The positive Mellin base clamped to the support interval. -/
def mellinBase (W : CompactBVPrimeWindow) (x : ℝ) : ℝ :=
  Set.projIcc W.lower W.upper W.lower_le_upper x

theorem mellinBase_mem (W : CompactBVPrimeWindow) (x : ℝ) :
    W.mellinBase x ∈ Set.Icc W.lower W.upper :=
  (Set.projIcc W.lower W.upper W.lower_le_upper x).property

theorem mellinBase_pos (W : CompactBVPrimeWindow) (x : ℝ) :
    0 < W.mellinBase x :=
  W.lower_pos.trans_le (W.mellinBase_mem x).1

/-- Globally regularized Mellin weight.  On the support it is exactly `x⁻s`; outside the support
its value is irrelevant because the window vanishes. -/
def mellinWeight (W : CompactBVPrimeWindow) (s : ℂ) (x : ℝ) : ℂ :=
  (W.mellinBase x : ℂ) ^ (-s)

/-- The complex Mellin integrand with a globally Lipschitz weight representative. -/
def mellinIntegrand (W : CompactBVPrimeWindow) (s : ℂ) (x : ℝ) : ℂ :=
  W x * W.mellinWeight s x

/-- Clamping does not change the Mellin integrand. -/
theorem mellinIntegrand_eq_raw (W : CompactBVPrimeWindow) (s : ℂ) (x : ℝ) :
    W.mellinIntegrand s x = W x * (x : ℂ) ^ (-s) := by
  by_cases hx : x ∈ Set.Icc W.lower W.upper
  · rw [mellinIntegrand, mellinWeight, mellinBase,
      Set.projIcc_of_mem W.lower_le_upper hx]
  · rw [mellinIntegrand, W.eq_zero_off_support x hx]
    simp

/-- The Mellin transform of a concrete compact BV window. -/
def mellinTransform (W : CompactBVPrimeWindow) (s : ℂ) : ℂ :=
  ∫ x, W.mellinIntegrand s x

private theorem hasDerivAt_ofReal_cpow_neg
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
      ((-s) * (x : ℂ) ^ (-s - 1)) x := by
  exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) (neg_ne_zero.mpr hs)

/-- For every Mellin coordinate, the clamped Mellin weight is globally Lipschitz and bounded.  The
constants are produced from the derivative maximum on the compact support interval; no analytic
regularity assumption is stored in the window. -/
theorem exists_mellinWeight_lipschitz_bound
    (W : CompactBVPrimeWindow) (s : ℂ) :
    ∃ Mh : ℝ, ∃ C : ℝ≥0, 0 ≤ Mh ∧
      (∀ x, ‖W.mellinWeight s x‖ ≤ Mh) ∧
      LipschitzWith C (W.mellinWeight s) := by
  by_cases hs : s = 0
  · subst s
    refine ⟨1, 0, by norm_num, ?_, ?_⟩
    · intro x
      simp [mellinWeight, W.mellinBase_pos x |>.ne']
    · have hconst : W.mellinWeight 0 = fun _ ↦ 1 := by
        funext x
        simp [mellinWeight, W.mellinBase_pos x |>.ne']
      rw [hconst]
      exact LipschitzWith.const 1
  · let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (-s)
    let F' : ℝ → ℂ := fun x ↦ (-s) * (x : ℂ) ^ (-s - 1)
    have hpos : ∀ x ∈ Set.Icc W.lower W.upper, 0 < x := by
      intro x hx
      exact W.lower_pos.trans_le hx.1
    have hF'cont : ContinuousOn F' (Set.Icc W.lower W.upper) := by
      dsimp only [F']
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.cpow_const (Complex.continuous_ofReal.comp_continuousOn continuousOn_id)
      intro x hx
      simpa using hpos x hx
    have hnormCont : ContinuousOn (fun x ↦ ‖F' x‖) (Set.Icc W.lower W.upper) :=
      hF'cont.norm
    obtain ⟨R, hR⟩ := (isCompact_Icc : IsCompact (Set.Icc W.lower W.upper)).exists_bound_of_continuousOn
      hnormCont
    have hR0 : 0 ≤ R := by
      exact (norm_nonneg (F' W.lower)).trans (by
        simpa only [Real.norm_of_nonneg (norm_nonneg _)] using
          hR W.lower ⟨le_rfl, W.lower_le_upper⟩)
    let C : ℝ≥0 := Real.toNNReal R
    have hCcoe : (C : ℝ) = R := Real.coe_toNNReal _ hR0
    have hFderiv : ∀ x ∈ Set.Icc W.lower W.upper,
        HasDerivWithinAt F (F' x) (Set.Icc W.lower W.upper) x := by
      intro x hx
      exact (hasDerivAt_ofReal_cpow_neg (hpos x hx) hs).hasDerivWithinAt
    have hFlip : LipschitzOnWith C F (Set.Icc W.lower W.upper) := by
      apply (convex_Icc W.lower W.upper).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hFderiv
      intro x hx
      rw [← NNReal.coe_le_coe, hCcoe]
      simpa only [F', coe_nnnorm, Real.norm_of_nonneg (norm_nonneg _)] using hR x hx
    have hproj : LipschitzWith 1 (Set.projIcc W.lower W.upper W.lower_le_upper) :=
      LipschitzWith.projIcc W.lower_le_upper
    have hweightLip : LipschitzWith C (W.mellinWeight s) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (F (W.mellinBase x)) (F (W.mellinBase y)) ≤ (C : ℝ) * dist x y
      have hprojDist : dist (W.mellinBase x) (W.mellinBase y) ≤ dist x y := by
        simpa using hproj.dist_le_mul x y
      exact (hFlip.dist_le_mul _ (W.mellinBase_mem x) _ (W.mellinBase_mem y)).trans
        (mul_le_mul_of_nonneg_left hprojDist C.coe_nonneg)
    let Mh : ℝ := ‖F W.lower‖ + (C : ℝ) * (W.upper - W.lower)
    have hMh0 : 0 ≤ Mh := by
      dsimp only [Mh]
      exact add_nonneg (norm_nonneg _) <|
        mul_nonneg C.coe_nonneg (sub_nonneg.mpr W.lower_le_upper)
    refine ⟨Mh, C, hMh0, ?_, hweightLip⟩
    intro x
    have hxmem := W.mellinBase_mem x
    have hdist := hFlip.dist_le_mul (W.mellinBase x) hxmem W.lower
      ⟨le_rfl, W.lower_le_upper⟩
    have hbaseDist : dist (W.mellinBase x) W.lower ≤ W.upper - W.lower := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxmem.1)]
      linarith [hxmem.2]
    calc
      ‖W.mellinWeight s x‖ = ‖F (W.mellinBase x)‖ := rfl
      _ ≤ ‖F W.lower‖ + dist (F (W.mellinBase x)) (F W.lower) := by
        rw [dist_eq_norm]
        exact norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖F W.lower‖ + (C : ℝ) * dist (W.mellinBase x) W.lower := by
        gcongr
      _ ≤ Mh := by
        dsimp only [Mh]
        gcongr

/-- The Mellin integrand of every compact BV window has bounded variation on every compact real
interval, obtained from the window variation and the clamped Lipschitz Mellin weight. -/
theorem mellinIntegrand_boundedVariationOn
    (W : CompactBVPrimeWindow) (s : ℂ) {c d : ℝ} (hcd : c ≤ d) :
    BoundedVariationOn (W.mellinIntegrand s) (Set.Icc c d) := by
  obtain ⟨Mh, C, hMh0, hMh, hLip⟩ := W.exists_mellinWeight_lipschitz_bound s
  apply HTGeometry.BoundedVariationOn.mul_of_norm_le_of_lipschitzOn hcd
    (W.boundedVariation.mono (Set.subset_univ _))
    (eVariationOn W Set.univ).toReal_nonneg hMh0
  · intro x hx
    exact W.norm_le_totalVariation x
  · intro x hx
    exact hMh x
  · exact hLip.lipschitzOnWith

end CompactBVPrimeWindow

end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- The clamped Mellin integrand is globally integrable. -/
theorem mellinIntegrand_integrable (W : CompactBVPrimeWindow) (s : ℂ) :
    Integrable (W.mellinIntegrand s) volume := by
  obtain ⟨Mh, C, hMh0, hMh, hLip⟩ := W.exists_mellinWeight_lipschitz_bound s
  exact W.integrable.mul_bdd hLip.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hMh)

/-- The Mellin integrand is supported on the original compact window. -/
theorem support_mellinIntegrand_subset (W : CompactBVPrimeWindow) (s : ℂ) :
    Function.support (W.mellinIntegrand s) ⊆ Set.Icc W.lower W.upper := by
  intro x hx
  by_contra hxs
  exact hx (by simp [mellinIntegrand, W.eq_zero_off_support x hxs])

/-- Number of positive mesh endpoints needed to cover the support at scale `k`. -/
def gridCount (W : CompactBVPrimeWindow) (k : ℕ) : ℕ :=
  ⌈W.upper * (k : ℝ)⌉₊

/-- The mesh endpoint covers the upper edge of the window support. -/
theorem upper_le_gridCount_div (W : CompactBVPrimeWindow) {k : ℕ} (hk : 1 ≤ k) :
    W.upper ≤ (W.gridCount k : ℝ) / k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (le_div_iff₀ hkreal).2
  simpa only [gridCount] using (Nat.le_ceil (W.upper * (k : ℝ)))

/-- The covering mesh endpoint overshoots the support by less than one unit for every `k ≥ 1`. -/
theorem gridCount_div_le_upper_add_one (W : CompactBVPrimeWindow) {k : ℕ} (hk : 1 ≤ k) :
    (W.gridCount k : ℝ) / k ≤ W.upper + 1 := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hceil := Nat.ceil_lt_add_one
    (mul_nonneg W.upper_pos.le (Nat.cast_nonneg k))
  apply (div_le_iff₀ hkreal).2
  calc
    (W.gridCount k : ℝ) ≤ W.upper * (k : ℝ) + 1 := by
      simpa only [gridCount] using hceil.le
    _ ≤ (W.upper + 1) * (k : ℝ) := by nlinarith

/-- The interval integral over the complete positive grid is the Mellin transform, because the
integrand vanishes off the compact support. -/
theorem integral_zero_gridCount_eq_mellinTransform
    (W : CompactBVPrimeWindow) (s : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (∫ x in 0..(W.gridCount k : ℝ) / k, W.mellinIntegrand s x) =
      W.mellinTransform s := by
  rw [mellinTransform]
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hxs := W.support_mellinIntegrand_subset s hx
  exact ⟨W.lower_pos.trans_le hxs.1, hxs.2.trans (W.upper_le_gridCount_div hk)⟩

/-- The right-endpoint Riemann sum for the Mellin integrand at scale `k`. -/
def gridRiemannSum (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) : ℂ :=
  ((1 / (k : ℝ)) : ℝ) •
    ∑ i ∈ Finset.range (W.gridCount k),
      W.mellinIntegrand s (((i + 1 : ℕ) : ℝ) / k)

/-- The unscaled BV quadrature remainder. -/
def gridError (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) : ℂ :=
  W.gridRiemannSum k s - W.mellinTransform s

/-- The raw grid error is controlled by the total variation of the Mellin integrand on the covered
mesh interval. -/
theorem norm_gridError_le_variation
    (W : CompactBVPrimeWindow) {k : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    ‖W.gridError k s‖ ≤
      (1 / (k : ℝ)) *
        (eVariationOn (W.mellinIntegrand s)
          (Set.Icc 0 ((W.gridCount k : ℝ) / k))).toReal := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) ≤ (W.gridCount k : ℝ) / k := by positivity
  have hint : IntervalIntegrable (W.mellinIntegrand s) volume 0
      ((W.gridCount k : ℝ) / k) :=
    (W.mellinIntegrand_integrable s).intervalIntegrable
  have hvar := W.mellinIntegrand_boundedVariationOn s hD0
  have hq := HTGeometry.norm_rightEndpoint_riemannSum_sub_integral_le_eVariationOn
    (g := W.mellinIntegrand s) (k := (k : ℝ)) hkreal
    (n := W.gridCount k) hint hvar
  rw [gridError, gridRiemannSum, ← W.integral_zero_gridCount_eq_mellinTransform s hk]
  simpa only [Nat.cast_add, Nat.cast_one] using hq

/-- Pointwise first-order BV quadrature: for each Mellin coordinate there is a concrete finite
constant, independent of the scale, bounding the grid remainder by `Q / k`. -/
theorem exists_norm_gridError_le_div
    (W : CompactBVPrimeWindow) (s : ℂ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ k : ℕ, 1 ≤ k → ‖W.gridError k s‖ ≤ Q / k := by
  obtain ⟨Mh, C, hMh0, hMh, hLip⟩ := W.exists_mellinWeight_lipschitz_bound s
  let V : ℝ := (eVariationOn W Set.univ).toReal
  let Q : ℝ := Mh * V + V * (C : ℝ) * (W.upper + 1)
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hupperOne : 0 ≤ W.upper + 1 := by linarith [W.upper_pos]
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  refine ⟨Q, hQ0, ?_⟩
  intro k hk
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let D : ℝ := (W.gridCount k : ℝ) / k
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hDle : D ≤ W.upper + 1 := W.gridCount_div_le_upper_add_one hk
  have hprod := HTGeometry.eVariationOn_mul_le_of_norm_le_of_lipschitzOn
    (f := W.toFun) (h := W.mellinWeight s) (a := 0) (b := D)
    (Mf := V) (Mh := Mh) hD0
    (W.boundedVariation.mono (Set.subset_univ _)) hV0 hMh0
    (fun x hx => W.norm_le_totalVariation x)
    (fun x hx => hMh x) hLip.lipschitzOnWith
  have hprodReal :
      (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal ≤
        Mh * V + V * (C : ℝ) * D := by
    have h := ENNReal.toReal_mono (by simp) hprod
    rw [ENNReal.toReal_ofReal] at h
    · have hWlocal :
          (eVariationOn W (Set.Icc 0 D)).toReal ≤ V := by
          exact ENNReal.toReal_mono W.boundedVariation
            (eVariationOn.mono W (Set.subset_univ _))
      calc
        (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal ≤
            Mh * (eVariationOn W (Set.Icc 0 D)).toReal + V * (C : ℝ) * D := by
          simpa only [mellinIntegrand, sub_zero] using h
        _ ≤ Mh * V + V * (C : ℝ) * D := by
          gcongr
    · positivity
  calc
    ‖W.gridError k s‖ ≤ (1 / (k : ℝ)) *
        (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal := by
      simpa only [D] using W.norm_gridError_le_variation hk s
    _ ≤ (1 / (k : ℝ)) * (Mh * V + V * (C : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hprodReal (by positivity)
    _ ≤ (1 / (k : ℝ)) * Q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp only [Q]
      gcongr
    _ = Q / k := by field_simp

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- The Mellin-scaled quadrature error appearing after reversal of the moving-window double sum. -/
def scaledGridError (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) : ℂ :=
  (k : ℂ) ^ (1 - s) * W.gridError k s

/-- Pointwise Mellin quadrature bound in the exact scale required by the von-Mangoldt remainder. -/
theorem exists_norm_scaledGridError_le_rpow
    (W : CompactBVPrimeWindow) (s : ℂ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ k : ℕ, 1 ≤ k →
      ‖W.scaledGridError k s‖ ≤ Q * (k : ℝ) ^ (-s.re) := by
  obtain ⟨Q, hQ0, hQ⟩ := W.exists_norm_gridError_le_div s
  refine ⟨Q, hQ0, ?_⟩
  intro k hk
  have hkpos : 0 < k := by omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  rw [scaledGridError, norm_mul, Complex.norm_natCast_cpow_of_pos hkpos]
  calc
    (k : ℝ) ^ (1 - s).re * ‖W.gridError k s‖ ≤
        (k : ℝ) ^ (1 - s).re * (Q / k) :=
      mul_le_mul_of_nonneg_left (hQ k hk) (Real.rpow_nonneg hkreal.le _)
    _ = Q * (k : ℝ) ^ (-s.re) := by
      rw [Complex.sub_re, Complex.one_re, div_eq_mul_inv,
        ← Real.rpow_neg_one]
      calc
        (k : ℝ) ^ (1 - s.re) * (Q * (k : ℝ) ^ (-1 : ℝ)) =
            Q * ((k : ℝ) ^ (1 - s.re) * (k : ℝ) ^ (-1 : ℝ)) := by ring
        _ = Q * (k : ℝ) ^ ((1 - s.re) + (-1 : ℝ)) := by
          rw [Real.rpow_add hkreal]
        _ = Q * (k : ℝ) ^ (-s.re) := by ring_nf

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

private theorem hasDerivAt_ofReal_cpow_neg_all
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
      ((-s) * (x : ℂ) ^ (-s - 1)) x := by
  by_cases hs : s = 0
  · subst s
    simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ)))
  · exact hasDerivAt_ofReal_cpow_neg hx hs

/-- A compact family of Mellin coordinates admits common bounds for the clamped weight and its
Lipschitz constant.  The constants come from maxima of the weight and its real derivative on the
compact product `K × [a,b]`. -/
theorem exists_mellinWeight_uniform_lipschitz_bound
    (W : CompactBVPrimeWindow) {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ Mh : ℝ, ∃ C : ℝ≥0, 0 ≤ Mh ∧
      (∀ s ∈ K, ∀ x, ‖W.mellinWeight s x‖ ≤ Mh) ∧
      (∀ s ∈ K, LipschitzWith C (W.mellinWeight s)) := by
  let P : Set (ℂ × ℝ) := K ×ˢ Set.Icc W.lower W.upper
  have hPcompact : IsCompact P := hK.prod isCompact_Icc
  have hpos : ∀ p ∈ P, 0 < p.2 := by
    intro p hp
    exact W.lower_pos.trans_le hp.2.1
  have hbaseCont : ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ)) P :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hweightCpowCont : ContinuousOn
      (fun p : ℂ × ℝ => (p.2 : ℂ) ^ (-p.1)) P := by
    apply hbaseCont.cpow continuous_fst.neg.continuousOn
    intro p hp
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hpos p hp
  have hderivCpowCont : ContinuousOn
      (fun p : ℂ × ℝ => (p.2 : ℂ) ^ (-p.1 - 1)) P := by
    apply hbaseCont.cpow (continuous_fst.neg.sub continuous_const).continuousOn
    intro p hp
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hpos p hp
  have hweightNormCont : ContinuousOn
      (fun p : ℂ × ℝ => ‖(p.2 : ℂ) ^ (-p.1)‖) P :=
    hweightCpowCont.norm
  have hderivNormCont : ContinuousOn
      (fun p : ℂ × ℝ => ‖(-p.1) * (p.2 : ℂ) ^ (-p.1 - 1)‖) P :=
    (continuous_fst.neg.continuousOn.mul hderivCpowCont).norm
  obtain ⟨Mh, hMh⟩ := hPcompact.exists_bound_of_continuousOn hweightNormCont
  obtain ⟨R, hR⟩ := hPcompact.exists_bound_of_continuousOn hderivNormCont
  obtain ⟨s₀, hs₀⟩ := hKne
  have hp₀ : (s₀, W.lower) ∈ P := ⟨hs₀, le_rfl, W.lower_le_upper⟩
  have hMh0 : 0 ≤ Mh := by
    exact (norm_nonneg ((W.lower : ℂ) ^ (-s₀))).trans (by
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hMh (s₀, W.lower) hp₀)
  have hR0 : 0 ≤ R := by
    exact (norm_nonneg ((-s₀) * (W.lower : ℂ) ^ (-s₀ - 1))).trans (by
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hR (s₀, W.lower) hp₀)
  let C : ℝ≥0 := Real.toNNReal R
  have hCcoe : (C : ℝ) = R := Real.coe_toNNReal _ hR0
  have hFlip (s : ℂ) (hs : s ∈ K) :
      LipschitzOnWith C (fun x : ℝ => (x : ℂ) ^ (-s))
        (Set.Icc W.lower W.upper) := by
    apply (convex_Icc W.lower W.upper).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    · intro x hx
      exact (hasDerivAt_ofReal_cpow_neg_all
        (W.lower_pos.trans_le hx.1) s).hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, hCcoe]
      simpa only [coe_nnnorm, Real.norm_of_nonneg (norm_nonneg _)] using
        hR (s, x) ⟨hs, hx⟩
  have hproj : LipschitzWith 1 (Set.projIcc W.lower W.upper W.lower_le_upper) :=
    LipschitzWith.projIcc W.lower_le_upper
  refine ⟨Mh, C, hMh0, ?_, ?_⟩
  · intro s hs x
    simpa only [mellinWeight, mellinBase, Real.norm_of_nonneg (norm_nonneg _)] using
      hMh (s, W.mellinBase x) ⟨hs, W.mellinBase_mem x⟩
  · intro s hs
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hprojDist : dist (W.mellinBase x) (W.mellinBase y) ≤ dist x y := by
      simpa using hproj.dist_le_mul x y
    exact ((hFlip s hs).dist_le_mul _ (W.mellinBase_mem x) _
      (W.mellinBase_mem y)).trans
        (mul_le_mul_of_nonneg_left hprojDist C.coe_nonneg)

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- Compact-uniform first-order quadrature bound. -/
theorem exists_uniform_norm_gridError_le_div
    (W : CompactBVPrimeWindow) {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ s ∈ K, ∀ k : ℕ, 1 ≤ k →
      ‖W.gridError k s‖ ≤ Q / k := by
  obtain ⟨Mh, C, hMh0, hMh, hLip⟩ :=
    W.exists_mellinWeight_uniform_lipschitz_bound hK hKne
  let V : ℝ := (eVariationOn W Set.univ).toReal
  let Q : ℝ := Mh * V + V * (C : ℝ) * (W.upper + 1)
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    have : 0 ≤ W.upper + 1 := by linarith [W.upper_pos]
    positivity
  refine ⟨Q, hQ0, ?_⟩
  intro s hs k hk
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let D : ℝ := (W.gridCount k : ℝ) / k
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hDle : D ≤ W.upper + 1 := W.gridCount_div_le_upper_add_one hk
  have hprod := HTGeometry.eVariationOn_mul_le_of_norm_le_of_lipschitzOn
    (f := W.toFun) (h := W.mellinWeight s) (a := 0) (b := D)
    (Mf := V) (Mh := Mh) hD0
    (W.boundedVariation.mono (Set.subset_univ _)) hV0 hMh0
    (fun x hx => W.norm_le_totalVariation x)
    (fun x hx => hMh s hs x) (hLip s hs).lipschitzOnWith
  have hprodReal :
      (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal ≤
        Mh * V + V * (C : ℝ) * D := by
    have h := ENNReal.toReal_mono (by simp) hprod
    rw [ENNReal.toReal_ofReal] at h
    · have hWlocal : (eVariationOn W (Set.Icc 0 D)).toReal ≤ V :=
        ENNReal.toReal_mono W.boundedVariation
          (eVariationOn.mono W (Set.subset_univ _))
      calc
        (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal ≤
            Mh * (eVariationOn W (Set.Icc 0 D)).toReal + V * (C : ℝ) * D := by
          simpa only [mellinIntegrand, sub_zero] using h
        _ ≤ Mh * V + V * (C : ℝ) * D := by gcongr
    · positivity
  calc
    ‖W.gridError k s‖ ≤ (1 / (k : ℝ)) *
        (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal := by
      simpa only [D] using W.norm_gridError_le_variation hk s
    _ ≤ (1 / (k : ℝ)) * (Mh * V + V * (C : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hprodReal (by positivity)
    _ ≤ (1 / (k : ℝ)) * Q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp only [Q]
      gcongr
    _ = Q / k := by field_simp

/-- Compact-uniform Mellin-scaled error bound. -/
theorem exists_uniform_norm_scaledGridError_le_rpow
    (W : CompactBVPrimeWindow) {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ s ∈ K, ∀ k : ℕ, 1 ≤ k →
      ‖W.scaledGridError k s‖ ≤ Q * (k : ℝ) ^ (-s.re) := by
  obtain ⟨Q, hQ0, hQ⟩ := W.exists_uniform_norm_gridError_le_div hK hKne
  refine ⟨Q, hQ0, ?_⟩
  intro s hs k hk
  have hkpos : 0 < k := by omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  rw [scaledGridError, norm_mul, Complex.norm_natCast_cpow_of_pos hkpos]
  calc
    (k : ℝ) ^ (1 - s).re * ‖W.gridError k s‖ ≤
        (k : ℝ) ^ (1 - s).re * (Q / k) :=
      mul_le_mul_of_nonneg_left (hQ s hs k hk) (Real.rpow_nonneg hkreal.le _)
    _ = Q * (k : ℝ) ^ (-s.re) := by
      rw [Complex.sub_re, Complex.one_re, div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        (k : ℝ) ^ (1 - s.re) * (Q * (k : ℝ) ^ (-1 : ℝ)) =
            Q * ((k : ℝ) ^ (1 - s.re) * (k : ℝ) ^ (-1 : ℝ)) := by ring
        _ = Q * (k : ℝ) ^ ((1 - s.re) + (-1 : ℝ)) := by
          rw [Real.rpow_add hkreal]
        _ = Q * (k : ℝ) ^ (-s.re) := by ring_nf

end CompactBVPrimeWindow
end RHTower
