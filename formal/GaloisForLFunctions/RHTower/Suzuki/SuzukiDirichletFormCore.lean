import GaloisForLFunctions.RHTower.Suzuki.SuzukiH01OperatorDomain
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogLaurentFormCore

/-!
# Suzuki's Dirichlet domain is a core for the exact restricted Weil form

Suzuki's 2026 Friedrichs-extension theorem needs more than the inclusion
`H₀¹(-a,a) ⊆ D(Q_W^a)`: the image of `H₀¹` must be dense in the complete form domain.  This
module proves that missing closure statement.  A smooth vector supported strictly inside the
aperture is recovered exactly by integrating its classical derivative from the left endpoint.
Its derivative has zero mean, so this recovery is through Suzuki's literal Dirichlet inverse.
The already proved density of strict-interior smooth vectors then gives the full form-core result.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Interval `L²` coordinate of the classical derivative of a smooth compactly supported test. -/
def suzukiSmoothDerivativeCoordinate (a : SuzukiPositiveAperture)
    (g : ℝ → ℂ) (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) : SuzukiApertureIntervalL2 a.1 :=
  suzukiApertureRestrictL2 a.1
    (suzukiComplexTestL2 (deriv g)
      ((contDiff_infty_iff_deriv.mp hgdiff).2) hgsupp.deriv)

theorem suzukiSmoothDerivativeCoordinate_coeFn
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) :
    (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp :
        SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
      fun x => deriv g (x : ℝ) := by
  let dg : SoninL2 := suzukiComplexTestL2 (deriv g)
    ((contDiff_infty_iff_deriv.mp hgdiff).2) hgsupp.deriv
  have hdg : (dg : ℝ → ℂ) =ᵐ[volume] deriv g :=
    suzukiComplexTestL2_coeFn (deriv g)
      ((contDiff_infty_iff_deriv.mp hgdiff).2) hgsupp.deriv
  have hdgSub : (fun x : SuzukiApertureInterval a.1 => dg (x : ℝ)) =ᵐ[volume]
      fun x => deriv g (x : ℝ) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp (ae_restrict_of_ae hdg)
  change (suzukiApertureRestrictL2 a.1 dg :
      SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] _
  filter_upwards [suzukiApertureRestrictL2_coeFn a.1 dg,
    suzukiApertureRestrictRepresentative_ae a.1 dg, hdgSub]
      with x hrestrict hrep hdgPoint
  rw [hrestrict, hrep, hdgPoint]

theorem suzukiSmoothDerivativeCoordinate_zeroMean
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp ∈
      SuzukiApertureZeroMean a := by
  rw [mem_suzukiApertureZeroMean_iff, suzukiApertureIntervalMean]
  have hderiv : ∀ x : ℝ, HasDerivAt g (deriv g x) x := fun x =>
    (hgdiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hint : IntervalIntegrable (deriv g) volume (-a.1) a.1 :=
    ((contDiff_infty_iff_deriv.mp hgdiff).2.continuous).intervalIntegrable _ _
  have hend := aperture_endpoint_jets_zero hginterior
  calc
    (∫ x : SuzukiApertureInterval a.1,
        (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp) x ∂volume) =
      ∫ x : SuzukiApertureInterval a.1, deriv g (x : ℝ) ∂volume := by
        apply integral_congr_ae
        exact suzukiSmoothDerivativeCoordinate_coeFn a g hgdiff hgsupp
    _ = ∫ x in Icc (-a.1) a.1, deriv g x := by
      rw [← integral_subtype measurableSet_Icc]
    _ = ∫ x in (-a.1)..a.1, deriv g x := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [a.2])]
    _ = g a.1 - g (-a.1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hint
    _ = 0 := by rw [hend.1, hend.2.1, sub_zero]

/-- Exact zero-mean derivative coordinate associated with a strict-interior smooth test. -/
def suzukiSmoothDerivativeZeroMean
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    SuzukiApertureZeroMean a :=
  ⟨suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp,
    suzukiSmoothDerivativeCoordinate_zeroMean a g hgdiff hgsupp hginterior⟩

theorem suzukiApertureZeroExtend_smoothDerivativeCoordinate
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    suzukiApertureZeroExtend
        (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp) =ᵐ[volume]
      deriv g := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae
        (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp),
      suzukiSmoothDerivativeCoordinate_coeFn a g hgdiff hgsupp]
        with x hrep hcoord
    rw [suzukiApertureZeroExtend_apply, hrep, hcoord]
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl]
      with x hx
    have hxIcc : x ∉ Icc (-a.1) a.1 := hx
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem _ hxIcc]
    symm
    apply Function.notMem_support.mp
    intro hxderiv
    have hxg : x ∈ tsupport g :=
      tsupport_deriv_subset (subset_tsupport (deriv g) hxderiv)
    exact hxIcc (Ioo_subset_Icc_self (hginterior hxg))

/-- Fundamental theorem of calculus in Suzuki's literal primitive coordinate. -/
theorem suzukiAperturePrimitive_smoothDerivativeCoordinate
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    suzukiAperturePrimitive a.1
        (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp) =
      suzukiApertureRestrictL2 a.1 (suzukiComplexTestL2 g hgdiff hgsupp) := by
  apply Lp.ext
  have hderiv : ∀ x : ℝ, HasDerivAt g (deriv g x) x := fun x =>
    (hgdiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hint : ∀ t : SuzukiApertureInterval a.1,
      IntervalIntegrable (deriv g) volume (-a.1) (t : ℝ) := fun t =>
    ((contDiff_infty_iff_deriv.mp hgdiff).2.continuous).intervalIntegrable _ _
  have hleft : g (-a.1) = 0 :=
    (aperture_endpoint_jets_zero hginterior).1
  have hzero := suzukiApertureZeroExtend_smoothDerivativeCoordinate
    a g hgdiff hgsupp hginterior
  have hgfull : (suzukiComplexTestL2 g hgdiff hgsupp : ℝ → ℂ) =ᵐ[volume] g :=
    suzukiComplexTestL2_coeFn g hgdiff hgsupp
  have hgsub : (fun x : SuzukiApertureInterval a.1 =>
      (suzukiComplexTestL2 g hgdiff hgsupp : SoninL2) (x : ℝ)) =ᵐ[volume]
      fun x => g (x : ℝ) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp (ae_restrict_of_ae hgfull)
  filter_upwards [suzukiAperturePrimitive_coeFn a.1
      (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp),
    suzukiApertureRestrictL2_coeFn a.1 (suzukiComplexTestL2 g hgdiff hgsupp),
    suzukiApertureRestrictRepresentative_ae a.1
      (suzukiComplexTestL2 g hgdiff hgsupp), hgsub] with t hprim hrestrict hrep hgpoint
  rw [hprim, hrestrict, hrep, hgpoint,
    suzukiAperturePrefix_eq_intervalIntegral]
  calc
    (∫ x in (-a.1)..(t : ℝ),
        suzukiApertureZeroExtend
          (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp) x) =
      ∫ x in (-a.1)..(t : ℝ), deriv g x := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hzero] with x hx _
        exact hx
    _ = g (t : ℝ) - g (-a.1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) (hint t)
    _ = g (t : ℝ) := by rw [hleft, sub_zero]

/-- Every strict-interior smooth logarithmic form vector is a literal zero-mean primitive. -/
theorem suzukiHlogInteriorSmoothCore_mem_primitiveRange
    (a : SuzukiPositiveAperture) {q : SuzukiHlogFormDomain a}
    (hq : q ∈ suzukiHlogInteriorSmoothCore a) :
    q ∈ LinearMap.range (suzukiAperturePrimitiveHlogFormLM a) := by
  rcases hq with ⟨g, hgdiff, hgsupp, hginterior, hqembed⟩
  let f := suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp
  refine ⟨f, ?_⟩
  apply suzukiHlogFormEmbedding_injective a
  change suzukiHlogFormEmbedding a
      (suzukiAperturePrimitiveHlogFormVector a f) =
    suzukiHlogFormEmbedding a q
  rw [suzukiHlogFormEmbedding_primitiveHlogFormVector,
    suzukiAperturePrimitive_smoothDerivativeCoordinate
      a g hgdiff hgsupp hginterior]
  exact (suzukiApertureZeroExtendL2_restrict_eq a
    ⟨suzukiComplexTestL2 g hgdiff hgsupp, by
      rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
      refine ⟨suzukiComplexTestL2 g hgdiff hgsupp, ?_⟩
      apply Lp.ext
      filter_upwards [indicatorCutoff_ae (centralInterval a.1)
          (measurableSet_centralInterval a.1)
          (suzukiComplexTestL2 g hgdiff hgsupp),
        suzukiComplexTestL2_coeFn g hgdiff hgsupp] with x hcut hgx
      change (indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1)
          (suzukiComplexTestL2 g hgdiff hgsupp) : SoninL2) x =
        (suzukiComplexTestL2 g hgdiff hgsupp : SoninL2) x
      rw [hcut]
      by_cases hx : x ∈ centralInterval a.1
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hgx]
        symm
        apply Function.notMem_support.mp
        intro hxg
        exact hx (by simpa [centralInterval] using
          Ioo_subset_Icc_self (hginterior (subset_tsupport g hxg)))⟩).trans
    hqembed.symm

/-- A strict-interior smooth logarithmic form vector, transported to the exact CCM form domain,
lies in the range of Suzuki's literal `H₀¹` form lift. -/
theorem ccmLogFormToArchimedean_interiorSmoothCore_mem_dirichletRange
    (a : SuzukiPositiveAperture) {q : SuzukiHlogFormDomain a}
    (hq : q ∈ suzukiHlogInteriorSmoothCore a) :
    ccmLogFormToArchimedean a q ∈
      LinearMap.range (suzukiDirichletDomainCCMFormLift a) := by
  rcases hq with ⟨g, hgdiff, hgsupp, hginterior, hqembed⟩
  let f0 : SuzukiApertureZeroMean a :=
    suzukiSmoothDerivativeZeroMean a g hgdiff hgsupp hginterior
  obtain ⟨hdom, happly⟩ := suzukiDirichletDerivative_apply_inverse a f0
  let v : (suzukiDirichletDerivative a).domain :=
    ⟨suzukiDirichletInverseCLM a f0, hdom⟩
  refine ⟨v, ?_⟩
  apply suzukiWeilIntervalFormEmbedding_injective a
  rw [suzukiWeilIntervalFormEmbedding_dirichletDomainCCMFormLift]
  change suzukiDirichletInverseCLM a f0 =
    suzukiWeilIntervalFormEmbedding a (ccmLogFormToArchimedean a q)
  change suzukiAperturePrimitive a.1
      (suzukiSmoothDerivativeCoordinate a g hgdiff hgsupp) = _
  rw [suzukiAperturePrimitive_smoothDerivativeCoordinate
    a g hgdiff hgsupp hginterior]
  change suzukiApertureRestrictL2 a.1 (suzukiComplexTestL2 g hgdiff hgsupp) =
    (suzukiApertureL2Equiv a).symm
      (ccmArchimedeanFormToAperture a (ccmLogFormToArchimedean a q))
  apply (suzukiApertureL2Equiv a).injective
  apply Subtype.ext
  rw [(suzukiApertureL2Equiv a).apply_symm_apply]
  change suzukiApertureZeroExtendL2
      (suzukiApertureRestrictL2 a.1 (suzukiComplexTestL2 g hgdiff hgsupp)) =
    ccmArchimedeanFourierToTime (ccmLogToArchimedean q.1)
  rw [ccmArchimedeanFourierToTime_logToArchimedean]
  have hleft := suzukiApertureZeroExtendL2_restrict_eq a
    ⟨suzukiComplexTestL2 g hgdiff hgsupp, by
      rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
      refine ⟨suzukiComplexTestL2 g hgdiff hgsupp, ?_⟩
      apply Lp.ext
      filter_upwards [indicatorCutoff_ae (centralInterval a.1)
          (measurableSet_centralInterval a.1)
          (suzukiComplexTestL2 g hgdiff hgsupp),
        suzukiComplexTestL2_coeFn g hgdiff hgsupp] with x hcut hgx
      change (indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1)
          (suzukiComplexTestL2 g hgdiff hgsupp) : SoninL2) x =
        (suzukiComplexTestL2 g hgdiff hgsupp : SoninL2) x
      rw [hcut]
      by_cases hx : x ∈ centralInterval a.1
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hgx]
        symm
        apply Function.notMem_support.mp
        intro hxg
        exact hx (by simpa [centralInterval] using
          Ioo_subset_Icc_self (hginterior (subset_tsupport g hxg)))⟩
  rw [hleft]
  exact hqembed.symm

/-- **Suzuki (2026), equation (3.2), completed form-core consequence.**

The literal Dirichlet domain `H₀¹(-a,a)` is dense in the complete exact CCM restricted-Weil form
domain in its form norm.  This is the closure statement needed for the Friedrichs extension; no
additional regularity, RH, or density premise remains.
-/
theorem denseRange_suzukiDirichletDomainCCMFormLift
    (a : SuzukiPositiveAperture) :
    DenseRange (suzukiDirichletDomainCCMFormLift a) := by
  have hdense : Dense (ccmLogFormToArchimedean a ''
      suzukiHlogInteriorSmoothCore a) :=
    (ccmArchimedeanLogFormDomainEquiv a).surjective.denseRange.dense_image
      (ccmLogFormToArchimedean a).continuous
      (dense_suzukiHlogInteriorSmoothCore a)
  apply hdense.mono
  rintro y ⟨q, hq, rfl⟩
  exact ccmLogFormToArchimedean_interiorSmoothCore_mem_dirichletRange a hq

end RHTower

end
