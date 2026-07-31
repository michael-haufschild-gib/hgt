import GaloisForLFunctions.RHTower.SoninShellProductMixedTerms
import GaloisForLFunctions.RHTower.L2FourierUncertainty

/-!
# The two polarizations of the mixed coupling cannot cancel each other

The four blocks carrying the aperture coupling split into two pairs by the polarization of their
*range*: two land in the physical band between the apertures, two land in the Fourier band between
them.  A vector in both bands is zero — this is the qualitative uncertainty principle — so the two
pairs can only cancel by each vanishing separately.

The four-block cancellation question is therefore two independent two-block questions, one in each
polarization.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory ContinuousLinearMap

/-! ### Qualitative uncertainty on the even subspace -/

/-- **A vector confined to a physical band and to a Fourier band is zero.**  This is the
qualitative uncertainty principle transported to the even subspace. -/
theorem eq_zero_of_evenIndicatorCutoff_eq_self_of_evenFourierCutoff_eq_self
    {a b : ℝ} {v : evenSubspace}
    (hA : evenIndicatorCutoff a v = v) (hR : evenFourierCutoff b v = v) :
    v = 0 := by
  have hfA :
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) (v : SoninL2) =
        (v : SoninL2) := by
    have h := congrArg (fun w : evenSubspace => (w : SoninL2)) hA
    simpa using h
  have hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc (-a) a → ((v : SoninL2) : ℝ → ℂ) x = 0 := by
    filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
      (v : SoninL2)] with x hx hout
    rw [hfA] at hx
    simpa [centralInterval, hout] using hx
  have h0 :
      fourierCutoff (centralInterval b) (measurableSet_centralInterval b) (v : SoninL2) =
        (v : SoninL2) := by
    have h := congrArg (fun w : evenSubspace => (w : SoninL2)) hR
    simpa using h
  have hfR :
      indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
          (fourierUnitary (v : SoninL2)) = fourierUnitary (v : SoninL2) := by
    have h := congrArg fourierUnitary h0
    simpa only [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply] using h
  have hFsupp : ∀ᵐ w ∂volume, w ∉ Set.Icc (-b) b →
      ((fourierUnitary (v : SoninL2) : SoninL2) : ℝ → ℂ) w = 0 := by
    filter_upwards [indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b)
      (fourierUnitary (v : SoninL2))] with w hw hout
    rw [hfR] at hw
    simpa [centralInterval, hout] using hw
  have hzero : (v : SoninL2) = 0 := l2_fourier_uncertainty (v : SoninL2) hsupp hFsupp
  exact Subtype.ext (by simpa using hzero)

/-! ### The two polarized blocks -/

/-- The pair of mixed blocks whose range lies in the physical band `(a, b]`. -/
def soninMixedPhysicalBlock (a b c r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  (evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationSum r hr *
    (evenFourierCutoff c - evenFourierCutoff b)

/-- The pair of mixed blocks whose range lies in the Fourier band `(a, b]`. -/
def soninMixedFourierBlock (a b c r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  (evenFourierCutoff b - evenFourierCutoff a) * evenDilationSum r hr *
    (evenIndicatorCutoff c - evenIndicatorCutoff b)

/-- The physical block absorbs the physical cutoff at the outer aperture: its range is confined to
the physical band. -/
theorem evenIndicatorCutoff_mul_soninMixedPhysicalBlock
    (a b c r : ℝ) (hr : 1 < r) (hab : a ≤ b) :
    evenIndicatorCutoff b * soninMixedPhysicalBlock a b c r hr =
      soninMixedPhysicalBlock a b c r hr := by
  have h1 : evenIndicatorCutoff b * (evenIndicatorCutoff b - evenIndicatorCutoff a) =
      evenIndicatorCutoff b - evenIndicatorCutoff a := by
    rw [mul_sub, evenIndicatorCutoff_mul_of_le_rev a b hab,
      evenIndicatorCutoff_mul_of_le b b le_rfl]
  unfold soninMixedPhysicalBlock
  calc evenIndicatorCutoff b *
        ((evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationSum r hr *
          (evenFourierCutoff c - evenFourierCutoff b))
      = (evenIndicatorCutoff b * (evenIndicatorCutoff b - evenIndicatorCutoff a)) *
          evenDilationSum r hr * (evenFourierCutoff c - evenFourierCutoff b) := by
        noncomm_ring
    _ = (evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationSum r hr *
          (evenFourierCutoff c - evenFourierCutoff b) := by rw [h1]

/-- The Fourier block absorbs the Fourier cutoff at the outer aperture: its range is confined to
the Fourier band. -/
theorem evenFourierCutoff_mul_soninMixedFourierBlock
    (a b c r : ℝ) (hr : 1 < r) (hab : a ≤ b) :
    evenFourierCutoff b * soninMixedFourierBlock a b c r hr =
      soninMixedFourierBlock a b c r hr := by
  have h1 : evenFourierCutoff b * (evenFourierCutoff b - evenFourierCutoff a) =
      evenFourierCutoff b - evenFourierCutoff a := by
    rw [mul_sub, evenFourierCutoff_mul_of_le_rev a b hab,
      evenFourierCutoff_mul_of_le b b le_rfl]
  unfold soninMixedFourierBlock
  calc evenFourierCutoff b *
        ((evenFourierCutoff b - evenFourierCutoff a) * evenDilationSum r hr *
          (evenIndicatorCutoff c - evenIndicatorCutoff b))
      = (evenFourierCutoff b * (evenFourierCutoff b - evenFourierCutoff a)) *
          evenDilationSum r hr * (evenIndicatorCutoff c - evenIndicatorCutoff b) := by
        noncomm_ring
    _ = (evenFourierCutoff b - evenFourierCutoff a) * evenDilationSum r hr *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) := by rw [h1]

/-- The sum of the two polarized blocks is exactly the four-term mixed form of the coupling. -/
theorem soninMixedPhysicalBlock_add_soninMixedFourierBlock_eq
    (a b c r : ℝ) (hr : 1 < r) :
    soninMixedPhysicalBlock a b c r hr + soninMixedFourierBlock a b c r hr =
      (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenFourierCutoff b - evenFourierCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) := by
  unfold soninMixedPhysicalBlock soninMixedFourierBlock
  rw [evenDilationSum_eq]
  noncomm_ring

/-! ### The polarization split -/

/-- **Polarizations cannot cancel.**  The two mixed blocks sum to zero only if each is zero: their
values at a common vector live in the physical and the Fourier band respectively, and a vector in
both bands is zero. -/
theorem soninMixedPhysicalBlock_add_soninMixedFourierBlock_eq_zero_iff
    (a b c r : ℝ) (hr : 1 < r) (hab : a ≤ b) :
    soninMixedPhysicalBlock a b c r hr + soninMixedFourierBlock a b c r hr = 0 ↔
      soninMixedPhysicalBlock a b c r hr = 0 ∧ soninMixedFourierBlock a b c r hr = 0 := by
  constructor
  · intro hsum
    have hphys : soninMixedPhysicalBlock a b c r hr = 0 := by
      apply ContinuousLinearMap.ext
      intro w
      set u := soninMixedPhysicalBlock a b c r hr w with hu
      have hA : evenIndicatorCutoff b u = u := by
        have h := DFunLike.congr_fun
          (evenIndicatorCutoff_mul_soninMixedPhysicalBlock a b c r hr hab) w
        simpa [hu] using h
      have hneg : soninMixedFourierBlock a b c r hr w = -u := by
        have h := DFunLike.congr_fun hsum w
        simp only [add_apply, zero_apply] at h
        rw [← hu] at h
        linear_combination (norm := module) h
      have hR : evenFourierCutoff b u = u := by
        have h := DFunLike.congr_fun
          (evenFourierCutoff_mul_soninMixedFourierBlock a b c r hr hab) w
        rw [mul_apply_eq_comp, hneg, map_neg] at h
        have := neg_injective h
        simpa using this
      simpa using
        eq_zero_of_evenIndicatorCutoff_eq_self_of_evenFourierCutoff_eq_self hA hR
    refine ⟨hphys, ?_⟩
    rw [hphys, zero_add] at hsum
    exact hsum
  · rintro ⟨h1, h2⟩
    rw [h1, h2, add_zero]

/-- **The coupling's mixed part is carried by two independent polarizations.**  Modulo the relative
ideal the successive-layer coupling is the sum of the two polarized blocks, and that sum vanishes
exactly when both blocks do. -/
theorem evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_polarizedBlocks
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr =ᵣ
      soninMixedPhysicalBlock a b c r hr + soninMixedFourierBlock a b c r hr := by
  rw [soninMixedPhysicalBlock_add_soninMixedFourierBlock_eq a b c r hr]
  exact evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_mixed
    ha hb hc hab hbc hr hcr

end RHTower
