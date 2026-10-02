import GaloisForLFunctions.RHTower.SoninMixedBlockPolarizationSplit
import GaloisForLFunctions.RHTower.SoninApertureFourierParityNoGo
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# A bounded section of the actual Sonin annular restriction

The asymmetric time-band resolvent removes the physical band without changing
the prescribed finite Fourier band. Consequently every even Fourier annulus
above the Sonin gap has an actual bounded lift into the Sonin carrier.
-/

noncomputable section

namespace RHTower

private theorem eq_zero_of_evenTimeBand_fixed {b c : ℝ} {f : evenSubspace}
    (hf : evenIndicatorCutoff b (evenFourierCutoff c f) = f) : f = 0 := by
  have hA : ‖evenIndicatorCutoff b (evenFourierCutoff c f)‖ ≤
      ‖evenFourierCutoff c f‖ := by
    change ‖indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
      (evenFourierCutoff c f : SoninL2)‖ ≤ ‖(evenFourierCutoff c f : SoninL2)‖
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    exact (physicalForbidden (centralInterval b)
      (measurableSet_centralInterval b)).norm_starProjection_apply_le _
  have hR : ‖evenFourierCutoff c f‖ ≤ ‖f‖ := by
    change ‖fourierCutoff (centralInterval c) (measurableSet_centralInterval c)
      (f : SoninL2)‖ ≤ ‖(f : SoninL2)‖
    rw [fourierCutoff_eq_fourierForbidden_starProjection]
    exact (fourierForbidden (centralInterval c)
      (measurableSet_centralInterval c)).norm_starProjection_apply_le _
  rw [hf] at hA
  have hnorm : ‖evenFourierCutoff c f‖ = ‖f‖ := le_antisymm hR hA
  have hRfix : evenFourierCutoff c f = f := by
    apply Subtype.ext
    change fourierCutoff (centralInterval c) (measurableSet_centralInterval c)
      (f : SoninL2) = (f : SoninL2)
    rw [fourierCutoff_eq_fourierForbidden_starProjection]
    apply Submodule.starProjection_eq_self_iff.mpr
    apply (Submodule.mem_iff_norm_starProjection _ _).mpr
    change ‖fourierCutoff (centralInterval c) (measurableSet_centralInterval c)
      (f : SoninL2)‖ = ‖(f : SoninL2)‖ at hnorm
    simpa only [fourierCutoff_eq_fourierForbidden_starProjection] using hnorm
  exact eq_zero_of_evenIndicatorCutoff_eq_self_of_evenFourierCutoff_eq_self
    (by simpa only [hRfix] using hf) hRfix

/-- The actual asymmetric time-band complement is invertible on the full even space. -/
theorem isUnit_one_sub_evenIndicatorFourierBlock (b c : ℝ) (hb : 0 < b) :
    IsUnit (1 - evenIndicatorCutoff b * evenFourierCutoff c) := by
  rcases (isCompactOperator_evenIndicatorFourierBlock b c hb).hasEigenvalue_or_mem_resolventSet
      (one_ne_zero : (1 : ℂ) ≠ 0) with heig | hres
  · obtain ⟨f, hf, hfne⟩ := heig.exists_hasEigenvector
    simp only [Module.End.mem_genEigenspace_one, one_smul] at hf
    exact (hfne (eq_zero_of_evenTimeBand_fixed hf)).elim
  · simpa only [spectrum.mem_resolventSet_iff, map_one] using hres

/-- The bounded inverse is selected from the proved unit, with no spectral premise. -/
def evenSoninTimeBandInverse (b c : ℝ) (hb : 0 < b) :
    evenSubspace →L[ℂ] evenSubspace :=
  ↑((isUnit_one_sub_evenIndicatorFourierBlock b c hb).unit⁻¹)

theorem evenSoninTimeBandInverse_left (b c : ℝ) (hb : 0 < b) :
    (1 - evenIndicatorCutoff b * evenFourierCutoff c) *
      evenSoninTimeBandInverse b c hb = 1 :=
  (isUnit_one_sub_evenIndicatorFourierBlock b c hb).mul_val_inv

theorem evenSoninTimeBandInverse_right (b c : ℝ) (hb : 0 < b) :
    evenSoninTimeBandInverse b c hb *
      (1 - evenIndicatorCutoff b * evenFourierCutoff c) = 1 :=
  (isUnit_one_sub_evenIndicatorFourierBlock b c hb).val_inv_mul

/-- Remove the physical band while retaining the entire prescribed Fourier band. -/
def evenSoninBandExtension (b c : ℝ) (hb : 0 < b) :
    evenSubspace →L[ℂ] evenSubspace :=
  1 - (1 - evenFourierCutoff c) * evenSoninTimeBandInverse b c hb *
    evenIndicatorCutoff b

theorem evenIndicatorCutoff_mul_evenSoninBandExtension (b c : ℝ) (hb : 0 < b) :
    evenIndicatorCutoff b * evenSoninBandExtension b c hb = 0 := by
  let A := evenIndicatorCutoff b
  let R := evenFourierCutoff c
  let G := evenSoninTimeBandInverse b c hb
  let H := G * A
  have hAA : A * A = A := evenIndicatorCutoff_mul_of_le b b le_rfl
  have hG : (1 - A * R) * G = 1 := evenSoninTimeBandInverse_left b c hb
  have hH : H - A * R * H = A := by
    calc
      H - A * R * H = ((1 - A * R) * G) * A := by
        simp only [H, sub_mul, one_mul, mul_assoc]
      _ = A := by rw [hG, one_mul]
  have hAH : A * H = H := by
    have heq := congrArg (fun X : evenSubspace →L[ℂ] evenSubspace => A * X) hH
    have hAAH : A * (A * R * H) = A * R * H := by
      simp only [← mul_assoc, hAA]
    rw [mul_sub, hAAH, hAA] at heq
    have hcancel := congrArg
      (fun X : evenSubspace →L[ℂ] evenSubspace => X + A * R * H) (heq.trans hH.symm)
    simpa only [sub_add_cancel] using hcancel
  change A * (1 - (1 - R) * G * A) = 0
  calc
    A * (1 - (1 - R) * G * A) = A - (A * H - A * R * H) := by
      simp only [H, mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
    _ = 0 := by rw [hAH, hH, sub_self]

theorem evenFourierCutoff_mul_evenSoninBandExtension (b c : ℝ) (hb : 0 < b) :
    evenFourierCutoff c * evenSoninBandExtension b c hb = evenFourierCutoff c := by
  have hRR := evenFourierCutoff_mul_of_le c c le_rfl
  unfold evenSoninBandExtension
  rw [mul_sub, mul_one, ← mul_assoc, ← mul_assoc, mul_sub, mul_one, hRR,
    sub_self, zero_mul, zero_mul, sub_zero]

/-- An annular datum has a bounded lift into the actual Sonin carrier. -/
theorem evenSoninBandExtension_mem_sonin {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    {u : evenSubspace} (hu : evenFourierCutoff b u = 0) :
    evenSoninBandExtension b c hb u ∈ evenCentralSoninCarrier b := by
  apply (mem_evenCentralSoninCarrier_iff_cutoffs_zero b _).mpr
  constructor
  · exact DFunLike.congr_fun (evenIndicatorCutoff_mul_evenSoninBandExtension b c hb) u
  · have hR : evenFourierCutoff b * evenSoninBandExtension b c hb =
        evenFourierCutoff b := by
      calc
        evenFourierCutoff b * evenSoninBandExtension b c hb =
            (evenFourierCutoff b * evenFourierCutoff c) *
              evenSoninBandExtension b c hb := by rw [evenFourierCutoff_mul_of_le b c hbc]
        _ = evenFourierCutoff b := by
          rw [mul_assoc, evenFourierCutoff_mul_evenSoninBandExtension,
            evenFourierCutoff_mul_of_le b c hbc]
    exact (DFunLike.congr_fun hR u).trans hu

/-- Exact surjectivity onto the even Fourier annulus, including its endpoints. -/
theorem exists_sonin_lift_of_fourier_annulus {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    {u : evenSubspace} (hu : evenFourierCutoff b u = 0)
    (huc : evenFourierCutoff c u = u) :
    ∃ f ∈ evenCentralSoninCarrier b, evenFourierCutoff c f = u := by
  refine ⟨evenSoninBandExtension b c hb u,
    evenSoninBandExtension_mem_sonin hb hbc hu, ?_⟩
  exact (DFunLike.congr_fun (evenFourierCutoff_mul_evenSoninBandExtension b c hb) u).trans huc

/-- The annulus is exactly the range, rather than only a dense set of boundary data. -/
theorem exists_sonin_lift_iff_fourier_annulus {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    (u : evenSubspace) :
    (∃ f ∈ evenCentralSoninCarrier b, evenFourierCutoff c f = u) ↔
      evenFourierCutoff b u = 0 ∧ evenFourierCutoff c u = u := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨?_, DFunLike.congr_fun (evenFourierCutoff_mul_of_le c c le_rfl) f⟩
    exact (DFunLike.congr_fun (evenFourierCutoff_mul_of_le b c hbc) f).trans
      ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mp hf).2
  · rintro ⟨hlo, hhi⟩
    exact exists_sonin_lift_of_fourier_annulus hb hbc hlo hhi

end RHTower
