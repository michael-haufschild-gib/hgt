import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerKreinLaxPhillipsRealization
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowRealizations
import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimeCombIsATranslation

/-!
# Window Serre duality is not the linear Krein reflection

Every positive-length window contains a reflection-odd smooth unit test of strictly positive
complete Weil energy. The odd eigenspace of the PM Krein reflection has nonpositive Krein
energy. Consequently no real-linear isometry of these forms can intertwine the two reflections.
The obstruction concerns the linear identification; Mellin transport includes conjugation
and an exponential twist.
-/

noncomputable section
open Set MeasureTheory
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticCompensationTheory ArithmeticCriticalityTheory

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Every nonempty window has a Serre-odd unit test with a uniform positive Weil lower bound.
A narrow normalized odd bump is translated to the center of the window. -/
theorem exists_windowInvolution_odd_weilQuad_pos {A : ℝ} (hA : 0 < A) :
    ∃ H : ℝ → ℝ, IsWindowTest A H ∧ windowInvolution A H = -H ∧
      (∫ u, H u ^ 2) = 1 ∧ 1 / 4 ≤ weilQuad H := by
  let r := min (A / 2) (1 / 2000)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hrA : r ≤ A / 2 := min_le_left _ _
  have hrsmall : r ≤ 1 / 2000 := min_le_right _ _
  let F := rescaledTest unitOddBump r
  obtain ⟨hreg, -, hodd, hsupp, hmass⟩ :=
    exists_odd_smooth_family_sharp_comb_rate.1 r hr
  have hf : ContDiff ℝ 2 F := hreg 2
  have hnorm : (∫ u, F u ^ 2) = 1 := by
    simpa only [autoCorr, add_zero, ← pow_two] using hmass
  have hq : 1 / 4 ≤ weilQuad F := by
    have hsmall : IsWindowTest (2 * r) (fun u => F (u + r)) := by
      refine ⟨hf.comp (contDiff_id.add contDiff_const), fun u hu => hsupp _ ?_⟩
      by_contra hn
      obtain ⟨hl, hh⟩ := abs_le.mp (le_of_not_gt hn)
      exact hu ⟨by linarith, by linarith⟩
    have hb := weilQuad_ge_of_short hsmall (by linarith) (by linarith)
    have hshift : weilQuad (fun u => F (u + r)) = weilQuad F := by
      simpa only [sub_neg_eq_add] using weilQuad_translate F (-r)
    rw [integral_add_right_eq_self (fun u => F u ^ 2) r, hnorm, hshift] at hb
    exact hb
  let H : ℝ → ℝ := fun u => F (u + A / 2)
  have hH : IsWindowTest A H := by
    refine ⟨hf.comp (contDiff_id.add contDiff_const), fun u hu => hsupp _ ?_⟩
    by_contra hn
    obtain ⟨hl, hh⟩ := abs_le.mp (le_of_not_gt hn)
    exact hu ⟨by linarith, by linarith⟩
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · funext u
    change F (-A - u + A / 2) = -F (u + A / 2)
    rw [show -A - u + A / 2 = -(u + A / 2) by ring]
    exact hodd _
  · change (∫ u, F (u + A / 2) ^ 2) = 1
    rw [integral_add_right_eq_self (fun u => F u ^ 2) (A / 2), hnorm]
  · have ht : weilQuad H = weilQuad F := by
      simpa only [sub_neg_eq_add] using weilQuad_translate F (-(A / 2))
    rw [ht]
    exact hq

/-- The odd eigenspace of the actual PM reflection has nonpositive Krein square. -/
theorem mayerKreinForm_nonpos_of_reflection_neg {v : mayerPeriodKreinSpace}
    (hv : mayerKreinReflection v = -v) : (mayerKreinForm v v).re ≤ 0 := by
  have he : mayerKreinForm v v = -mayerKreinPosInner v v := by
    rw [mayerKreinForm, ← mayerKreinPosInner_reflection_adj, hv]
    rw [← neg_one_smul ℂ v, mayerKreinPosInner_smul_left, neg_one_mul]
  rw [he, Complex.neg_re]
  exact neg_nonpos.mpr (mayerKreinPosInner_self_re_nonneg v)

/-- No real-linear map preserves the complete Weil form and identifies window Serre duality
with the linear PM Krein reflection, on any positive-length window. -/
theorem no_weil_isometric_krein_reflection_intertwiner {A : ℝ} (hA : 0 < A) :
    ¬ ∃ T : windowTests A →ₗ[ℝ] mayerPeriodKreinSpace,
      (∀ H : windowTests A, (mayerKreinForm (T H) (T H)).re = weilQuad H) ∧
      (∀ H : windowTests A,
        T ⟨windowInvolution A H, H.2.windowInvolution⟩ = mayerKreinReflection (T H)) := by
  rintro ⟨T, hform, hreflect⟩
  obtain ⟨H, hH, hodd, -, hq⟩ := exists_windowInvolution_odd_weilQuad_pos hA
  have hsub : (⟨windowInvolution A H, hH.windowInvolution⟩ : windowTests A) =
      -(⟨H, hH⟩ : windowTests A) := Subtype.ext hodd
  have hv : mayerKreinReflection (T ⟨H, hH⟩) = -(T ⟨H, hH⟩) := by
    rw [← hreflect ⟨H, hH⟩, hsub, map_neg]
  have hn := mayerKreinForm_nonpos_of_reflection_neg hv
  rw [hform ⟨H, hH⟩] at hn
  linarith

#print axioms exists_windowInvolution_odd_weilQuad_pos
#print axioms no_weil_isometric_krein_reflection_intertwiner

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
