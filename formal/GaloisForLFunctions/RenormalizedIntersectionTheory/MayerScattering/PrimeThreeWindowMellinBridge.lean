import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisHeckePrimeThreeEigenvalue
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWindowMellinBridge

/-!
# The second prime in the source-to-window correspondence

The actual seven-branch Lewis operator realizes the logarithmic prime-three shift of window
tests. Together with the prime-two correspondence, both arithmetic grids now act through the
completed source periods. The complete Weil form scales by the prime degree.
-/

noncomputable section
open Complex Set MeasureTheory Zeta23
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticPolarization RenormalizedIntersectionTheory

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The degree-three adjoint shift into a longer window. -/
def heckeWindowPullThree (H : ℝ → ℝ) : ℝ → ℝ := fun u => Real.sqrt 3 * H (u + Real.log 3)

theorem heckeWindowPullThree_mem {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    IsWindowTest (A + Real.log 3) (heckeWindowPullThree H) := by
  refine ⟨contDiff_const.mul (hH.contDiff.comp (contDiff_id.add contDiff_const)), ?_⟩
  intro u hu
  change Real.sqrt 3 * H (u + Real.log 3) = 0
  rw [hH.vanish _ (fun hm => hu ⟨by linarith [hm.1], by
    linarith [hm.2, Real.log_pos (by norm_num : (1 : ℝ) < 3)]⟩), mul_zero]

/-- The source correspondence preserves every term of Weil's form, with degree three. -/
theorem weilQuad_heckeWindowPullThree (H : ℝ → ℝ) :
    weilQuad (heckeWindowPullThree H) = 3 * weilQuad H := by
  unfold heckeWindowPullThree
  rw [weilQuad_const_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have ht := weilQuad_translate H (-Real.log 3)
  simpa only [sub_neg_eq_add] using congrArg (fun q : ℝ => 3 * q) ht

private theorem sqrt_three_exp_factor (s : ℂ) :
    (Real.sqrt 3 : ℂ) * Complex.exp ((2 * s - 1 / 2) * (-Real.log 3 : ℝ)) =
      3 * (3 : ℂ) ^ (-(2 * s)) := by
  have hsqrt : Real.sqrt 3 = Real.exp (Real.log 3 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsqrt, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0)]
  have hlog : (Real.log 3 : ℂ) = Complex.log 3 :=
    Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)
  calc
    Complex.exp ((Real.log 3 / 2 : ℝ) : ℂ) *
        Complex.exp ((2 * s - 1 / 2) * (-Real.log 3 : ℝ)) =
        Complex.exp (Complex.log 3 + Complex.log 3 * (-(2 * s))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [hlog]
      ring
    _ = 3 * Complex.exp (Complex.log 3 * (-(2 * s))) := by
      rw [Complex.exp_add, Complex.exp_log (by norm_num : (3 : ℂ) ≠ 0)]

/-- The Mellin multiplier is the source Hecke eigenvalue minus identity. -/
theorem tr_heckeWindowPullThree (H : ℝ → ℝ) (s : ℂ) :
    tr (fun u => (heckeWindowPullThree H u : ℂ)) (2 * s) =
      (3 * (3 : ℂ) ^ (-(2 * s))) * tr (fun u => (H u : ℂ)) (2 * s) := by
  have hfun : (fun u => (heckeWindowPullThree H u : ℂ)) = fun u =>
      (Real.sqrt 3 : ℂ) * ArithmeticPolarization.translate (-Real.log 3) (fun v => (H v : ℂ)) u := by
    funext u
    simp only [heckeWindowPullThree, ArithmeticPolarization.translate, sub_neg_eq_add, Complex.ofReal_mul]
  rw [hfun, tr, paperFT_const_mul]
  change (Real.sqrt 3 : ℂ) * tr (ArithmeticPolarization.translate (-Real.log 3) (fun u => (H u : ℂ))) (2 * s) = _
  rw [tr_translate, ← mul_assoc, sqrt_three_exp_factor]

/-- The seven source branches realize the second-prime shift of the same normalized
Lewis period used for the prime-two correspondence. -/
theorem lewisHeckeT3_windowMellinPeriod (H : ℝ → ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) {a : ℝ} (ha : 0 < a) :
    lewisHeckeT3 s (windowMellinPeriod H s) a - windowMellinPeriod H s a =
      windowMellinPeriod (heckeWindowPullThree H) s a := by
  have he := eisensteinLewisPeriod_hecke_three hs0 hs1 ha
  have hlin (c : ℂ) :
      lewisHeckeT3 s (fun x : ℝ => c * eisensteinLewisPeriod s x) a =
        c * lewisHeckeT3 s (fun x : ℝ => eisensteinLewisPeriod s x) a := by
    simp only [lewisHeckeT3]
    ring
  unfold windowMellinPeriod
  rw [hlin, he, tr_heckeWindowPullThree]
  ring

#print axioms lewisHeckeT3_windowMellinPeriod
#print axioms weilQuad_heckeWindowPullThree

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
