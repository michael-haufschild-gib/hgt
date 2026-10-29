import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRobinConstantOfAnAtom
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates

/-!
# The aperture includes the width of the profile

If a profile is supported in `[a,b]`, its length-`N` atomic test at width `w`
is supported in `[aw, log N+bw]`. Centering this interval gives aperture
`(log N+(b-a)w)/2`, hence outer autocorrelation cutoff `N exp((b-a)w)`.
The polynomial length and the literal support cutoff are distinct coordinates.
-/

noncomputable section

set_option autoImplicit false

open Finset

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

open ArithmeticElectrostatics

/-- Center of the support interval supplied by a profile supported in `[a,b]`. -/
def profileAtomicCenter (N : ℕ) (w a b : ℝ) : ℝ :=
  (Real.log N + (a + b) * w) / 2

/-- Aperture supplied by the complete atomic support interval. -/
def profileAtomicAperture (N : ℕ) (w a b : ℝ) : ℝ :=
  (Real.log N + (b - a) * w) / 2

/-- The actual atomic support retains both profile endpoints. -/
theorem atomicTest_atomDilate_eq_zero_outside {φ : ℝ → ℝ} {a b w : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc a b → φ u = 0) (hw : 0 < w)
    (N : ℕ) (x : ℕ → ℝ) {u : ℝ}
    (hu : u ∉ Set.Icc (a * w) (Real.log N + b * w)) :
    atomicTest N x (atomDilate φ w) u = 0 := by
  change (∑ n ∈ Icc 1 N, x n * φ ((u - Real.log n) / w)) = 0
  refine sum_eq_zero fun n hn => ?_
  have hn1 := (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
  have harg : (u - Real.log n) / w ∉ Set.Icc a b := by
    intro harg
    have hlo := (le_div_iff₀ hw).mp harg.1
    have hhi := (div_le_iff₀ hw).mp harg.2
    exact hu ⟨by linarith only [hlo, hl0], by linarith only [hhi, hlN]⟩
  rw [hsupp _ harg, mul_zero]

/-- Translation to the midpoint gives the exact enclosing symmetric aperture. -/
theorem centered_atomicTest_eq_zero_outside_aperture {φ : ℝ → ℝ} {a b w : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc a b → φ u = 0) (hw : 0 < w)
    (N : ℕ) (x : ℕ → ℝ) {u : ℝ}
    (hu : profileAtomicAperture N w a b < |u|) :
    atomicTest N x (atomDilate φ w) (u + profileAtomicCenter N w a b) = 0 := by
  apply atomicTest_atomDilate_eq_zero_outside hsupp hw
  intro hmem
  have hlo := hmem.1
  have hhi := hmem.2
  have habs : |u| ≤ profileAtomicAperture N w a b := by
    rw [abs_le]
    dsimp only [profileAtomicCenter] at hlo hhi
    dsimp only [profileAtomicAperture]
    constructor <;> linarith only [hlo, hhi]
  exact (not_le_of_gt hu) habs

theorem profileAtomicAperture_eq_nominal_add (N : ℕ) (w a b : ℝ) :
    profileAtomicAperture N w a b = aperture N + (b - a) * w / 2 := by
  unfold profileAtomicAperture aperture
  ring

/-- The outer prime cutoff of the enclosing support includes the profile-width factor. -/
theorem exp_two_profileAtomicAperture {N : ℕ} (hN : 1 ≤ N) (w a b : ℝ) :
    Real.exp (2 * profileAtomicAperture N w a b) =
      (N : ℝ) * Real.exp ((b - a) * w) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [profileAtomicAperture,
    show 2 * ((Real.log N + (b - a) * w) / 2) = Real.log N + (b - a) * w by ring,
    Real.exp_add, Real.exp_log hN0]

theorem plateau_aperture_cutoff {N : ℕ} (hN : 1 ≤ N) (w : ℝ) :
    Real.exp (2 * profileAtomicAperture N w 0 1) = (N : ℝ) * Real.exp w := by
  simpa only [sub_zero, one_mul] using exp_two_profileAtomicAperture hN w 0 1

theorem symmetric_profile_aperture_cutoff {N : ℕ} (hN : 1 ≤ N) (w : ℝ) :
    Real.exp (2 * profileAtomicAperture N w (-1) 1) = (N : ℝ) * Real.exp (2 * w) := by
  simpa only [show (1 : ℝ) - -1 = 2 by norm_num] using
    exp_two_profileAtomicAperture hN w (-1) 1

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.atomicTest_atomDilate_eq_zero_outside
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.centered_atomicTest_eq_zero_outside_aperture
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.exp_two_profileAtomicAperture
