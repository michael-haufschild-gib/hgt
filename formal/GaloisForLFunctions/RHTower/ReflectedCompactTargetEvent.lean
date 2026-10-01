import GaloisForLFunctions.RHTower.ReflectedCompactCorrection
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Complex Set Metric MeasureTheory
noncomputable section
namespace RHTower
open SteinhausModel

/-- Absolute Gaussian admission gives continuity in all arithmetic phases. -/
theorem continuous_steinhausFullGaussianCofactor_phase (s : ℂ) {N : ℝ} (hN : 0 < N) :
    Continuous (steinhausFullGaussianCofactor s N) := by
  have hsum := (summable_steinhausFullGaussianCofactor
    (A := |s.re| + 1) (by positivity) (by linarith [le_abs_self s.re]) hN
    (fun _ => 0)).norm
  unfold steinhausFullGaussianCofactor
  apply continuous_tsum (fun n =>
    ((continuous_steinhausCharacter (n + 1)).mul_const _).mul_const _) hsum
  intro n ω
  simp only [norm_mul, norm_X, one_mul, le_refl]

/-- The actual reciprocal complement is continuous in phase, with no omitted tail. -/
theorem continuous_steinhausCompactReflectedComplement_phase {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {N : ℝ} (hN : 0 < N) :
    Continuous (steinhausCompactReflectedComplement z N) := by
  have hsum := summable_norm_reflectedCompactDeepSeries hN hz0 hz1 (fun _ => 0)
  unfold steinhausCompactReflectedComplement
  apply Continuous.const_mul
  apply continuous_tsum (fun n =>
    ((continuous_steinhausCharacter (n + 1)).star).const_mul _) hsum
  intro n ω
  simp only [norm_mul, RCLike.norm_conj, norm_star, norm_X, mul_one, le_refl]

/-- The complete original AFE written in its complex spectral coordinate. -/
def steinhausCompactReflectedAFE (z : ℂ) (N : ℕ) (ω : Omega) : ℂ :=
  zetaChi z * steinhausFullGaussianCofactor z N ω +
    steinhausCompactReflectedCorrection z N ω

theorem continuous_steinhausCompactReflectedAFE_phase {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) {N : ℕ} (hN : 0 < N) :
    Continuous (steinhausCompactReflectedAFE z N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  exact ((continuous_steinhausFullGaussianCofactor_phase z hNR).const_mul _).add
    ((continuous_steinhausCompactReflectedComplement_phase hz0 hz1 hNR).sub continuous_const)

theorem steinhausFullReflectedAFE_eq_compact {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (tau : ℝ) {N : ℕ} (hN : 0 < N) (ω : Omega) :
    steinhausFullReflectedAFE d tau N ω =
      steinhausCompactReflectedAFE (rightDisplacedLinePt d tau) N ω := by
  rw [steinhausFullReflectedAFE_eq_primal_add_compactCorrection hd hdhalf tau hN]
  rfl

/-- The physical phase is exactly zeta, not an approximation or a new carrier. -/
theorem steinhausCompactReflectedAFE_zero {z : ℂ} (hz0 : 1 / 2 < z.re) (hz1 : z.re < 1)
    {N : ℕ} (hN : 0 < N) :
    steinhausCompactReflectedAFE z N (fun _ => 0) = riemannZeta z := by
  have hz : rightDisplacedLinePt (z.re - 1 / 2) z.im = z := by
    apply Complex.ext <;> simp [rightDisplacedLinePt]
  have h := steinhausFullReflectedAFE_zero (d := z.re - 1 / 2)
    (by linarith) (by linarith) z.im hN
  rw [steinhausFullReflectedAFE_eq_compact (by linarith) (by linarith) _ hN, hz] at h
  exact h

/-- Canonical whole-disc target event for the complete original AFE. -/
def reflectedCompactTargetEvent (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (ε : ℝ)
    (N : ℕ) (tau : ℝ) : Set Omega :=
  {ω | ∀ s ∈ closedBall c r, ‖steinhausCompactReflectedAFE (s + (tau : ℂ) * I) N ω - f s‖ ≤ ε}

theorem isClosed_reflectedCompactTargetEvent (c : ℂ) (r : ℝ)
    (hc0 : 0 ≤ c.re - r) (hc1 : c.re + r ≤ 1) (f : ℂ → ℂ) (ε : ℝ)
    {N : ℕ} (hN : 0 < N) (tau : ℝ) :
    IsClosed (reflectedCompactTargetEvent c r f ε N tau) := by
  simp only [reflectedCompactTargetEvent, Set.setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro hs
  have hre : |s.re - c.re| ≤ r := by
    exact (show |s.re - c.re| ≤ dist s c by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)).trans hs
  have h0 : 0 ≤ (s + (tau : ℂ) * I).re := by simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero]; linarith [(abs_le.mp hre).1]
  have h1 : (s + (tau : ℂ) * I).re ≤ 1 := by simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero]; linarith [(abs_le.mp hre).2]
  exact isClosed_le ((continuous_steinhausCompactReflectedAFE_phase h0 h1 hN).sub continuous_const).norm continuous_const

theorem measurableSet_reflectedCompactTargetEvent (c : ℂ) (r : ℝ)
    (hc0 : 0 ≤ c.re - r) (hc1 : c.re + r ≤ 1) (f : ℂ → ℂ) (ε : ℝ)
    {N : ℕ} (hN : 0 < N) (tau : ℝ) :
    MeasurableSet (reflectedCompactTargetEvent c r f ε N tau) :=
  (isClosed_reflectedCompactTargetEvent c r hc0 hc1 f ε hN tau).measurableSet

end RHTower
