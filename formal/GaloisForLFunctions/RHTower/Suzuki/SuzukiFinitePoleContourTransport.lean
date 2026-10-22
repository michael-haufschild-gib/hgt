import GaloisForLFunctions.HTGeometry.FinitePoleHorizontalContourShift
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStripRapidDecrease
import GaloisForLFunctions.RHTower.StripRapidContourEdges
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelContourIntegrand

/-!
# Finite-pole transport for Suzuki's exact contour integrand

The exact logarithmic inverse-Mellin integrand is quarter-turned to a vertical-strip function.
All-order Deninger--Meyer Mellin decay absorbs polynomial growth of the shifted-Xi quotient and
the bounded-strip exponential factor.  This kills both vertical rectangle sides and specializes
the arbitrary-order finite-pole residue theorem with the exact inverse-Fourier normalization.
-/

namespace RHTower

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped BigOperators Interval

noncomputable section

theorem hasStripPolyGrowthOffReal_exp_real_mul (r : ℝ) :
    HasStripPolyGrowthOffReal (fun s : ℂ => Complex.exp (s * (r : ℂ))) := by
  intro a b
  refine ⟨0, 0, Real.exp (max |a| |b| * |r|), (Real.exp_pos _).le, fun s ha hb _ => ?_⟩
  rw [Complex.norm_exp]
  have hsabs : |s.re| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · calc
        -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
        _ ≤ a := neg_abs_le a
        _ ≤ s.re := ha
    · calc
        s.re ≤ b := hb
        _ ≤ |b| := le_abs_self b
        _ ≤ max |a| |b| := le_max_right _ _
  have hmul : (s * (r : ℂ)).re ≤ max |a| |b| * |r| := by
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc
      s.re * r ≤ |s.re * r| := le_abs_self _
      _ = |s.re| * |r| := abs_mul _ _
      _ ≤ max |a| |b| * |r| :=
        mul_le_mul_of_nonneg_right hsabs (abs_nonneg r)
  simpa using Real.exp_le_exp.mpr hmul

/-- Exact Suzuki contour integrand after the quarter-turn `z = i s`. -/
def suzukiCanonicalRotatedHankelContourIntegrand
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (s : ℂ) : ℂ :=
  suzukiCanonicalHankelContourIntegrand omega g r (Complex.I * s)

theorem suzukiCanonicalRotatedHankelContourIntegrand_eq
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (s : ℂ) :
    suzukiCanonicalRotatedHankelContourIntegrand omega g r s =
      suzukiCanonicalTheta omega (Complex.I * s) *
        deningerMeyerStrongLogMellin g s * Complex.exp (s * (r : ℂ)) := by
  rw [suzukiCanonicalRotatedHankelContourIntegrand,
    suzukiCanonicalHankelContourIntegrand]
  have hrot : -Complex.I * (Complex.I * s) = s := by
    rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
    ring
  rw [hrot]

theorem hasStripRapidDecrease_suzukiCanonicalRotatedHankelContourIntegrand
    {omega : ℝ}
    (htheta : HasStripPolyGrowthOffReal
      (fun s : ℂ => suzukiCanonicalTheta omega (Complex.I * s)))
    (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    HasStripRapidDecrease
      (suzukiCanonicalRotatedHankelContourIntegrand omega g r) := by
  have hM := hasStripRapidDecrease_deningerMeyerStrongLogMellin g
  have hMtheta := hM.mul_stripPolyGrowth htheta
  have h := hMtheta.mul_stripPolyGrowth (hasStripPolyGrowthOffReal_exp_real_mul r)
  rw [show suzukiCanonicalRotatedHankelContourIntegrand omega g r =
      fun s : ℂ =>
        (deningerMeyerStrongLogMellin g s *
          suzukiCanonicalTheta omega (Complex.I * s)) * Complex.exp (s * (r : ℂ)) by
    funext s
    rw [suzukiCanonicalRotatedHankelContourIntegrand_eq]
    ring]
  exact h

theorem vIntegral_eq_I_mul_hIntegral_quarterTurn (f : ℂ → ℂ) (x c d : ℝ) :
    VIntegral f x c d =
      Complex.I * HIntegral (fun s : ℂ => f (Complex.I * s)) c d (-x) := by
  simp only [VIntegral, HIntegral, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  apply congrArg f
  symm
  calc
    Complex.I * ((y : ℂ) + ((-x : ℝ) : ℂ) * Complex.I) =
        Complex.I * (y : ℂ) + (-((x : ℂ))) * (Complex.I * Complex.I) := by
      push_cast
      ring
    _ = (x : ℂ) + (y : ℂ) * Complex.I := by
      rw [Complex.I_mul_I]
      ring

private theorem continuous_rotated_line_of_analytic_horizontal
    {f : ℂ → ℂ} {c d sigma : ℝ} (hcd : c ≤ d) (hσ : sigma = c ∨ sigma = d)
    {P : Finset ℂ} (hPim : ∀ p ∈ P, c < p.im ∧ p.im < d)
    (hoff : ∀ s : ℂ, c ≤ s.im → s.im ≤ d → s ∉ P → AnalyticAt ℂ f s) :
    Continuous fun y : ℝ =>
      f (Complex.I * ((sigma : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  let z : ℂ := Complex.I * ((sigma : ℂ) + (y : ℂ) * Complex.I)
  have hzim : z.im = sigma := by simp [z, Complex.mul_im]
  have hzP : z ∉ P := by
    intro hz
    have hp := hPim z hz
    rw [hzim] at hp
    rcases hσ with hsc | hsd
    · exact (lt_irrefl c) (by simpa [hsc] using hp.1)
    · exact (lt_irrefl d) (by simpa [hsd] using hp.2)
  have hzAnalytic := hoff z
    (by
      rw [hzim]
      rcases hσ with hsc | hsd
      · rw [hsc]
      · rw [hsd]
        exact hcd)
    (by
      rw [hzim]
      rcases hσ with hsc | hsd
      · rw [hsc]
        exact hcd
      · rw [hsd]) hzP
  have hpath : ContinuousAt
      (fun y : ℝ => Complex.I * ((sigma : ℂ) + (y : ℂ) * Complex.I)) y := by
    fun_prop
  have hcomp := ContinuousAt.comp (x := y) hzAnalytic.continuousAt hpath
  change ContinuousAt (f ∘ fun y : ℝ =>
    Complex.I * ((sigma : ℂ) + (y : ℂ) * Complex.I)) y
  exact hcomp

private theorem integrable_horizontal_of_rotated_stripRapidDecrease
    {f : ℂ → ℂ} {c d sigma : ℝ} (hcd : c ≤ d) (hσ : sigma = c ∨ sigma = d)
    {P : Finset ℂ} (hPim : ∀ p ∈ P, c < p.im ∧ p.im < d)
    (hoff : ∀ s : ℂ, c ≤ s.im → s.im ≤ d → s ∉ P → AnalyticAt ℂ f s)
    (hrapid : HasStripRapidDecrease (fun s : ℂ => f (Complex.I * s))) :
    Integrable fun x : ℝ => f ((x : ℂ) + (sigma : ℂ) * Complex.I) := by
  have hline : Integrable (fun y : ℝ =>
      f (Complex.I * ((sigma : ℂ) + (y : ℂ) * Complex.I))) :=
    integrable_line_of_stripRapidDecrease hrapid
      (continuous_rotated_line_of_analytic_horizontal hcd hσ hPim hoff)
  refine hline.comp_neg.congr (Filter.Eventually.of_forall fun x => ?_)
  apply congrArg f
  calc
    Complex.I * ((sigma : ℂ) + ((-x : ℝ) : ℂ) * Complex.I) =
        Complex.I * (sigma : ℂ) + (-((x : ℂ))) * (Complex.I * Complex.I) := by
      push_cast
      ring
    _ = (x : ℂ) + (sigma : ℂ) * Complex.I := by
      rw [Complex.I_mul_I]
      ring

/-- Exact finite-pole transport of Suzuki's contour integrand.  Arbitrary-order poles contribute
their order-one Laurent coefficients, with inverse-Fourier normalization `i * sum residues`. -/
theorem horizontalIntegral_normalized_sub_eq_I_mul_sum_laurentCoeff_suzukiCanonical
    {omega c d : ℝ} (hcd : c < d) {P : Finset ℂ}
    (hPim : ∀ p ∈ P, c < p.im ∧ p.im < d)
    (g : DeningerMeyerStrongLogTarget) (r : ℝ)
    (hmero : ∀ p ∈ P,
      MeromorphicAt (suzukiCanonicalHankelContourIntegrand omega g r) p)
    (hoff : ∀ s : ℂ, c ≤ s.im → s.im ≤ d → s ∉ P →
      AnalyticAt ℂ (suzukiCanonicalHankelContourIntegrand omega g r) s)
    (htheta : HasStripPolyGrowthOffReal
      (fun s : ℂ => suzukiCanonicalTheta omega (Complex.I * s))) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          ((x : ℂ) + (c : ℂ) * Complex.I)) -
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          ((x : ℂ) + (d : ℂ) * Complex.I)) =
      Complex.I * ∑ p ∈ P,
        GaloisForLFunctions.HTGeometry.laurentCoeff
          (suzukiCanonicalHankelContourIntegrand omega g r) p (-1) := by
  let f := suzukiCanonicalHankelContourIntegrand omega g r
  let F := suzukiCanonicalRotatedHankelContourIntegrand omega g r
  have hrapid : HasStripRapidDecrease F :=
    hasStripRapidDecrease_suzukiCanonicalRotatedHankelContourIntegrand htheta g r
  have hF : F = fun s : ℂ => f (Complex.I * s) := by rfl
  have hc : Integrable fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I) := by
    apply integrable_horizontal_of_rotated_stripRapidDecrease hcd.le (Or.inl rfl) hPim hoff
    simpa only [hF] using hrapid
  have hd : Integrable fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I) := by
    apply integrable_horizontal_of_rotated_stripRapidDecrease hcd.le (Or.inr rfl) hPim hoff
    simpa only [hF] using hrapid
  let T : ℕ → ℝ := fun n => (n : ℝ)
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_natCast_atTop_atTop
  have habs : Tendsto (fun n : ℕ => |T n|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp hT
  have habsneg : Tendsto (fun n : ℕ => |-T n|) atTop atTop := by
    simpa only [abs_neg] using habs
  have hrightH : Tendsto (fun n => HIntegral F c d (-T n)) atTop (nhds 0) :=
    tendsto_hIntegral_of_stripRapidDecrease hrapid habsneg
  have hleftH : Tendsto (fun n => HIntegral F c d (T n)) atTop (nhds 0) :=
    tendsto_hIntegral_of_stripRapidDecrease hrapid habs
  have hright : Tendsto (fun n => VIntegral f (T n) c d) atTop (nhds 0) := by
    have heq : (fun n => VIntegral f (T n) c d) =
        (fun n => Complex.I * HIntegral F c d (-T n)) := by
      funext n
      rw [vIntegral_eq_I_mul_hIntegral_quarterTurn]
      rw [← hF]
    rw [heq]
    simpa only [mul_zero] using hrightH.const_mul Complex.I
  have hleft : Tendsto (fun n => VIntegral f (-(T n)) c d) atTop (nhds 0) := by
    have heq : (fun n => VIntegral f (-(T n)) c d) =
        (fun n => Complex.I * HIntegral F c d (T n)) := by
      funext n
      rw [vIntegral_eq_I_mul_hIntegral_quarterTurn]
      rw [← hF]
      simp
    rw [heq]
    simpa only [mul_zero] using hleftH.const_mul Complex.I
  simpa only [f] using
    GaloisForLFunctions.HTGeometry.horizontalIntegral_normalized_sub_eq_I_mul_sum_laurentCoeff_of_vertical_tendsto_seq
      hcd hPim hmero hoff hc hd hT hright hleft

end

end RHTower
