import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity
import GaloisForLFunctions.RHTower.SuzukiDonoghueHerglotzTransform

/-!
# The Herglotz representation on the half plane

An anti-Herglotz function on the upper half plane has a nonnegative harmonic negated imaginary part,
so the disc representation applies once the half plane is carried to the disc.

No conformal invariance of harmonicity is needed.  The function to be represented is the imaginary
part of an analytic function, and composing with the inverse Cayley map — itself analytic on the
disc — produces the imaginary part of an analytic function again.  Harmonicity of the composite is
therefore the same one-line fact as harmonicity of the original, not a transfer theorem.
-/

namespace GaloisForLFunctions.RHTower

open Complex InnerProductSpace Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

/-- A point of the open unit disc is not the pole of the inverse Cayley map. -/
theorem ne_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rw [mem_ball_zero_iff] at hw
  intro h
  rw [h] at hw
  simp at hw

theorem normSq_lt_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : Complex.normSq w < 1 := by
  rw [mem_ball_zero_iff] at hw
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg w]

/-- The inverse Cayley map is analytic off its pole. -/
theorem analyticAt_herglotzOfCayley {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ herglotzOfCayley w := by
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have heq : herglotzOfCayley = fun z : ℂ => Complex.I * (1 + z) / (1 - z) := rfl
  rw [heq]
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hden

/-- **The pulled-back function is harmonic and nonnegative.**  It is the negated imaginary part of an
analytic function, namely the anti-Herglotz function composed with the inverse Cayley map. -/
theorem harmonicOnNhd_neg_im_comp {q : ℂ → ℂ}
    (hq : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ q z) :
    HarmonicOnNhd (fun w => -(q (herglotzOfCayley w)).im) (ball (0 : ℂ) 1) := by
  intro w hw
  have hcomp : AnalyticAt ℂ (fun z => q (herglotzOfCayley z)) w :=
    (hq _ (im_herglotzOfCayley_pos (normSq_lt_one_of_mem_ball hw))).comp
      (analyticAt_herglotzOfCayley (ne_one_of_mem_ball hw))
  exact hcomp.harmonicAt_im.neg

/-- **The Herglotz representation on the half plane, in disc coordinates.**  For an analytic
anti-Herglotz function on the upper half plane there is a finite positive measure on the circle of
angles whose Poisson integral is the negated imaginary part. -/
theorem exists_poissonRepresentation_antiHerglotz {q : ℂ → ℂ}
    (hq : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ q z)
    (hsign : ∀ z : ℂ, 0 < z.im → (q z).im ≤ 0) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = -(q (herglotzOfCayley w)).im :=
  exists_poissonRepresentation (harmonicOnNhd_neg_im_comp hq)
    fun _ hw => neg_nonneg.mpr
      (hsign _ (im_herglotzOfCayley_pos (normSq_lt_one_of_mem_ball hw)))

/-- **The Herglotz representation on the half plane.**  The same measure represents the negated
imaginary part at every point of the upper half plane, the point being reached through the Cayley
transform. -/
theorem exists_poissonRepresentation_upperHalfPlane {q : ℂ → ℂ}
    (hq : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ q z)
    (hsign : ∀ z : ℂ, 0 < z.im → (q z).im ≤ 0) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ m : ℂ, 0 < m.im →
        ∫ θ, poissonKernel 0 (cayleyOfHerglotz m) (circleMap 0 1 θ) ∂ν = -(q m).im := by
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation_antiHerglotz hq hsign
  refine ⟨ν, hfin, fun m hm => ?_⟩
  have hmem : cayleyOfHerglotz m ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    have h := normSq_cayleyOfHerglotz_lt_one hm
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (cayleyOfHerglotz m)]
  rw [hrep _ hmem, herglotzOfCayley_cayleyOfHerglotz (cayleyOfHerglotz_denom_ne_zero hm)]

end GaloisForLFunctions.RHTower
