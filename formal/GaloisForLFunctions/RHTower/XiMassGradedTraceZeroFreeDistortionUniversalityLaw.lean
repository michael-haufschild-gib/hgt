import GaloisForLFunctions.RHTower.XiMassFaithfulTransfer
import GaloisForLFunctions.RHTower.XiSpectralFamilyGradedOnLine

/-!
# Mass-graded Xi trace zero-free distortion universality

The exponential type of the mass-shifted Xi trace retains quantitative transverse information about
the original Xi divisor.  Mass shifting contracts displacement, so an original zero-free chamber
implies a trace-growth bound with the same exponent.  Conversely, the faithful mass transfer turns
any such exponent into an original zero-free chamber with explicit squared loss `(9 + a²) / 9`.

This extends the zero-exponent mass line-bound criterion to every nonnegative exponential type.
-/

open Complex

namespace RHTower

noncomputable section

/-- The mass-shifted Xi trace has exponential type at most `lam` on some strict-right vertical
line. -/
def xiMassTraceLineGrowth {a : ℝ} (ha : 1 / 2 ≤ a) (lam : ℝ) : Prop :=
  ∃ σ C : ℝ, 0 < σ ∧
    ∀ x : ℝ,
      ‖(xiMassFamily ha).traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
        C * Real.exp (lam * |x|)

/-- Mass shifting contracts the transverse displacement of every Xi divisor point. -/
theorem abs_im_xiMassFamily_le_abs_im_xiSpectralPoint
    {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    |((xiMassFamily ha).pt q).im| ≤ |(xiSpectralPoint q).im| := by
  rw [xiMassFamily_pt_eq_mass_pt ha q]
  have h := xiPoissonAbstract.abs_csqrtIm_massArg_le ha q
  rw [HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_im]
  rw [xiPoissonAbstract_pt, xiPoissonPoint] at h
  split_ifs at h with hc
  · exact h
  · simpa only [Complex.neg_im, abs_neg] using h

/-- An original Xi zero-free chamber supplies the same exponential-type bound for every
mass-shifted trace. -/
theorem xiMassTraceLineGrowth_of_xiZeroStrip
    {a lam : ℝ} (ha : 1 / 2 ≤ a) (hlam : 0 ≤ lam)
    (hzero : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ lam) :
    xiMassTraceLineGrowth ha lam := by
  apply ((xiMassFamily ha).abs_im_le_iff_exists_line_growth hlam).mp
  intro q
  exact le_trans
    (abs_im_xiMassFamily_le_abs_im_xiSpectralPoint ha q) (hzero q)

/-- A mass-shifted trace exponent returns an explicit zero-free chamber for the original Xi
divisor. -/
theorem nine_mul_sq_im_xiSpectralPoint_le_of_xiMassTraceLineGrowth
    {a lam : ℝ} (ha : 1 / 2 ≤ a) (hlam : 0 ≤ lam)
    (hgrowth : xiMassTraceLineGrowth ha lam) (q : XiZeroCopy) :
    9 * (xiSpectralPoint q).im ^ (2 : ℕ) ≤
      (9 + a ^ (2 : ℕ)) * lam ^ (2 : ℕ) := by
  obtain ⟨σ, C, hσ, hline⟩ := hgrowth
  have hmass :=
    (xiMassFamily ha).abs_im_le_of_line_growth_all
      hσ hlam hline q
  have hmasssq :
      ((xiMassFamily ha).pt q).im ^ (2 : ℕ) ≤ lam ^ (2 : ℕ) := by
    rw [← sq_abs ((xiMassFamily ha).pt q).im]
    exact (sq_le_sq₀ (abs_nonneg _) hlam).mpr hmass
  calc
    9 * (xiSpectralPoint q).im ^ (2 : ℕ) ≤
        (9 + a ^ (2 : ℕ)) * ((xiMassFamily ha).pt q).im ^ (2 : ℕ) :=
      nine_mul_sq_im_xiSpectralPoint_le ha q
    _ ≤ (9 + a ^ (2 : ℕ)) * lam ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hmasssq (by positivity)

/-- **Mass-graded Xi zero-free distortion law.**  Original transverse width bounds
mass-trace exponential type without loss; mass-trace type bounds original squared width with the
universal condition number `(9 + a²) / 9`. -/
theorem xiMass_gradedTrace_zeroFreeDistortionUniversality
    {a lam : ℝ} (ha : 1 / 2 ≤ a) (hlam : 0 ≤ lam) :
    ((∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ lam) →
      xiMassTraceLineGrowth ha lam) ∧
    (xiMassTraceLineGrowth ha lam →
      ∀ q : XiZeroCopy,
        9 * (xiSpectralPoint q).im ^ (2 : ℕ) ≤
          (9 + a ^ (2 : ℕ)) * lam ^ (2 : ℕ)) := by
  exact
    ⟨xiMassTraceLineGrowth_of_xiZeroStrip ha hlam,
      fun h q =>
        nine_mul_sq_im_xiSpectralPoint_le_of_xiMassTraceLineGrowth
          ha hlam h q⟩

end

end RHTower
