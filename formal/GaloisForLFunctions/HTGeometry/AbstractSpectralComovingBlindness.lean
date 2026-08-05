import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingMass

/-!
# Blindness and charge recovery at co-moving mass

Co-moving trace boundedness cannot force spectral reality: it is automatic for every admissible
family whose height floor is at least `1/2`.  A concrete conjugate two-point family with nonzero
displacement makes this logical obstruction explicit.

The obstruction exposes a positive invariant.  Although unscaled displacement vanishes at large
mass, its first mass rescaling recovers the conserved charge `R J`.  Quantitatively,

`a * |a K - R J| ≤ R * |R J|`,

where `R+iJ` is the original point and `M+iK` its mass image.  Thus fixed-aperture recovery cannot
use unscaled cone values alone; it must retain a first aperture jet or an equivalent charge
normalization.
-/

open Complex

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- **Quantitative first-aperture-jet recovery.**  Rescaling the mass displacement by `a` recovers
the conserved charge with an explicit error of order `1/a`. -/
theorem mass_rescaled_im_error
    {a : ℝ} (ha : 1 / 2 ≤ a) (hbase : 1 / 2 ≤ F.base) (i : ι) :
    a * |a * ((F.mass ha).pt i).im - (F.pt i).re * (F.pt i).im| ≤
      (F.pt i).re * |(F.pt i).re * (F.pt i).im| := by
  have hM : a < ((F.mass ha).pt i).re := F.lt_re_mass_of_base_half ha hbase i
  have hMpos : 0 < ((F.mass ha).pt i).re := lt_trans (by linarith : 0 < a) hM
  have hRpos : 0 < (F.pt i).re := F.re_pos i
  have hMle : ((F.mass ha).pt i).re ≤ (F.pt i).re + a := by
    simpa only [mass_pt, csqrt_re] using F.csqrtRe_massArg_le_add ha i
  have hgap0 : 0 ≤ ((F.mass ha).pt i).re - a := by linarith
  have hgap : ((F.mass ha).pt i).re - a ≤ (F.pt i).re := by linarith
  have hprod := F.re_mul_im_mass ha i
  have hprodAbs :
      ((F.mass ha).pt i).re * |((F.mass ha).pt i).im| =
        (F.pt i).re * |(F.pt i).im| := by
    have habs := congrArg abs hprod
    simpa only [abs_mul, abs_of_pos hMpos, abs_of_pos hRpos] using habs
  have hdiff :
      |a * ((F.mass ha).pt i).im - (F.pt i).re * (F.pt i).im| =
        (((F.mass ha).pt i).re - a) * |((F.mass ha).pt i).im| := by
    rw [← hprod]
    calc
      |a * ((F.mass ha).pt i).im -
          ((F.mass ha).pt i).re * ((F.mass ha).pt i).im| =
          |a - ((F.mass ha).pt i).re| * |((F.mass ha).pt i).im| := by
            rw [← sub_mul, abs_mul]
      _ = (((F.mass ha).pt i).re - a) * |((F.mass ha).pt i).im| := by
        rw [abs_sub_comm, abs_of_nonneg hgap0]
  have hcoef :
      a * (((F.mass ha).pt i).re - a) ≤
        ((F.mass ha).pt i).re * (F.pt i).re := by
    exact mul_le_mul hM.le hgap hgap0 hMpos.le
  calc
    a * |a * ((F.mass ha).pt i).im - (F.pt i).re * (F.pt i).im| =
        (a * (((F.mass ha).pt i).re - a)) * |((F.mass ha).pt i).im| := by
      rw [hdiff]
      ring
    _ ≤ (((F.mass ha).pt i).re * (F.pt i).re) *
        |((F.mass ha).pt i).im| :=
      mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    _ = (F.pt i).re *
        (((F.mass ha).pt i).re * |((F.mass ha).pt i).im|) := by ring
    _ = (F.pt i).re * ((F.pt i).re * |(F.pt i).im|) := by rw [hprodAbs]
    _ = (F.pt i).re * |(F.pt i).re * (F.pt i).im| := by
      rw [abs_mul, abs_of_pos hRpos]

end AbstractSpectralFamily

/-! ## An explicit nonreal family inside the co-moving bounded cone -/

/-- The conjugate pair `1 ± i/4`, as an admissible abstract spectral family. -/
def offRealPairFamily : AbstractSpectralFamily Bool where
  pt := fun b => if b then (1 : ℂ) + (1 / 4 : ℂ) * I else (1 : ℂ) - (1 / 4 : ℂ) * I
  inv := Equiv.swap true false
  base := 1
  base_pos := by norm_num
  base_le := by
    intro b
    cases b <;> norm_num [Complex.mul_re]
  abs_im_lt := by
    intro b
    cases b <;> norm_num [Complex.mul_im, abs_of_nonneg, abs_of_neg]
  summable_weight := by
    intro σ hσ
    exact Summable.of_finite
  shell_finite := by
    intro R
    exact Set.toFinite _
  conj_stable := by
    intro b
    cases b <;>
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Complex.ext_iff,
        Complex.mul_re, Complex.mul_im]

theorem offRealPairFamily_base_half : 1 / 2 ≤ offRealPairFamily.base := by
  norm_num [offRealPairFamily]

/-- The explicit countermodel is genuinely off the real axis. -/
theorem offRealPairFamily_nonreal : (offRealPairFamily.pt true).im ≠ 0 := by
  norm_num [offRealPairFamily, Complex.mul_im]

/-- Minimal aperture containing vertical time. -/
def canonicalComovingMass (u : ℝ) : ℝ := |u| + 1 / 2

theorem canonicalComovingMass_half (u : ℝ) : 1 / 2 ≤ canonicalComovingMass u := by
  unfold canonicalComovingMass
  linarith [abs_nonneg u]

theorem abs_le_canonicalComovingMass (u : ℝ) : |u| ≤ canonicalComovingMass u := by
  unfold canonicalComovingMass
  linarith

/-- **Sharp no-go countermodel.**  A nonreal conjugate spectrum obeys the full co-moving bound at
every vertical time.  Therefore no implication from this bound alone to spectral reality exists. -/
theorem offRealPairFamily_comoving_bound {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖(offRealPairFamily.mass (canonicalComovingMass_half u)).traceC
        ((σ : ℂ) + u * I)‖ ≤
      offRealPairFamily.traceReal (σ - 1 / 2) :=
  offRealPairFamily.norm_mass_traceC_le_comoving
    (canonicalComovingMass_half u) offRealPairFamily_base_half
    (abs_le_canonicalComovingMass u) hσ

end

end HTGeometry
