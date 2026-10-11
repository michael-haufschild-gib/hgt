import GaloisForLFunctions.RHTower.PaperEGCCompleteCorrection

/-!
# Exact source landing of the complete EGC correction

The uniformly summable copy row is the literal Xi logarithmic-derivative difference. On the
predeclared negative imaginary source ray it is exactly the existing continued prime--Gamma
diagonal extractor. The source points and shifts are fixed without consulting any Xi zero.
-/

namespace RHTower

noncomputable section
open Filter
open scoped Topology BigOperators

/-- Complete copy summation agrees with the exact Xi log-derivative divided difference. -/
theorem paperEGCCompleteCorrection_eq_logDeriv (eps x : PaperEGCSmallParameter) (t : ℝ) :
    paperEGCCompleteCorrection eps x t =
      (((eps : ℝ) : ℂ) / 2) *
        (logDeriv XiC ((((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) + ((eps : ℝ) : ℂ)) -
          logDeriv XiC ((((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((eps : ℝ) : ℂ))) := by
  let w : ℂ := ((x : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hp : XiC (w + ((eps : ℝ) : ℂ)) ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h
    apply paperEGC_line_minus_ne_zero eps x t q
    rw [hq]
    dsimp only [w]
    ring
  have hm : XiC (w - ((eps : ℝ) : ℂ)) ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h
    apply paperEGC_line_plus_ne_zero eps x t q
    rw [hq]
    dsimp only [w]
    ring
  rw [logDeriv_XiC_eq_relativeResolventTrace hp, logDeriv_XiC_eq_relativeResolventTrace hm,
    xiRelativeResolventTrace, xiRelativeResolventTrace,
    ← (summable_xiRelativeResolventTerm hp).tsum_sub (summable_xiRelativeResolventTerm hm),
    ← tsum_mul_left]
  unfold paperEGCCompleteCorrection
  apply tsum_congr
  intro q
  change -((eps : ℝ) : ℂ) / (2 * (xiSpectralPoint q - w - ((eps : ℝ) : ℂ))) +
    ((eps : ℝ) : ℂ) / (2 * (xiSpectralPoint q - w + ((eps : ℝ) : ℂ))) =
    (((eps : ℝ) : ℂ) / 2) *
      ((xiSpectralPoint q)⁻¹ - (xiSpectralPoint q - (w + ((eps : ℝ) : ℂ)))⁻¹ -
        ((xiSpectralPoint q)⁻¹ - (xiSpectralPoint q - (w - ((eps : ℝ) : ℂ)))⁻¹))
  rw [show xiSpectralPoint q - (w + ((eps : ℝ) : ℂ)) =
    xiSpectralPoint q - w - ((eps : ℝ) : ℂ) by ring,
    show xiSpectralPoint q - (w - ((eps : ℝ) : ℂ)) =
    xiSpectralPoint q - w + ((eps : ℝ) : ℂ) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Predeclared source observations whose Xi coordinates lie in the Euler half-plane. -/
def paperEGCSourceRayPoint (x : PaperEGCSmallParameter) (m : ℕ) : ℂ :=
  ((x : ℝ) : ℂ) + (-((m : ℝ) + 1) : ℂ) * Complex.I

/-- Every real shift of the source ray is admissible independently of the divisor. -/
theorem paperEGCSourceRayPoint_admissible_shift (x : PaperEGCSmallParameter) (m : ℕ) (r : ℝ) :
    XiExplicitAdmissible (paperEGCSourceRayPoint x m + (r : ℂ)) := by
  apply XiExplicitAdmissible_of_one_lt_re
  norm_num [paperEGCSourceRayPoint, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- The full correction is the native source-only extractor at every prescribed ray point. -/
theorem paperEGCCompleteCorrection_eq_sourceExtractor (n m : ℕ) (x : PaperEGCSmallParameter) :
    paperEGCCompleteCorrection (paperEGCScale n) x (-((m : ℝ) + 1)) =
      centeredPrimeArchRealShiftDiagonalExtractor (paperEGCSourceRayPoint x m) n := by
  have hp := paperEGCSourceRayPoint_admissible_shift x m ((n : ℝ) + 1)⁻¹
  have hm := paperEGCSourceRayPoint_admissible_shift x m (-((n : ℝ) + 1)⁻¹)
  rw [paperEGCCompleteCorrection_eq_logDeriv, centeredPrimeArchRealShiftDiagonalExtractor]
  simp only [one_div, Complex.ofReal_neg, ← sub_eq_add_neg] at hp hm ⊢
  rw [continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hp,
    continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hm]
  simp only [paperEGCScale, paperEGCSourceRayPoint, Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]

/-- A source bound paid by the full native reciprocal-square mass, at every ray point. -/
theorem norm_paperEGCSourceExtractor_le (n m : ℕ) (x : PaperEGCSmallParameter) :
    ‖centeredPrimeArchRealShiftDiagonalExtractor (paperEGCSourceRayPoint x m) n‖ ≤
      (8 * (paperEGCScale n : ℝ)^2) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖^2 := by
  rw [← paperEGCCompleteCorrection_eq_sourceExtractor]
  exact norm_paperEGCCompleteCorrection_le _ _ _

/-- The actual source extractor tends to zero along the prescribed Euler-safe ray. -/
theorem tendsto_paperEGCSourceExtractor (n : ℕ) (x : PaperEGCSmallParameter) :
    Tendsto (fun m => centeredPrimeArchRealShiftDiagonalExtractor
      (paperEGCSourceRayPoint x m) n) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => -((m : ℝ) + 1)) atTop (Bornology.cobounded ℝ) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    have hn (m : ℕ) : |(m : ℝ) + 1| = (m : ℝ) + 1 := abs_of_nonneg (by positivity)
    simpa only [norm_neg, Real.norm_eq_abs, hn] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)))
  have h := (tendsto_paperEGCCompleteCorrection_cobounded (paperEGCScale n) x).comp ht
  change Tendsto (fun m : ℕ => paperEGCCompleteCorrection (paperEGCScale n) x
    (-((m : ℝ) + 1))) atTop (𝓝 0) at h
  simpa only [paperEGCCompleteCorrection_eq_sourceExtractor] using h

end
end RHTower
