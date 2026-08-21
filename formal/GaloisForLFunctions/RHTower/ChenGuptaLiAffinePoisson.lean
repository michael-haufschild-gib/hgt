import GaloisForLFunctions.RHTower.ChenGuptaLiRamanujanFourier
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A positive dyadic length used by CGL's smoothed character sums. -/
structure CGLPositiveLength where
  value : ℕ
  positive : 0 < value

def cglAffinePhysicalScale (N : CGLPositiveLength) (Q : CGLPositiveModulus) : ℝ :=
  (Q.value : ℝ) / N.value

def cglAffineFourierScale (N : CGLPositiveLength) (Q : CGLPositiveModulus) : ℝ :=
  (N.value : ℝ) / Q.value

theorem cglAffinePhysicalScale_pos (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    0 < cglAffinePhysicalScale N Q := by
  exact div_pos (by exact_mod_cast Q.positive) (by exact_mod_cast N.positive)

theorem cglAffineFourierScale_pos (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    0 < cglAffineFourierScale N Q := by
  exact div_pos (by exact_mod_cast N.positive) (by exact_mod_cast Q.positive)

def cglAffineDilation (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)

/-- The Schwartz input on the integer lattice whose values are
`f ((a + qk) / N)`. -/
def cglAffineResidueSchwartz (f : SchwartzMap ℝ ℂ) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (a : ZMod Q.value) : SchwartzMap ℝ ℂ :=
  SchwartzMap.translateCLM ℂ ((a.val : ℝ) / Q.value)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (cglAffineDilation (cglAffinePhysicalScale N Q) (cglAffinePhysicalScale_pos N Q).ne') f)

@[simp] theorem cglAffineResidueSchwartz_apply (f : SchwartzMap ℝ ℂ) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (a : ZMod Q.value) (x : ℝ) :
    cglAffineResidueSchwartz f N Q a x =
      f (((a.val : ℝ) + Q.value * x) / N.value) := by
  change f (((Q.value : ℝ) / N.value) * (x + (a.val : ℝ) / Q.value)) = _
  have hq : (Q.value : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Q.positive)
  have hn : (N.value : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt N.positive)
  congr 1
  field_simp
  ring

/-- Exact Fourier transform of the CGL affine residue-class input. -/
theorem cglAffineResidueSchwartz_fourier (f : SchwartzMap ℝ ℂ) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (a : ZMod Q.value) (ξ : ℝ) :
    𝓕 (cglAffineResidueSchwartz f N Q a : ℝ → ℂ) ξ =
      Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * ξ) : ℂ) * Complex.I) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * ξ)) := by
  change 𝓕 (fun x : ℝ =>
      f (cglAffinePhysicalScale N Q * (x + (a.val : ℝ) / Q.value))) ξ = _
  rw [GaloisForLFunctions.HTGeometry.fourierIntegral_comp_add_right
    (fun x : ℝ => f (cglAffinePhysicalScale N Q * x)) ((a.val : ℝ) / Q.value) ξ]
  have hfun : (fun x : ℝ => f (cglAffinePhysicalScale N Q * x)) =
      fun x : ℝ => f (x / cglAffineFourierScale N Q) := by
    funext x
    change f (((Q.value : ℝ) / N.value) * x) =
      f (x / ((N.value : ℝ) / Q.value))
    congr 1
    have hq : (Q.value : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Q.positive)
    have hn : (N.value : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt N.positive)
    field_simp [cglAffinePhysicalScale, cglAffineFourierScale]
  rw [hfun, GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div f
    (cglAffineFourierScale N Q) (cglAffineFourierScale_pos N Q) ξ]
  change Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * ξ) : ℂ) * Complex.I) *
      ((cglAffineFourierScale N Q : ℂ) *
        𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * ξ)) = _
  rfl

/-- Affine Poisson summation before rewriting its phase as a finite additive character. -/
theorem cglAffineResidue_tsum_eq_tsum_fourier (f : SchwartzMap ℝ ℂ)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (a : ZMod Q.value) :
    ∑' k : ℤ, f (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) =
      ∑' m : ℤ,
        Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * (m : ℝ)) : ℂ) * Complex.I) *
          ((cglAffineFourierScale N Q : ℂ) *
            𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ))) := by
  calc
    ∑' k : ℤ, f (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) =
        ∑' k : ℤ, cglAffineResidueSchwartz f N Q a (k : ℝ) := by
      apply tsum_congr
      intro k
      exact (cglAffineResidueSchwartz_apply f N Q a (k : ℝ)).symm
    _ = ∑' m : ℤ, 𝓕 (cglAffineResidueSchwartz f N Q a : ℝ → ℂ) (m : ℝ) := by
      simpa using cglSchwartz_tsum_eq_tsum_fourier (cglAffineResidueSchwartz f N Q a) 0
    _ = _ := by
      apply tsum_congr
      intro m
      exact cglAffineResidueSchwartz_fourier f N Q a (m : ℝ)

/-- The real Poisson phase is CGL's standard finite additive character. -/
theorem cglAffineFourierPhase_eq_stdAddChar (Q : CGLPositiveModulus)
    (a : ZMod Q.value) (m : ℤ) :
    Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * (m : ℝ)) : ℂ) * Complex.I) =
      ZMod.stdAddChar (((a.val : ℤ) * m : ℤ) : ZMod Q.value) := by
  rw [ZMod.stdAddChar_coe]
  congr 1
  have hq : (Q.value : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Q.positive)
  push_cast
  field_simp

theorem cglAffineFourierPhase_eq_stdAddChar_mul (Q : CGLPositiveModulus)
    (a : ZMod Q.value) (m : ℤ) :
    Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * (m : ℝ)) : ℂ) * Complex.I) =
      ZMod.stdAddChar (a * (m : ZMod Q.value)) := by
  rw [cglAffineFourierPhase_eq_stdAddChar]
  congr 1
  simp

/-- Affine Poisson summation with CGL's finite additive character. -/
theorem cglAffineResidue_tsum_eq_tsum_fourier_addChar (f : SchwartzMap ℝ ℂ)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (a : ZMod Q.value) :
    ∑' k : ℤ, f (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) =
      ∑' m : ℤ, ZMod.stdAddChar (a * (m : ZMod Q.value)) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ))) := by
  rw [cglAffineResidue_tsum_eq_tsum_fourier]
  apply tsum_congr
  intro m
  rw [cglAffineFourierPhase_eq_stdAddChar_mul]

/-- Schwartz Fourier samples on the integer lattice are summable. -/
theorem cglSchwartz_summable_fourier_int (f : SchwartzMap ℝ ℂ) :
    Summable fun m : ℤ => 𝓕 (f : ℝ → ℂ) (m : ℝ) := by
  refine summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) ?_
  simpa only [Real.norm_eq_abs] using
    ((𝓕 f).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite

/-- CGL's reduced-residue Poisson identity, with finite and infinite summation interchanged using
the proved Schwartz summability of every affine residue class. -/
theorem cglReducedResidue_tsum_eq_tsum_ramanujan (f : SchwartzMap ℝ ℂ)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
      ∑' k : ℤ, f (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) =
      ∑' m : ℤ, cglRamanujanAdditiveSum Q (m : ZMod Q.value) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ))) := by
  let F : ZMod Q.value → ℤ → ℂ := fun a m =>
    ZMod.stdAddChar (a * (m : ZMod Q.value)) *
      ((cglAffineFourierScale N Q : ℂ) *
        𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ)))
  have hsingle (a : ZMod Q.value) :
      ∑' k : ℤ, f (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) = ∑' m : ℤ, F a m := by
    exact cglAffineResidue_tsum_eq_tsum_fourier_addChar f N Q a
  simp_rw [hsingle]
  have hsum (a : ZMod Q.value) (ha : a ∈ Finset.univ.filter IsUnit) : Summable (F a) := by
    refine (cglSchwartz_summable_fourier_int (cglAffineResidueSchwartz f N Q a)).congr ?_
    intro m
    calc
      𝓕 (cglAffineResidueSchwartz f N Q a : ℝ → ℂ) (m : ℝ) =
          Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * (m : ℝ)) : ℂ) * Complex.I) *
            ((cglAffineFourierScale N Q : ℂ) *
              𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ))) :=
        cglAffineResidueSchwartz_fourier f N Q a (m : ℝ)
      _ = F a m := by
        rw [cglAffineFourierPhase_eq_stdAddChar_mul]
  rw [← Summable.tsum_finsetSum hsum]
  apply tsum_congr
  intro m
  unfold F cglRamanujanAdditiveSum
  rw [Finset.sum_mul]

/-- The same CGL identity with the reduced-residue sum expressed as a finite DFT. -/
theorem cglReducedResidue_tsum_eq_tsum_dftUnitIndicator (f : SchwartzMap ℝ ℂ)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
      ∑' k : ℤ, f (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) =
      ∑' m : ℤ, ZMod.dft (cglUnitResidueIndicator Q) (-(m : ZMod Q.value)) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ))) := by
  rw [cglReducedResidue_tsum_eq_tsum_ramanujan]
  apply tsum_congr
  intro m
  rw [cglRamanujanAdditiveSum_eq_dft_unitIndicator]

/-- CGL Lemma 4.4's literal `h₀=w²` kernel in the reduced-residue Poisson identity. -/
theorem cglSmoothBumpHZero_reducedResidue_tsum_eq_tsum_ramanujan
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
      ∑' k : ℤ,
        w.value (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) *
          w.value (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) =
      ∑' m : ℤ, cglRamanujanAdditiveSum Q (m : ZMod Q.value) *
        ((cglAffineFourierScale N Q : ℂ) *
          𝓕 (fun u => w.value u * w.value u)
            (cglAffineFourierScale N Q * (m : ℝ))) := by
  have h := cglReducedResidue_tsum_eq_tsum_ramanujan (cglSmoothBumpHZero w) N Q
  have hfun : (cglSmoothBumpHZero w : ℝ → ℂ) = fun u => w.value u * w.value u := by
    funext u
    rfl
  rw [hfun] at h
  simpa only [cglSmoothBumpHZero_apply] using h

end RHTower
