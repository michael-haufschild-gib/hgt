import GaloisForLFunctions.RHTower.HedenmalmShiftedClosedWeightedDerivative

/-!
# Actual cokernel line of every translated Hedenmalm derivative

The source conormal `k(x) exp(-i conj(α)x)` belongs to the weighted Hilbert space for every
complex parameter because the theta source has all exponential moments.  This file packages that
function as an actual Hilbert vector before identifying the full translated range.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource
  HedenmalmFredholmRange

private abbrev H := Lp ℂ 2 unitIntervalMeasure

private abbrev HS := SourceSpace thetaSource

private abbrev sourceMeasure : Measure ℝ :=
  volume.withDensity (realDensity (sourceWeight thetaSource))

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

theorem cokernelVector_eq_k_mul_sourceChar (α : ℂ) (x : ℝ) :
    cokernelVector thetaSource α x =
      (thetaSource.k x : ℂ) * sourceChar (-(starRingEnd ℂ) α) x := by
  rw [cokernelVector, sourceChar]
  congr 2
  ring

theorem memLp_thetaCokernelSource (α : ℂ) :
    MemLp (cokernelVector thetaSource α) 2 sourceMeasure := by
  rw [sourceMeasure]
  apply (memLp_two_withDensity_iff (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mpr
  let z : ℂ := -(starRingEnd ℂ) α
  let q : ℝ → ℂ := fun x =>
    ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x
  have hqcont : Continuous q :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp thetaSource.continuous_k)).mul
        (continuous_sourceChar z)
  have hq : MemLp q 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq_norm hqcont.aestronglyMeasurable).mpr
    refine (HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource
      (-2 * α.im)).congr ?_
    filter_upwards with x
    rw [q, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_sourceChar, mul_pow,
      Real.sq_sqrt (thetaSource.pos_k x).le, thetaSource_k]
    have hzIm : z.im = α.im := by
      simp [z]
    rw [hzIm]
    have hexp : Real.exp (-α.im * x) ^ 2 =
        Real.exp ((-2 * α.im) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    ring
  have hfun : (fun x => sqrtWeight (sourceWeight thetaSource) x *
      cokernelVector thetaSource α x) = q := by
    funext x
    have hk : 0 < thetaSource.k x := thetaSource.pos_k x
    have hsqrt : Real.sqrt (thetaSource.k x) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
    have hsqrtC : ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hsqrt
    have hsw : sqrtWeight (sourceWeight thetaSource) x =
        (((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) := by
      rw [sqrtWeight]
      norm_cast
      rw [show sourceWeight thetaSource x = (thetaSource.k x)⁻¹ from rfl,
        Real.sqrt_inv]
    rw [cokernelVector_eq_k_mul_sourceChar, hsw]
    change ((((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) *
        ((thetaSource.k x : ℝ) : ℂ)) * sourceChar z x = q x
    rw [q]
    congr 1
    push_cast
    field_simp [hsqrtC]
    exact_mod_cast (Real.sq_sqrt hk.le).symm
  rw [hfun]
  exact hq

/-- Source-space representative of the translated cokernel conormal. -/
def thetaCokernelSourceVector (α : ℂ) : HS :=
  (memLp_thetaCokernelSource α).toLp (cokernelVector thetaSource α)

theorem thetaCokernelSourceVector_ae (α : ℂ) :
    (thetaCokernelSourceVector α : ℝ → ℂ) =ᵐ[sourceMeasure]
      cokernelVector thetaSource α :=
  (memLp_thetaCokernelSource α).coeFn_toLp

theorem thetaCokernelSourceVector_ne_zero (α : ℂ) :
    thetaCokernelSourceVector α ≠ 0 := by
  intro hzero
  have hzeroWeighted :
      ((0 : HS) : ℝ → ℂ) =ᵐ[sourceMeasure] fun _ => 0 :=
    Lp.coeFn_zero ℂ 2 sourceMeasure
  have hzeroAEμ :
      cokernelVector thetaSource α =ᵐ[sourceMeasure] fun _ => 0 := by
    have hrep := thetaCokernelSourceVector_ae α
    rw [hzero] at hrep
    exact hrep.symm.trans hzeroWeighted
  have hzeroAE :
      cokernelVector thetaSource α =ᵐ[(volume : Measure ℝ)] fun _ => 0 :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using hzeroAEμ)
  have hcont : Continuous (cokernelVector thetaSource α) := by
    rw [show cokernelVector thetaSource α = fun x =>
      (thetaSource.k x : ℂ) * sourceChar (-(starRingEnd ℂ) α) x by
        funext x
        exact cokernelVector_eq_k_mul_sourceChar α x]
    exact (Complex.continuous_ofReal.comp thetaSource.continuous_k).mul
      (continuous_sourceChar (-(starRingEnd ℂ) α))
  have hall : cokernelVector thetaSource α = fun _ : ℝ => 0 :=
    Measure.eq_of_ae_eq hzeroAE hcont continuous_zero
  have hzeroAt := congrFun hall 0
  rw [cokernelVector] at hzeroAt
  exact (mul_ne_zero (by exact_mod_cast (thetaSource.pos_k 0).ne')
    (Complex.exp_ne_zero _)) hzeroAt

/-- Quantile-space vector spanning the translated cokernel line. -/
def thetaCokernelVector (α : ℂ) : H :=
  quantileUnitary thetaSource (thetaCokernelSourceVector α)

theorem thetaCokernelVector_ne_zero (α : ℂ) : thetaCokernelVector α ≠ 0 := by
  intro hzero
  apply thetaCokernelSourceVector_ne_zero α
  apply (quantileUnitary thetaSource).injective
  simpa [thetaCokernelVector] using hzero

end HedenmalmClosedWeightedDerivative

end

end RHTower
