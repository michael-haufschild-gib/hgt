import GaloisForLFunctions.RHTower.GaussPrimeScaleFourier
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The prime block as a bounded operator on `L²(ℝ/ℤ)`

The prime-scale amplitude `b_p(x) = p^{(1-x)/2}` is a bounded measurable function on the circle:
its values lie in `[1, √p]`.  Multiplication by it is therefore a bounded operator on
`L²(ℝ/ℤ)` of norm at most `√p` — the block `B_p` of the quasi-inner decomposition.

Measurability is the composition of the measurable equivalence `AddCircle 1 ≃ᵐ (0, 1]` with the
continuous representative; the bound is monotonicity of `exp` on the period.
-/

namespace RHTower

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Continuity, measurability and the uniform bound -/

theorem continuous_gaussPrimeScale (p : ℝ) : Continuous (gaussPrimeScale p) := by
  unfold gaussPrimeScale
  fun_prop

theorem measurable_gaussPrimeScaleCircle (p : ℝ) :
    Measurable (gaussPrimeScaleCircle p) := by
  rw [gaussPrimeScaleCircle, AddCircle.liftIoc]
  refine Measurable.comp ?_ (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable
  exact ((Complex.measurable_ofReal.comp
    (continuous_gaussPrimeScale p).measurable).comp measurable_subtype_coe)

theorem gaussPrimeScale_le_sqrt {p : ℝ} (hp : 1 < p) {x : ℝ} (hx : 0 ≤ x) :
    gaussPrimeScale p x ≤ Real.sqrt p := by
  have hppos : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hle : (1 - x) * Real.log p / 2 ≤ Real.log p / 2 := by
    have : (1 - x) * Real.log p ≤ 1 * Real.log p :=
      mul_le_mul_of_nonneg_right (by linarith) hlog.le
    linarith
  rw [gaussPrimeScale, ← GaloisForLFunctions.RHTower.exp_log_div_two p hppos]
  exact Real.exp_le_exp.mpr hle

theorem norm_gaussPrimeScaleCircle_le {p : ℝ} (hp : 1 < p) (z : AddCircle (1 : ℝ)) :
    ‖gaussPrimeScaleCircle p z‖ ≤ Real.sqrt p := by
  have hmem := (AddCircle.equivIoc (1 : ℝ) 0 z).2
  have hval : gaussPrimeScaleCircle p z =
      ((gaussPrimeScale p ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) :
        ℝ) : ℂ) := rfl
  rw [hval, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gaussPrimeScale_pos p _)]
  exact gaussPrimeScale_le_sqrt hp (le_of_lt hmem.1)

/-! ## The prime block -/

/-- The prime block `B_p`: multiplication by the prime-scale amplitude on `L²(ℝ/ℤ)`. -/
def gaussPrimeScaleBlock {p : ℝ} (hp : 1 < p) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MeasureTheory.lpBoundedMulCLM (measurable_gaussPrimeScaleCircle p)
    (Real.sqrt_nonneg p) (norm_gaussPrimeScaleCircle_le hp)

/-- The prime block acts by pointwise multiplication. -/
theorem gaussPrimeScaleBlock_coeFn {p : ℝ} (hp : 1 < p)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (gaussPrimeScaleBlock hp f : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => gaussPrimeScaleCircle p z * (f : _ → ℂ) z :=
  MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ f

/-- **The prime block is a contraction up to `√p`.** -/
theorem norm_gaussPrimeScaleBlock_le {p : ℝ} (hp : 1 < p) :
    ‖gaussPrimeScaleBlock hp‖ ≤ Real.sqrt p :=
  MeasureTheory.norm_lpBoundedMulCLM_le _ _ _

/-! ## The Fourier side of the prime block -/

theorem fourierCoeff_congr_ae {f g : AddCircle (1 : ℝ) → ℂ}
    (h : f =ᵐ[AddCircle.haarAddCircle] g) (n : ℤ) :
    fourierCoeff f n = fourierCoeff g n := by
  rw [fourierCoeff, fourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- **The prime block on a Fourier mode.**  Multiplying the `n`th exponential monomial by the
prime-scale amplitude shifts the Fourier index: the `l`th coefficient is `b̂(l - n)`. -/
theorem fourierCoeff_gaussPrimeScaleBlock_fourierLp {p : ℝ} (hp : 1 < p) (n l : ℤ) :
    fourierCoeff
        ((gaussPrimeScaleBlock hp (fourierLp 2 n) : AddCircle (1 : ℝ) → ℂ)) l
      = gaussPrimeScaleFourierCoefficient p (l - n) := by
  have hae : (gaussPrimeScaleBlock hp (fourierLp 2 n) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => fourier n z * gaussPrimeScaleCircle p z := by
    filter_upwards [gaussPrimeScaleBlock_coeFn hp (fourierLp 2 n),
      coeFn_fourierLp (T := (1 : ℝ)) 2 n] with z h1 h2
    rw [h1, h2, mul_comm]
  rw [fourierCoeff_congr_ae hae l,
    GaloisForLFunctions.fourierCoeff_fourier_mul (gaussPrimeScaleCircle p) l n,
    fourierCoeff_gaussPrimeScaleCircle hp]

end

end RHTower
