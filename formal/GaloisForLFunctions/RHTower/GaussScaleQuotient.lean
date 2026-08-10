import GaloisForLFunctions.RHTower.GaussAmplitudeClass
import GaloisForLFunctions.HTGeometry.PiecewiseExponentialAlgebra

/-!
# The intermediate stage of the principal step is a translate

The middle stage `B^(-2) T_δ B` of the telescoping identity is translation of a single
multiplication operator:

`B^(-2) (T_δ (B f)) = T_δ (M_(q_δ) f)`,   `q_δ(z) = b(z)·b(z+δ)^(-2)`.

Since translation leaves the modulus of every Fourier coefficient unchanged, the decay constant of
the intermediate stage is the decay constant of `q_δ · f`, and `q_δ` is a two-piece exponential
with the same breakpoint `1-δ` as the moving amplitude.  So the second hypothesis of the one-step
estimate never requires a refinement of the partition.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions

noncomputable section

/-! ## The scale quotient on the circle -/

/-- The scale quotient `q_δ(z) = b(z)·b(z+δ)^(-2)`. -/
def gaussScaleQuotientCircle (p : ℝ) (δ : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) → ℂ :=
  fun z => gaussPrimeScaleInvSqCircle p (z + δ) * gaussPrimeScaleCircle p z

theorem measurable_gaussScaleQuotientCircle (p : ℝ) (δ : AddCircle (1 : ℝ)) :
    Measurable (gaussScaleQuotientCircle p δ) :=
  ((measurable_gaussPrimeScaleInvSqCircle p).comp (measurable_add_const δ)).mul
    (measurable_gaussPrimeScaleCircle p)

theorem norm_gaussScaleQuotientCircle_le {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (z : AddCircle (1 : ℝ)) : ‖gaussScaleQuotientCircle p δ z‖ ≤ Real.sqrt p := by
  have hb := norm_gaussPrimeScaleCircle_le hp z
  have hi := norm_gaussPrimeScaleInvSqCircle_le hp (z + δ)
  rw [gaussScaleQuotientCircle, norm_mul]
  calc ‖gaussPrimeScaleInvSqCircle p (z + δ)‖ * ‖gaussPrimeScaleCircle p z‖
      ≤ 1 * Real.sqrt p := mul_le_mul hi hb (norm_nonneg _) zero_le_one
    _ = Real.sqrt p := one_mul _

/-- Multiplication by the scale quotient. -/
def gaussScaleQuotientBlock {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MeasureTheory.lpBoundedMulCLM (measurable_gaussScaleQuotientCircle p δ)
    (Real.sqrt_nonneg p) (norm_gaussScaleQuotientCircle_le hp δ)

theorem norm_gaussScaleQuotientBlock_le {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    ‖gaussScaleQuotientBlock hp δ‖ ≤ Real.sqrt p :=
  MeasureTheory.norm_lpBoundedMulCLM_le _ _ _

/-! ## The intermediate stage -/

/-- **The intermediate stage of the principal step is a translate of one multiplication
operator.** -/
theorem gaussPrimeScaleInvSqBlock_translate_gaussPrimeScaleBlock {p : ℝ} (hp : 1 < p)
    (δ : AddCircle (1 : ℝ)) (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrimeScaleInvSqBlock hp (gaussTranslationBlock δ (gaussPrimeScaleBlock hp f))
      = gaussTranslationBlock δ (gaussScaleQuotientBlock hp δ f) := by
  have h1 : (gaussPrimeScaleBlock hp f : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleCircle p z * (f : AddCircle (1 : ℝ) → ℂ) z :=
    gaussPrimeScaleBlock_coeFn hp f
  have h2 : (gaussTranslationBlock δ (gaussPrimeScaleBlock hp f) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleCircle p (z - δ) * (f : AddCircle (1 : ℝ) → ℂ) (z - δ) := by
    refine (coeFn_gaussTranslationBlock δ (gaussPrimeScaleBlock hp f)).trans ?_
    filter_upwards [ae_eq_comp_sub δ h1] with z hz
    exact hz
  have hL : (gaussPrimeScaleInvSqBlock hp
        (gaussTranslationBlock δ (gaussPrimeScaleBlock hp f)) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleInvSqCircle p z *
          (gaussPrimeScaleCircle p (z - δ) * (f : AddCircle (1 : ℝ) → ℂ) (z - δ)) := by
    refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).trans ?_
    filter_upwards [h2] with z hz
    rw [hz]
  have h3 : (gaussScaleQuotientBlock hp δ f : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussScaleQuotientCircle p δ z * (f : AddCircle (1 : ℝ) → ℂ) z :=
    MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ f
  have hR : (gaussTranslationBlock δ (gaussScaleQuotientBlock hp δ f) :
        AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussScaleQuotientCircle p δ (z - δ) * (f : AddCircle (1 : ℝ) → ℂ) (z - δ) := by
    refine (coeFn_gaussTranslationBlock δ (gaussScaleQuotientBlock hp δ f)).trans ?_
    filter_upwards [ae_eq_comp_sub δ h3] with z hz
    exact hz
  refine Lp.ext (hL.trans (Filter.EventuallyEq.trans ?_ hR.symm))
  filter_upwards with z
  rw [gaussScaleQuotientCircle, sub_add_cancel]
  ring

/-! ## The scale quotient is a two-piece exponential -/

theorem ofReal_exp_mul (α x : ℝ) :
    ((Real.exp (α * x) : ℝ) : ℂ) = Complex.exp ((α : ℂ) * (x : ℂ)) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Before the wrap the scale quotient is `p^(s-1/2)·e^{x·log p/2}`. -/
theorem gaussScaleQuotientCircle_of_lt {p : ℝ} {s x : ℝ}
    (hs0 : 0 ≤ s) (hx0 : 0 < x) (hx : x + s ≤ 1) :
    gaussScaleQuotientCircle p ((s : ℝ) : AddCircle (1 : ℝ)) ((x : ℝ) : AddCircle (1 : ℝ))
      = ((Real.exp ((s - 1 / 2) * Real.log p) : ℝ) : ℂ) *
        Complex.exp (((Real.log p / 2 : ℝ) : ℂ) * (x : ℂ)) := by
  have hx1 : x ≤ 1 := by linarith
  have hxs : (0 : ℝ) < x + s := by linarith
  have hcoe : ((x : ℝ) : AddCircle (1 : ℝ)) + ((s : ℝ) : AddCircle (1 : ℝ))
      = ((x + s : ℝ) : AddCircle (1 : ℝ)) := rfl
  have hreal : gaussPrimeScaleInvSq p (x + s) * gaussPrimeScale p x
      = Real.exp ((s - 1 / 2) * Real.log p) * Real.exp (Real.log p / 2 * x) := by
    rw [gaussPrimeScaleInvSq, gaussPrimeScale, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [gaussScaleQuotientCircle, hcoe, gaussPrimeScaleCircle_coe ⟨hx0, hx1⟩,
    gaussPrimeScaleInvSqCircle_coe ⟨hxs, hx⟩, ← Complex.ofReal_mul, hreal,
    Complex.ofReal_mul, ofReal_exp_mul]
  congr 1
  exact ofReal_exp_mul _ _

/-- After the wrap the scale quotient is `p^(s-3/2)·e^{x·log p/2}`. -/
theorem gaussScaleQuotientCircle_of_ge {p : ℝ} {s x : ℝ}
    (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x ≤ 1) (hx : 1 < x + s) :
    gaussScaleQuotientCircle p ((s : ℝ) : AddCircle (1 : ℝ)) ((x : ℝ) : AddCircle (1 : ℝ))
      = ((Real.exp ((s - 3 / 2) * Real.log p) : ℝ) : ℂ) *
        Complex.exp (((Real.log p / 2 : ℝ) : ℂ) * (x : ℂ)) := by
  have hxs0 : (0 : ℝ) < x + s - 1 := by linarith
  have hxs1 : x + s - 1 ≤ 1 := by linarith
  have hcoe : ((x : ℝ) : AddCircle (1 : ℝ)) + ((s : ℝ) : AddCircle (1 : ℝ))
      = ((x + s - 1 : ℝ) : AddCircle (1 : ℝ)) := by
    have hper : ((x + s - 1 + 1 : ℝ) : AddCircle (1 : ℝ))
        = ((x + s - 1 : ℝ) : AddCircle (1 : ℝ)) := AddCircle.coe_add_period 1 _
    rw [← hper, show (x + s - 1 + 1 : ℝ) = x + s from by ring]
    rfl
  have hreal : gaussPrimeScaleInvSq p (x + s - 1) * gaussPrimeScale p x
      = Real.exp ((s - 3 / 2) * Real.log p) * Real.exp (Real.log p / 2 * x) := by
    rw [gaussPrimeScaleInvSq, gaussPrimeScale, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [gaussScaleQuotientCircle, hcoe, gaussPrimeScaleCircle_coe ⟨hx0, hx1⟩,
    gaussPrimeScaleInvSqCircle_coe ⟨hxs0, hxs1⟩, ← Complex.ofReal_mul, hreal,
    Complex.ofReal_mul, ofReal_exp_mul]
  congr 1
  exact ofReal_exp_mul _ _

/-- **The scale quotient is a two-piece exponential**, with the same breakpoint `1-s` as the
moving amplitude. -/
theorem isExpPiecewise_gaussScaleQuotientCircle {p : ℝ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IsExpPiecewise (Real.log p / 2) 2 (fun i => if i = 0 then 0 else if i = 1 then 1 - s else 1)
      (fun i => if i = 0 then ((Real.exp ((s - 1 / 2) * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 3 / 2) * Real.log p) : ℝ) : ℂ))
      (gaussScaleQuotientCircle p ((s : ℝ) : AddCircle (1 : ℝ))) where
  base := by norm_num
  top := by norm_num
  mono := by
    intro i hi
    interval_cases i <;> (norm_num; try linarith)
  nonneg := by
    intro i hi
    interval_cases i <;> (norm_num; try linarith)
  le_one := by
    intro i hi
    interval_cases i <;> (norm_num; try linarith)
  eq := by
    intro i hi x hx
    interval_cases i
    · have hx0 : 0 < x := by simpa using hx.1
      have hxr : x < 1 - s := by simpa using hx.2
      have hxs : x + s ≤ 1 := by linarith
      rw [gaussScaleQuotientCircle_of_lt hs0 hx0 hxs]
      norm_num
    · have hxl : 1 - s < x := by simpa using hx.1
      have hxr : x < 1 := by simpa using hx.2
      have hx0 : 0 < x := by linarith
      have hxs : 1 < x + s := by linarith
      rw [gaussScaleQuotientCircle_of_ge hs1 hx0 hxr.le hxs]
      norm_num

end

end RHTower
