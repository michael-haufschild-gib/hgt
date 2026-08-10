import GaloisForLFunctions.RHTower.GaussPrincipalStep
import GaloisForLFunctions.RHTower.GaussRotationIsTranslation

/-!
# The moving amplitude as an operator

The composite that the one-step factorization leaves behind is exactly multiplication by the
moving amplitude:

`B ∘ T_(-δ) ∘ B^(-2) ∘ T_δ ∘ B  =  M_(a_δ)`,   `a_δ(z) = b(z)² · b(z + δ)^(-2)`.

Pointwise the four factors telescope: translating in, dividing by `b(·)²` at the translated point,
translating back and multiplying by `b(·)²` leaves the ratio of the prime scale to its translate,
which is `s_p/s_p(· + δ)` — the amplitude whose exact period average is
`intervalIntegral_gaussMovingAmplitude_pow`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-! ## Almost-everywhere equality survives translation -/

theorem ae_eq_comp_sub {f g : AddCircle (1 : ℝ) → ℂ} (δ : AddCircle (1 : ℝ))
    (h : f =ᵐ[AddCircle.haarAddCircle] g) :
    (fun z => f (z - δ)) =ᵐ[AddCircle.haarAddCircle] fun z => g (z - δ) :=
  (measurePreserving_sub_right AddCircle.haarAddCircle δ).quasiMeasurePreserving.ae_eq_comp h

/-! ## The moving amplitude on the circle -/

/-- The moving amplitude `a_δ(z) = b(z)²·b(z+δ)^(-2)` on the circle. -/
def gaussMovingAmplitudeCircle (p : ℝ) (δ : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) → ℂ :=
  fun z => gaussPrimeScaleCircle p z * gaussPrimeScaleInvSqCircle p (z + δ) *
    gaussPrimeScaleCircle p z

theorem measurable_gaussMovingAmplitudeCircle (p : ℝ) (δ : AddCircle (1 : ℝ)) :
    Measurable (gaussMovingAmplitudeCircle p δ) :=
  ((measurable_gaussPrimeScaleCircle p).mul
    ((measurable_gaussPrimeScaleInvSqCircle p).comp (measurable_add_const δ))).mul
      (measurable_gaussPrimeScaleCircle p)

theorem norm_gaussMovingAmplitudeCircle_le {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (z : AddCircle (1 : ℝ)) : ‖gaussMovingAmplitudeCircle p δ z‖ ≤ p := by
  have hb := norm_gaussPrimeScaleCircle_le hp z
  have hi := norm_gaussPrimeScaleInvSqCircle_le hp (z + δ)
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
  rw [gaussMovingAmplitudeCircle, norm_mul, norm_mul]
  calc ‖gaussPrimeScaleCircle p z‖ * ‖gaussPrimeScaleInvSqCircle p (z + δ)‖ *
      ‖gaussPrimeScaleCircle p z‖
      ≤ Real.sqrt p * 1 * Real.sqrt p := by
        refine mul_le_mul (mul_le_mul hb hi (norm_nonneg _) (Real.sqrt_nonneg p)) hb
          (norm_nonneg _) (by positivity)
    _ = p := by rw [mul_one, hsq]

/-- Multiplication by the moving amplitude. -/
def gaussMovingAmplitudeBlock {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MeasureTheory.lpBoundedMulCLM (measurable_gaussMovingAmplitudeCircle p δ)
    (by linarith : (0 : ℝ) ≤ p) (norm_gaussMovingAmplitudeCircle_le hp δ)

/-! ## The telescoping identity -/

set_option maxHeartbeats 2000000 in
/-- **The composite is multiplication by the moving amplitude.** -/
theorem gaussPrimeScaleBlock_translate_invSq_translate {p : ℝ} (hp : 1 < p)
    (δ : AddCircle (1 : ℝ)) (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrimeScaleBlock hp
        (gaussTranslationBlock (-δ)
          (gaussPrimeScaleInvSqBlock hp (gaussTranslationBlock δ (gaussPrimeScaleBlock hp f))))
      = gaussMovingAmplitudeBlock hp δ f := by
  set u1 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussPrimeScaleBlock hp f with hu1
  set u2 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussTranslationBlock δ u1 with hu2
  set u3 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp u2 with hu3
  set u4 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussTranslationBlock (-δ) u3 with hu4
  have h1 : (u1 : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleCircle p z * (f : AddCircle (1 : ℝ) → ℂ) z := by
    rw [hu1]
    exact gaussPrimeScaleBlock_coeFn hp f
  have h2 : (u2 : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleCircle p (z - δ) * (f : AddCircle (1 : ℝ) → ℂ) (z - δ) := by
    rw [hu2]
    refine (coeFn_gaussTranslationBlock δ u1).trans ?_
    filter_upwards [ae_eq_comp_sub δ h1] with z hz
    exact hz
  have h3 : (u3 : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleInvSqCircle p z *
          (gaussPrimeScaleCircle p (z - δ) * (f : AddCircle (1 : ℝ) → ℂ) (z - δ)) := by
    rw [hu3]
    refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ u2).trans ?_
    filter_upwards [h2] with z hz
    rw [hz]
  have h4 : (u4 : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleInvSqCircle p (z + δ) *
          (gaussPrimeScaleCircle p z * (f : AddCircle (1 : ℝ) → ℂ) z) := by
    rw [hu4]
    refine (coeFn_gaussTranslationBlock (-δ) u3).trans ?_
    filter_upwards [ae_eq_comp_sub (-δ) h3] with z hz
    rw [hz]
    simp only [sub_neg_eq_add, add_sub_cancel_right]
  refine Lp.ext ?_
  refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ u4).trans ?_
  refine Filter.EventuallyEq.trans ?_ (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ f).symm
  filter_upwards [h4] with z hz
  rw [hz, gaussMovingAmplitudeCircle]
  ring

end

end RHTower
