import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwining

/-!
# The co-Poisson intertwining on the whole line

The half-line pairing identity extends to the line and to arbitrary Schwartz test functions.  Both
co-Poisson sums are even, so only the even part of a test function contributes, and the Fourier
transform commutes with taking even parts.  What is left is the half-line identity applied to that
even part.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- Reflection of a Schwartz function. -/
def schwartzNeg (w : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) w

@[simp] theorem schwartzNeg_apply (w : SchwartzMap ℝ ℂ) (x : ℝ) : schwartzNeg w x = w (-x) := rfl

/-- The even part of a Schwartz function. -/
def schwartzEvenPart (w : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (2 : ℂ)⁻¹ • (w + schwartzNeg w)

theorem schwartzEvenPart_apply (w : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzEvenPart w x = (2 : ℂ)⁻¹ * (w x + w (-x)) := rfl

theorem schwartzEvenPart_even (w : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzEvenPart w (-x) = schwartzEvenPart w x := by
  rw [schwartzEvenPart_apply, schwartzEvenPart_apply, neg_neg, add_comm]

theorem fourier_schwartzNeg (w : SchwartzMap ℝ ℂ) : 𝓕 (schwartzNeg w) = schwartzNeg (𝓕 w) := by
  ext x
  rw [SchwartzMap.fourier_coe, schwartzNeg_apply, SchwartzMap.fourier_coe]
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) w x

/-- **The Fourier transform commutes with taking even parts.** -/
theorem fourier_schwartzEvenPart (w : SchwartzMap ℝ ℂ) :
    𝓕 (schwartzEvenPart w) = schwartzEvenPart (𝓕 w) := by
  rw [schwartzEvenPart, schwartzEvenPart, FourierSMul.fourier_smul, FourierAdd.fourier_add,
    fourier_schwartzNeg]

theorem integrable_bdd_mul_schwartz {f : ℝ → ℂ} (hm : Measurable f) {K : ℝ}
    (hb : ∀ t : ℝ, ‖f t‖ ≤ K) (w : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => f t * w t) :=
  (SchwartzMap.integrable w).bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- **Only the even part of a test function pairs with an even function.** -/
theorem integral_mul_eq_evenPart {f : ℝ → ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (w : SchwartzMap ℝ ℂ) (hint : Integrable fun t : ℝ => f t * w t) :
    (∫ t : ℝ, f t * w t) = ∫ t : ℝ, f t * schwartzEvenPart w t := by
  have hrefl : (∫ t : ℝ, f (-t) * w (-t)) = ∫ t : ℝ, f t * w t :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp measurableEmbedding_neg
      (fun t : ℝ => f t * w t)
  have hneg : (∫ t : ℝ, f t * w (-t)) = ∫ t : ℝ, f t * w t := by
    rw [← hrefl]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [heven]
  have hint2 : Integrable fun t : ℝ => f t * w (-t) := by
    have h := hint.comp_neg
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [heven]
  have hsplit : ∀ t : ℝ, f t * schwartzEvenPart w t =
      (2 : ℂ)⁻¹ * (f t * w t) + (2 : ℂ)⁻¹ * (f t * w (-t)) := by
    intro t
    rw [schwartzEvenPart_apply]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add (hint.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul,
    hneg]
  ring

/-- **Burnol's co-Poisson intertwining on the line.**  For every Schwartz test function the pairing
of the co-Poisson sum of a window seed equals the pairing of the co-Poisson sum of the reciprocal
seed with the Fourier transform of the test function. -/
theorem integral_line_burnolCoPoisson_mul_eq_fourier {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (hG : Integrable (coPoissonReciprocalSeed g))
    (hGsupp : Function.support (coPoissonReciprocalSeed g) ⊆ Icc b b⁻¹)
    (hPm : Measurable (burnolCoPoissonRightSum g)) {K : ℝ}
    (hPb : ∀ t : ℝ, ‖burnolCoPoissonRightSum g t‖ ≤ K)
    (hPGm : Measurable (burnolCoPoissonRightSum (coPoissonReciprocalSeed g))) {K' : ℝ}
    (hPGb : ∀ t : ℝ, ‖burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t‖ ≤ K')
    (w : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, burnolCoPoissonRightSum g t * w t) =
      ∫ t : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t * 𝓕 (w : ℝ → ℂ) t := by
  set we : SchwartzMap ℝ ℂ := schwartzEvenPart w with hwe
  have hweven : ∀ x : ℝ, we (-x) = we x := schwartzEvenPart_even w
  -- reduce both sides to the even part
  have hleft : (∫ t : ℝ, burnolCoPoissonRightSum g t * w t) =
      ∫ t : ℝ, burnolCoPoissonRightSum g t * we t :=
    integral_mul_eq_evenPart (burnolCoPoissonRightSum_even g)
      w (integrable_bdd_mul_schwartz hPm hPb w)
  have hFcoe : ∀ x : ℝ, 𝓕 (w : ℝ → ℂ) x = ((𝓕 w : SchwartzMap ℝ ℂ) : ℝ → ℂ) x := by
    intro x
    rw [SchwartzMap.fourier_coe]
  have hright : (∫ t : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t
        * 𝓕 (w : ℝ → ℂ) t) =
      ∫ t : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t * 𝓕 (we : ℝ → ℂ) t := by
    have h1 : (∫ t : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t
          * ((𝓕 w : SchwartzMap ℝ ℂ) : ℝ → ℂ) t) =
        ∫ t : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t
          * schwartzEvenPart (𝓕 w) t :=
      integral_mul_eq_evenPart (burnolCoPoissonRightSum_even _) (𝓕 w)
        (integrable_bdd_mul_schwartz hPGm hPGb (𝓕 w))
    rw [integral_congr_ae (Filter.Eventually.of_forall fun t => by rw [hFcoe t]), h1, hwe,
      ← fourier_schwartzEvenPart w]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by rw [SchwartzMap.fourier_coe])
  rw [hleft, hright]
  -- both integrands are even, so the line integral is twice the half-line integral
  have hFwe_even : ∀ x : ℝ, 𝓕 (we : ℝ → ℂ) (-x) = 𝓕 (we : ℝ → ℂ) x :=
    fun x => fourier_even_of_even hweven x
  have heven1 : ∀ x : ℝ, burnolCoPoissonRightSum g (-x) * we (-x) =
      burnolCoPoissonRightSum g x * we x := by
    intro x
    rw [burnolCoPoissonRightSum_even, hweven]
  have heven2 : ∀ x : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) (-x)
        * 𝓕 (we : ℝ → ℂ) (-x) =
      burnolCoPoissonRightSum (coPoissonReciprocalSeed g) x * 𝓕 (we : ℝ → ℂ) x := by
    intro x
    rw [burnolCoPoissonRightSum_even, hFwe_even]
  have hint1 : Integrable fun t : ℝ => burnolCoPoissonRightSum g t * we t :=
    integrable_bdd_mul_schwartz hPm hPb we
  have hint2 : Integrable fun t : ℝ =>
      burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t * 𝓕 (we : ℝ → ℂ) t := by
    have h := integrable_bdd_mul_schwartz hPGm hPGb (𝓕 we)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [SchwartzMap.fourier_coe]
  rw [integral_eq_two_mul_integral_Ioi_of_even hint1 heven1,
    integral_eq_two_mul_integral_Ioi_of_even hint2 heven2]
  congr 1
  exact integral_Ioi_burnolCoPoisson_mul_eq_fourier hb hg hsupp hG hGsupp we hweven
    hint1.integrableOn hint2.integrableOn

end RHTower
