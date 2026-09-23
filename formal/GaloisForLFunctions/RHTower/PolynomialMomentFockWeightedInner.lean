import GaloisForLFunctions.RHTower.PolynomialFockNormalizedTangentGaussian

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

/-- Literal weighted pointwise polarization of two polynomial moment-Fock vectors. -/
def polynomialMomentFockWeightedInner
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) (z : ℂ) : ℂ :=
  conj (polynomialMomentFockFunction m hm f z) *
    polynomialMomentFockFunction m hm g z *
      Real.exp (-2 * polynomialFockPotential m ‖z‖)

theorem polynomialMomentFockWeightedInner_eq_polarization
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) (z : ℂ) :
    polynomialMomentFockWeightedInner m hm f g z =
      (((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ) +
        (((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) *
            Complex.I) / 4 := by
  let F : MomentFock →ₗ[ℂ] ℂ := polynomialMomentFockEvaluation m hm z
  have hpol := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (F f) (F g)
  unfold polynomialMomentFockWeightedInner
  rw [polynomialMomentFockFunction_eq_evaluation,
    polynomialMomentFockFunction_eq_evaluation]
  change conj (F f) * F g *
      Real.exp (-2 * polynomialFockPotential m ‖z‖) = _
  simp only [polynomialMomentFockWeightedNormSq,
    polynomialMomentFockFunction_eq_evaluation, F,
    map_add, map_sub, map_smul]
  simp only [RCLike.inner_apply, mul_comm] at hpol
  rw [hpol]
  push_cast
  dsimp [F]
  ring

theorem integrable_polynomialMomentFockWeightedInner
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) :
    Integrable (polynomialMomentFockWeightedInner m hm f g) := by
  have h₁ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f + g)).ofReal
  have h₂ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f - g)).ofReal
  have h₃ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g)).ofReal
  have h₄ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g)).ofReal
  have hpol := ((h₁.sub h₂).add ((h₃.sub h₄).mul_const Complex.I)).div_const 4
  refine hpol.congr ?_
  filter_upwards [] with z
  exact (polynomialMomentFockWeightedInner_eq_polarization m hm f g z).symm

/-- Weighted plane polarization recovers the coefficient-space inner product exactly. -/
theorem integral_polynomialMomentFockWeightedInner
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) :
    (∫ z : ℂ, polynomialMomentFockWeightedInner m hm f g z) = inner ℂ f g := by
  have h₁ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f + g)).ofReal
  have h₂ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f - g)).ofReal
  have h₃ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g)).ofReal
  have h₄ : Integrable (fun z : ℂ =>
      ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) :=
    (integrable_polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g)).ofReal
  have hcast (u : MomentFock) :
      (∫ z : ℂ, ((polynomialMomentFockWeightedNormSq m hm u z : ℝ) : ℂ)) =
        ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hu := integrable_polynomialMomentFockWeightedNormSq m hm u
    change (∫ z : ℂ, Complex.ofRealCLM
      (polynomialMomentFockWeightedNormSq m hm u z)) = _
    rw [ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hu]
    rw [integral_polynomialMomentFockWeightedNormSq]
    rfl
  rw [show (fun z : ℂ => polynomialMomentFockWeightedInner m hm f g z) =
      fun z =>
        (((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ) -
            ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ) +
          (((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ) -
            ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) *
              Complex.I) / 4 by
        funext z
        exact polynomialMomentFockWeightedInner_eq_polarization m hm f g z]
  rw [MeasureTheory.integral_div]
  have hadd := MeasureTheory.integral_add (h₁.sub h₂)
    ((h₃.sub h₄).mul_const Complex.I)
  have hadd' :
      (∫ z : ℂ,
        (((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ)) +
        ((((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) *
            Complex.I)) =
      (∫ z : ℂ,
        ((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ)) +
      (∫ z : ℂ,
        (((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) *
            Complex.I) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using hadd
  rw [hadd']
  have hsub12 := MeasureTheory.integral_sub h₁ h₂
  have hsub12' :
      (∫ z : ℂ,
        ((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ)) =
      (∫ z : ℂ, ((polynomialMomentFockWeightedNormSq m hm (f + g) z : ℝ) : ℂ)) -
      (∫ z : ℂ, ((polynomialMomentFockWeightedNormSq m hm (f - g) z : ℝ) : ℂ)) := by
    simpa only [Pi.sub_apply] using hsub12
  rw [hsub12']
  rw [MeasureTheory.integral_mul_const]
  have hsub34 := MeasureTheory.integral_sub h₃ h₄
  have hsub34' :
      (∫ z : ℂ,
        ((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ) -
          ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) =
      (∫ z : ℂ,
        ((polynomialMomentFockWeightedNormSq m hm (f - Complex.I • g) z : ℝ) : ℂ)) -
      (∫ z : ℂ,
        ((polynomialMomentFockWeightedNormSq m hm (f + Complex.I • g) z : ℝ) : ℂ)) := by
    simpa only [Pi.sub_apply] using hsub34
  rw [hsub34']
  rw [hcast, hcast, hcast, hcast]
  push_cast
  exact (inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) f g).symm

end

end RHTower
