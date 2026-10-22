import GaloisForLFunctions.RHTower.CCM.CCMPrimeFrustratedPhaseEnergy

/-!
# Diagonal phase symmetry and its exact Noether balance

The actual three-source phase potential defines a mechanical Lagrangian with
unit kinetic masses. Common phase translation preserves the Lagrangian, and
the three potential derivatives sum to zero. Consequently total angular
momentum is conserved along every classical Newton trajectory of this action.
The unit kinetic masses are a chosen mechanical realization of the potential.
-/

noncomputable section

namespace RHTower

theorem hasDerivAt_ccmWeilTrianglePhaseEnergy_first (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) :
    HasDerivAt (fun x => ccmWeilTrianglePhaseEnergy a u v w x beta gamma)
      (-2 * ccmWeilRealPolar a u v * Real.sin (alpha - beta) -
        2 * ccmWeilRealPolar a u w * Real.sin (alpha - gamma)) alpha := by
  simp_rw [ccmWeilTrianglePhaseEnergy_eq]
  have h₁ := ((hasDerivAt_id alpha).sub_const beta).cos.const_mul (2 * ccmWeilRealPolar a u v)
  have h₂ := ((hasDerivAt_id alpha).sub_const gamma).cos.const_mul (2 * ccmWeilRealPolar a u w)
  convert! (((hasDerivAt_const alpha (ccmRestrictedWeilSourceQuadratic a u +
    ccmRestrictedWeilSourceQuadratic a v + ccmRestrictedWeilSourceQuadratic a w)).add h₁).add h₂).add_const
      (2 * ccmWeilRealPolar a v w * Real.cos (beta - gamma)) using 1
  dsimp only [id_eq]
  ring

theorem hasDerivAt_ccmWeilTrianglePhaseEnergy_second (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) :
    HasDerivAt (fun x => ccmWeilTrianglePhaseEnergy a u v w alpha x gamma)
      (2 * ccmWeilRealPolar a u v * Real.sin (alpha - beta) -
        2 * ccmWeilRealPolar a v w * Real.sin (beta - gamma)) beta := by
  simp_rw [ccmWeilTrianglePhaseEnergy_eq]
  have h₁ := ((hasDerivAt_id beta).const_sub alpha).cos.const_mul (2 * ccmWeilRealPolar a u v)
  have h₃ := ((hasDerivAt_id beta).sub_const gamma).cos.const_mul (2 * ccmWeilRealPolar a v w)
  convert! (((hasDerivAt_const beta (ccmRestrictedWeilSourceQuadratic a u +
    ccmRestrictedWeilSourceQuadratic a v + ccmRestrictedWeilSourceQuadratic a w)).add h₁).add_const
      (2 * ccmWeilRealPolar a u w * Real.cos (alpha - gamma))).add h₃ using 1
  dsimp only [id_eq]
  ring

theorem hasDerivAt_ccmWeilTrianglePhaseEnergy_third (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) :
    HasDerivAt (fun x => ccmWeilTrianglePhaseEnergy a u v w alpha beta x)
      (2 * ccmWeilRealPolar a u w * Real.sin (alpha - gamma) +
        2 * ccmWeilRealPolar a v w * Real.sin (beta - gamma)) gamma := by
  simp_rw [ccmWeilTrianglePhaseEnergy_eq]
  have h₂ := ((hasDerivAt_id gamma).const_sub alpha).cos.const_mul (2 * ccmWeilRealPolar a u w)
  have h₃ := ((hasDerivAt_id gamma).const_sub beta).cos.const_mul (2 * ccmWeilRealPolar a v w)
  convert! ((hasDerivAt_const gamma (ccmRestrictedWeilSourceQuadratic a u +
    ccmRestrictedWeilSourceQuadratic a v + ccmRestrictedWeilSourceQuadratic a w +
      2 * ccmWeilRealPolar a u v * Real.cos (alpha - beta))).add h₂).add h₃ using 1
  dsimp only [id_eq]
  ring

/-- The infinitesimal Noether identity is unconditional for the full arithmetic potential. -/
theorem ccmWeilTrianglePhaseEnergy_total_derivative_zero (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) :
    deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w x beta gamma) alpha +
      deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w alpha x gamma) beta +
      deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w alpha beta x) gamma = 0 := by
  rw [(hasDerivAt_ccmWeilTrianglePhaseEnergy_first a u v w alpha beta gamma).deriv,
    (hasDerivAt_ccmWeilTrianglePhaseEnergy_second a u v w alpha beta gamma).deriv,
    (hasDerivAt_ccmWeilTrianglePhaseEnergy_third a u v w alpha beta gamma).deriv]
  ring

def ccmWeilTriangleLagrangian (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma va vb vc : ℝ) : ℝ :=
  (va ^ 2 + vb ^ 2 + vc ^ 2) / 2 - ccmWeilTrianglePhaseEnergy a u v w alpha beta gamma

theorem ccmWeilTriangleLagrangian_common_shift (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma va vb vc t : ℝ) :
    ccmWeilTriangleLagrangian a u v w (alpha + t) (beta + t) (gamma + t) va vb vc =
      ccmWeilTriangleLagrangian a u v w alpha beta gamma va vb vc := by
  simp only [ccmWeilTriangleLagrangian, ccmWeilTrianglePhaseEnergy_common_shift]

/-- Newton's equations imply conservation of the charge of common phase translation. -/
theorem ccmWeilTriangle_total_momentum_conserved (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt (deriv alpha)
      (-deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w x (beta t) (gamma t)) (alpha t)) t)
    (hb : ∀ t, HasDerivAt (deriv beta)
      (-deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w (alpha t) x (gamma t)) (beta t)) t)
    (hc : ∀ t, HasDerivAt (deriv gamma)
      (-deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w (alpha t) (beta t) x) (gamma t)) t)
    (s t : ℝ) :
    deriv alpha s + deriv beta s + deriv gamma s =
      deriv alpha t + deriv beta t + deriv gamma t := by
  have hd (x : ℝ) : HasDerivAt
      (fun y => deriv alpha y + deriv beta y + deriv gamma y) 0 x := by
    have h := (ha x |>.add (hb x)).add (hc x)
    have hz := ccmWeilTrianglePhaseEnergy_total_derivative_zero a u v w (alpha x) (beta x) (gamma x)
    convert! h using 1
    linarith only [hz]
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s t

def ccmWeilTriangleUniformPhase (c omega t : ℝ) : ℝ := c + omega * t

theorem hasDerivAt_ccmWeilTriangleUniformPhase (c omega t : ℝ) :
    HasDerivAt (ccmWeilTriangleUniformPhase c omega) omega t := by
  convert! ((hasDerivAt_id t).const_mul omega).const_add c using 1
  simp only [mul_one]

/-- A global trajectory is explicitly constructed; Newton's equations are conclusions. -/
theorem ccmWeilTriangle_uniform_rotation_newton (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (c omega t : ℝ) :
    let q := ccmWeilTriangleUniformPhase c omega
    HasDerivAt (deriv q)
      (-deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w x (q t) (q t)) (q t)) t ∧
    HasDerivAt (deriv q)
      (-deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w (q t) x (q t)) (q t)) t ∧
    HasDerivAt (deriv q)
      (-deriv (fun x => ccmWeilTrianglePhaseEnergy a u v w (q t) (q t) x) (q t)) t := by
  let q := ccmWeilTriangleUniformPhase c omega
  have hv : deriv q = fun _ => omega := funext fun s =>
    (hasDerivAt_ccmWeilTriangleUniformPhase c omega s).deriv
  have h₁ := (hasDerivAt_ccmWeilTrianglePhaseEnergy_first a u v w (q t) (q t) (q t)).deriv
  have h₂ := (hasDerivAt_ccmWeilTrianglePhaseEnergy_second a u v w (q t) (q t) (q t)).deriv
  have h₃ := (hasDerivAt_ccmWeilTrianglePhaseEnergy_third a u v w (q t) (q t) (q t)).deriv
  dsimp only
  change HasDerivAt (deriv q) _ t ∧ HasDerivAt (deriv q) _ t ∧ HasDerivAt (deriv q) _ t
  rw [hv, h₁, h₂, h₃]
  simp only [sub_self, Real.sin_zero, mul_zero, add_zero, neg_zero]
  exact ⟨hasDerivAt_const t omega, hasDerivAt_const t omega, hasDerivAt_const t omega⟩

/-- Both charges are exact along the constructed common rotation. -/
theorem ccmWeilTriangle_uniform_rotation_charges (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (c omega t : ℝ) :
    let q := ccmWeilTriangleUniformPhase c omega
    deriv q t + deriv q t + deriv q t = 3 * omega ∧
      (deriv q t ^ 2 + deriv q t ^ 2 + deriv q t ^ 2) / 2 +
        ccmWeilTrianglePhaseEnergy a u v w (q t) (q t) (q t) =
      3 * omega ^ 2 / 2 + ccmWeilTrianglePhaseEnergy a u v w c c c := by
  dsimp only
  rw [(hasDerivAt_ccmWeilTriangleUniformPhase c omega t).deriv]
  unfold ccmWeilTriangleUniformPhase
  rw [ccmWeilTrianglePhaseEnergy_common_shift]
  constructor <;> ring

end RHTower
