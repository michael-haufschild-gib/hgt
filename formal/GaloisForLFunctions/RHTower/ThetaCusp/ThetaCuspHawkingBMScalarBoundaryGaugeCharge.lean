import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalScalarMetric

set_option autoImplicit false

/-!
# Scalar boundary gauge charge of the literal BM reconstruction

The coordinate Lie/Weyl formula forces three gauge directions in four separated
scalar boundary coefficients. Their exact quotient is one complex charge. The
normalized original scalar radial matrix has charge tending to minus one.

The tensor-faithfulness theorem retains explicit nonzero scalar, gradient and
traceless-Hessian conditions. No claim about every global boundary gauge, every
literal Eisenstein specialization, a chosen physical boundary action, or RH is
inferred from this coefficient classification.
-/

namespace RHTower.D4BMScalarBoundaryGauge
open Filter Topology
noncomputable section

/-- Scalar boundary coefficients multiplying S, dS, S gamma, and Hess S. -/
structure Coefficients where
  tt : ℂ
  mixed : ℂ
  trace : ℂ
  hessian : ℂ
  deriving DecidableEq

/-- Scalar boundary coordinate change (time and gradient amplitudes) and Weyl change. -/
def gaugeShift (s alpha beta sigma : ℂ) : Coefficients :=
  ⟨-2*s*alpha-2*sigma, s*beta-alpha, 2*sigma, 2*beta⟩

/-- Addition of the literal coordinate/Weyl variation to the four scalar coefficients. -/
def transformed (s : ℂ) (c : Coefficients) (alpha beta sigma : ℂ) : Coefficients :=
  let q := gaugeShift s alpha beta sigma
  ⟨c.tt+q.tt, c.mixed+q.mixed, c.trace+q.trace, c.hessian+q.hessian⟩

/-- The surviving scalar boundary coefficient after the three boundary gauge freedoms. -/
def charge (s : ℂ) (c : Coefficients) : ℂ :=
  c.tt+c.trace-2*s*c.mixed+s^(2 : ℕ)*c.hessian

/-- The actual hyperbolic boundary metric at height y. -/
def boundaryMetric (y : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1,0,0; 0,y⁻¹^(2 : ℕ),0; 0,0,y⁻¹^(2 : ℕ)]

/-- Coordinate first jet of the actual boundary metric: only the height derivative is live. -/
def boundaryMetricFirst (y : ℂ) (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  if k = 2 then !![0,0,0; 0,-2*y⁻¹^(3 : ℕ),0; 0,0,-2*y⁻¹^(3 : ℕ)] else 0

/-- Scalar-sector boundary vector, with its common exponential time factor removed. -/
def gaugeVector (alpha beta y S Sx Sy : ℂ) : Fin 3 → ℂ :=
  ![alpha*S,beta*y^(2 : ℕ)*Sx,beta*y^(2 : ℕ)*Sy]

/-- Full coordinate first jet of the scalar boundary vector, retaining angular Hessian data. -/
def gaugeVectorFirst (s alpha beta y S Sx Sy Sxx Sxy Syy : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![s*alpha*S,s*beta*y^(2 : ℕ)*Sx,s*beta*y^(2 : ℕ)*Sy;
     alpha*Sx,beta*y^(2 : ℕ)*Sxx,beta*y^(2 : ℕ)*Sxy;
     alpha*Sy,beta*(2*y*Sx+y^(2 : ℕ)*Sxy),beta*(2*y*Sy+y^(2 : ℕ)*Syy)]

/-- Boundary tensor assembled with the actual hyperbolic covariant Hessian. -/
def tensor (c : Coefficients) (y S Sx Sy Sxx Sxy Syy : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![c.tt*S,c.mixed*Sx,c.mixed*Sy;
     c.mixed*Sx,c.trace*S*y⁻¹^(2 : ℕ)+c.hessian*(Sxx-Sy*y⁻¹),c.hessian*(Sxy+Sx*y⁻¹);
     c.mixed*Sy,c.hessian*(Sxy+Sx*y⁻¹),c.trace*S*y⁻¹^(2 : ℕ)+c.hessian*(Syy+Sy*y⁻¹)]

/-- A nondegenerate scalar harmonic jet makes coefficient equality actual tensor equality.
The hypotheses identify the exceptional harmonic issue instead of assuming a formal basis faithful. -/
theorem tensor_injective (y S Sx Sy Sxx Sxy Syy : ℂ)
    (hy : y ≠ 0) (hS : S ≠ 0) (hGrad : Sx ≠ 0 ∨ Sy ≠ 0)
    (hH : Sxy+Sx*y⁻¹ ≠ 0 ∨ Sxx-Syy-2*Sy*y⁻¹ ≠ 0) :
    Function.Injective (fun c => tensor c y S Sx Sy Sxx Sxy Syy) := by
  intro c d he
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) he
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) he
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 2) he
  have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 1) he
  change c.tt*S=d.tt*S at h0
  change c.mixed*Sx=d.mixed*Sx at h1
  change c.hessian*(Sxy+Sx*y⁻¹)=d.hessian*(Sxy+Sx*y⁻¹) at h2
  change c.trace*S*y⁻¹^(2 : ℕ)+c.hessian*(Sxx-Sy*y⁻¹) =
    d.trace*S*y⁻¹^(2 : ℕ)+d.hessian*(Sxx-Sy*y⁻¹) at h3
  have ht := mul_right_cancel₀ hS h0
  have hm : c.mixed = d.mixed := by
    rcases hGrad with hx | hy'
    · exact mul_right_cancel₀ hx h1
    · exact mul_right_cancel₀ hy' (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 2) he)
  have hh : c.hessian = d.hessian := by
    rcases hH with hxy | hdiff
    · exact mul_right_cancel₀ hxy h2
    · have h4 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 2) he
      change c.trace*S*y⁻¹^(2 : ℕ)+c.hessian*(Syy+Sy*y⁻¹) =
        d.trace*S*y⁻¹^(2 : ℕ)+d.hessian*(Syy+Sy*y⁻¹) at h4
      apply mul_right_cancel₀ hdiff
      linear_combination h3-h4
  rw [hh] at h3
  have ha := mul_right_cancel₀ hS
    (mul_right_cancel₀ (pow_ne_zero 2 (inv_ne_zero hy)) (add_right_cancel h3))
  cases c
  cases d
  cases ht
  cases hm
  cases hh
  cases ha
  rfl

/-- Coordinate Lie action and Weyl action on the actual boundary metric jet. -/
def lieWeyl (s alpha beta sigma y S Sx Sy Sxx Sxy Syy : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    (∑ k, gaugeVector alpha beta y S Sx Sy k * boundaryMetricFirst y k i j) +
    (∑ k, boundaryMetric y k j * gaugeVectorFirst s alpha beta y S Sx Sy Sxx Sxy Syy i k) +
    (∑ k, boundaryMetric y i k * gaugeVectorFirst s alpha beta y S Sx Sy Sxx Sxy Syy j k) +
    2*sigma*S*boundaryMetric y i j

/-- The four gauge shifts follow from the coordinate Lie formula; none is chosen by charge invariance. -/
theorem lieWeyl_eq (s alpha beta sigma y S Sx Sy Sxx Sxy Syy : ℂ) (hy : y ≠ 0) :
    lieWeyl s alpha beta sigma y S Sx Sy Sxx Sxy Syy =
      tensor (gaugeShift s alpha beta sigma) y S Sx Sy Sxx Sxy Syy := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [lieWeyl, gaugeVector, boundaryMetricFirst, boundaryMetric,
    gaugeVectorFirst, tensor, gaugeShift, Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

/-- The boundary charge is invariant under every separated scalar coordinate/Weyl change. -/
theorem charge_transformed (s : ℂ) (c : Coefficients) (alpha beta sigma : ℂ) :
    charge s (transformed s c alpha beta sigma) = charge s c := by
  simp only [charge, transformed, gaugeShift]
  ring

/-- Equal charges characterize the complete four-coefficient gauge orbit. -/
theorem exists_transformed_iff (s : ℂ) (c d : Coefficients) :
    (∃ alpha beta sigma, transformed s c alpha beta sigma = d) ↔ charge s c = charge s d := by
  constructor
  · rintro ⟨alpha,beta,sigma,he⟩
    rw [← he,charge_transformed]
  · intro h
    refine ⟨s*(d.hessian-c.hessian)/2-(d.mixed-c.mixed),
      (d.hessian-c.hessian)/2, (d.trace-c.trace)/2, ?_⟩
    cases c with | mk ct cm ca ch =>
      cases d with | mk dt dm da dh =>
        simp only [charge] at h
        simp only [transformed, gaugeShift, Coefficients.mk.injEq]
        constructor
        · linear_combination h
        · constructor
          · ring
          · constructor <;> ring

/-- Boundary coefficient of the normalized literal scalar family: only its angular trace survives. -/
def fundamental : Coefficients := ⟨0,0,-1,0⟩

/-- The normalized scalar boundary obstruction is nonzero at every time frequency. -/
theorem charge_fundamental (s : ℂ) : charge s fundamental = -1 := by
  simp [charge,fundamental]

/-- No separated scalar boundary coordinate/Weyl transformation makes these coefficients vanish. -/
theorem fundamental_not_gauge_zero (s : ℂ) :
    ¬ ∃ alpha beta sigma, transformed s fundamental alpha beta sigma = ⟨0,0,0,0⟩ := by
  rw [exists_transformed_iff,charge_fundamental]
  norm_num [charge]

/-- At a faithful scalar harmonic jet, the normalized boundary tensor is outside the zero gauge orbit. -/
theorem fundamental_tensor_not_gauge_zero (s y S Sx Sy Sxx Sxy Syy : ℂ)
    (hy : y ≠ 0) (hS : S ≠ 0) (hGrad : Sx ≠ 0 ∨ Sy ≠ 0)
    (hH : Sxy+Sx*y⁻¹ ≠ 0 ∨ Sxx-Syy-2*Sy*y⁻¹ ≠ 0) :
    ¬ ∃ alpha beta sigma,
      tensor (transformed s fundamental alpha beta sigma) y S Sx Sy Sxx Sxy Syy = 0 := by
  rintro ⟨alpha,beta,sigma,he⟩
  apply fundamental_not_gauge_zero s
  refine ⟨alpha,beta,sigma, tensor_injective y S Sx Sy Sxx Sxy Syy hy hS hGrad hH ?_⟩
  refine he.trans ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensor]

/-- Tangential coordinate inclusion from (time,x,y) into the actual four-coordinate chart. -/
def tangential : Fin 3 → Fin 4 := ![0,2,3]

/-- Exact normalized coefficients at finite radius before taking the AdS boundary limit. -/
def normalizedFundamental (s r : ℂ) : Coefficients :=
  ⟨r⁻¹^(2 : ℕ)*(s*(s-3)/2+s*(s+1)/(2*r^(2 : ℕ))),0,
   r⁻¹^(2 : ℕ)*(-r^(2 : ℕ)-s*(s+1)/2),0⟩

/-- These coefficients are extracted from the original reconstructed scalar radial matrix. -/
theorem normalizedFundamental_tensor (s r y S : ℂ) (i j : Fin 3) :
    r⁻¹^(2 : ℕ)*S*D4BMFundamentalScalarMetric.radialMatrix s r y (tangential i) (tangential j) =
      tensor (normalizedFundamental s r) y S 0 0 0 0 0 i j := by
  fin_cases i <;> fin_cases j
  all_goals simp [D4BMFundamentalScalarMetric.radialMatrix, tangential,
    tensor, normalizedFundamental]
  all_goals ring

/-- The complete normalized scalar boundary charge retains a unit constant at every frequency. -/
theorem charge_normalizedFundamental (s r : ℂ) (hr : r ≠ 0) :
    charge s (normalizedFundamental s r) = -1-2*s*r⁻¹^(2 : ℕ)+s*(s+1)/2*r⁻¹^(4 : ℕ) := by
  simp only [charge, normalizedFundamental]
  field_simp
  ring

/-- The actual finite-radius charge tends to minus one at spatial infinity. -/
theorem charge_normalizedFundamental_limit (s : ℂ) :
    Tendsto (fun r : ℝ => charge s (normalizedFundamental s r)) atTop (𝓝 (-1)) := by
  have he : (fun r : ℝ => charge s (normalizedFundamental s r)) =ᶠ[atTop]
      (fun r : ℝ => -1-2*s*((r : ℂ)⁻¹)^(2 : ℕ)+s*(s+1)/2*((r : ℂ)⁻¹)^(4 : ℕ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact charge_normalizedFundamental s r (by exact_mod_cast hr.ne')
  have hi : Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_inv] using
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  have h := ((tendsto_const_nhds (x := (-1 : ℂ))).sub
    ((hi.pow 2).const_mul (2*s))).add ((hi.pow 4).const_mul (s*(s+1)/2))
  simpa using h.congr' he.symm

/-- Even radius-dependent scalar coordinate/Weyl amplitudes leave this limiting obstruction unchanged. -/
theorem transformed_normalizedFundamental_limit (s : ℂ) (alpha beta sigma : ℝ → ℂ) :
    Tendsto (fun r : ℝ => charge s
      (transformed s (normalizedFundamental s r) (alpha r) (beta r) (sigma r)))
      atTop (𝓝 (-1)) := by
  simp only [charge_transformed]
  exact charge_normalizedFundamental_limit s

end
end RHTower.D4BMScalarBoundaryGauge
