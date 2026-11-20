import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentreValueIsTheEquationOfTheSignBranchPoints
import GaloisForLFunctions.RHTower.HeatOperatorPolynomial
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite

/-!
# All derivatives along a parabolic heat ray

On (τ+s²,z+sy), the j-th derivative at s=0 of the k-th spatial
derivative is the (k+j)-th spatial derivative times the monic Hermite
polynomial with variance two, evaluated at y. The chain rule and the
backward heat equation give the three-term Hermite recurrence.
-/

noncomputable section
open Complex Polynomial Filter Topology RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The spatial derivative as a function on complex time and place. -/
def spacetimeHeatJet (k : ℕ) (p : ℂ × ℂ) := iteratedDeriv k (complexHeat p.1) p.2

theorem analyticAt_spacetimeHeatJet (k : ℕ) (p : ℂ × ℂ) : AnalyticAt ℂ (spacetimeHeatJet k) p := by
  induction k generalizing p with
  | zero =>
    rw [show spacetimeHeatJet 0 = fun q : ℂ × ℂ => complexHeat q.1 q.2 from
      funext fun q => by simp [spacetimeHeatJet]]
    exact analyticAt_complexHeat p
  | succ k ih =>
    have he : spacetimeHeatJet (k+1) = fun q => fderiv ℂ (spacetimeHeatJet k) q (0,1) := by
      funext q
      have h := (ih q).differentiableAt.hasFDerivAt.comp_hasDerivAt q.2
        ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
      change iteratedDeriv (k+1) (complexHeat q.1) q.2=_
      rw [iteratedDeriv_succ]
      exact h.deriv
    rw [he]
    exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1):ℂ × ℂ)).analyticAt _).comp (ih p).fderiv

private def ray (τ z y : ℂ) (k : ℕ) (s : ℂ) := spacetimeHeatJet k (τ+s^2,z+s*y)

private theorem ray_analytic (τ z y : ℂ) (k : ℕ) (s : ℂ) : AnalyticAt ℂ (ray τ z y k) s :=
  (analyticAt_spacetimeHeatJet k _).comp
    ((analyticAt_const.add (analyticAt_id.pow 2)).prod (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))

private theorem ray_deriv (τ z y : ℂ) (k : ℕ) :
    deriv (ray τ z y k) = (fun s => y*ray τ z y (k+1) s) -
      (fun s => 2*(s*ray τ z y (k+2) s)) := by
  funext s
  let p : ℂ × ℂ := (τ+s^2,z+s*y)
  let D := fderiv ℂ (spacetimeHeatJet k) p
  have hd := (analyticAt_spacetimeHeatJet k p).differentiableAt.hasFDerivAt
  have ht : D (1,0) = -spacetimeHeatJet (k+2) p := by
    have h := hd.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    exact h.unique (hasDerivAt_time_iteratedDeriv_complexHeat k p.1 p.2)
  have hz : D (0,1)=spacetimeHeatJet (k+1) p := by
    have h := hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    change _=iteratedDeriv (k+1) (complexHeat p.1) p.2
    rw [iteratedDeriv_succ]
    exact h.deriv.symm
  have hline : HasDerivAt (fun u : ℂ => (τ+u^2,z+u*y)) (2*s,y) s := by
    apply HasDerivAt.prodMk
    · simpa using ((hasDerivAt_id s).pow 2).const_add τ
    · simpa using ((hasDerivAt_id s).mul_const y).const_add z
  have h := (hd.comp_hasDerivAt s hline).deriv
  change deriv (ray τ z y k) s=D (2*s,y) at h
  rw [h,show (2*s,y)=(2*s) • ((1,0):ℂ × ℂ)+y • ((0,1):ℂ × ℂ) by ext <;> simp,
    map_add,map_smul,map_smul,ht,hz]
  change (2*s)*(-spacetimeHeatJet (k+2) p)+y*spacetimeHeatJet (k+1) p=
    y*spacetimeHeatJet (k+1) p-2*(s*spacetimeHeatJet (k+2) p)
  ring

/-- The rescaled Hermite polynomials form an Appell sequence at every
nonzero heat scale and at the totalized scale zero. -/
theorem derivative_heat_shift_polynomial (t : ℝ) (n : ℕ) :
    (heatShiftPoly t (n+1)).derivative = C ((n:ℝ)+1)*heatShiftPoly t n := by
  induction n with
  | zero => simp [heatShiftPoly_succ]
  | succ n ih =>
    rw [heatShiftPoly_succ t (n+1),derivative_sub,derivative_mul,derivative_X,one_mul,
      derivative_C_mul,ih,derivative_C_mul,heatShiftPoly_succ t n,Nat.cast_succ]
    simp only [map_add,map_one,map_natCast]
    ring

/-- The monic heat polynomial evaluated at a complex direction. -/
def parabolicRayPolynomial (j : ℕ) (y : ℂ) := aeval y (heatShiftPoly (1/4) j)

theorem parabolic_ray_raise (j : ℕ) (y : ℂ) :
    parabolicRayPolynomial (j+1) y = y*parabolicRayPolynomial j y-2*deriv (parabolicRayPolynomial j) y := by
  have h : deriv (parabolicRayPolynomial j) y=aeval y (heatShiftPoly (1/4) j).derivative :=
    ((heatShiftPoly (1/4) j).hasDerivAt_aeval y).deriv
  rw [h]
  simp only [parabolicRayPolynomial]
  rw [heatShiftPoly_succ,map_sub,map_mul,map_mul,aeval_X,aeval_C]
  norm_num

theorem parabolic_ray_lower (j : ℕ) (y : ℂ) :
    deriv (parabolicRayPolynomial (j+1)) y=((j:ℂ)+1)*parabolicRayPolynomial j y := by
  rw [show deriv (parabolicRayPolynomial (j+1)) y=aeval y (heatShiftPoly (1/4) (j+1)).derivative from
    ((heatShiftPoly (1/4) (j+1)).hasDerivAt_aeval y).deriv,derivative_heat_shift_polynomial,
    map_mul,aeval_C,map_add,map_natCast,map_one] <;> rfl

/-- Extracting a ray jet costs one further spatial derivative per order,
at arbitrary complex time, place and direction. -/
theorem heat_parabolic_ray_derivative (τ z y : ℂ) (j k : ℕ) :
    iteratedDeriv j (fun s : ℂ => iteratedDeriv k (complexHeat (τ+s^2)) (z+s*y)) 0 =
      parabolicRayPolynomial j y * iteratedDeriv (k+j) (complexHeat τ) z := by
  change iteratedDeriv j (ray τ z y k) 0=_
  induction j using Nat.twoStepInduction generalizing k with
  | zero => simp [ray,spacetimeHeatJet,parabolicRayPolynomial]
  | one =>
    rw [iteratedDeriv_one,ray_deriv]
    simp [ray,spacetimeHeatJet,parabolicRayPolynomial,heatShiftPoly_succ]
  | more j h₀ h₁ =>
    have hf := fun k s => (ray_analytic τ z y k s).differentiableAt
    have ha : ContDiffAt ℂ (j+1) (fun s => y*ray τ z y (k+1) s) 0 :=
      (contDiffAt_const.mul (ray_analytic τ z y (k+1) 0).contDiffAt)
    have hb : ContDiffAt ℂ (j+1) (fun s => 2*(s*ray τ z y (k+2) s)) 0 :=
      contDiffAt_const.mul (contDiffAt_id.mul (ray_analytic τ z y (k+2) 0).contDiffAt)
    rw [iteratedDeriv_succ',ray_deriv,iteratedDeriv_sub ha hb,
      iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
    beta_reduce
    rw [HTGeometry.iteratedDeriv_id_mul_zero (hf (k+2)) j,h₁ (k+1),h₀ (k+2),
      parabolic_ray_raise (j+1),parabolic_ray_lower]
    rw [show k+1+(j+1)=k+(j+2) by omega,show k+2+j=k+(j+2) by omega]
    ring

#print axioms analyticAt_spacetimeHeatJet
#print axioms heat_parabolic_ray_derivative
end GaloisForLFunctions.GaloisTheoryOfZeros
