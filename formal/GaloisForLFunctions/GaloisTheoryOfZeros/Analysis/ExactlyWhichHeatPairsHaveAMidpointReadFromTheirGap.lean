import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.RecoveringHeatTimeFromOneReflectedPair

/-!
# Which heat pairs have a midpoint determined by the squared gap?

The signed gap between any two distinct Hermite sheets is a local
coordinate. A function of its square must agree at the two opposite
coordinate values, so a differentiable midpoint must have zero first
derivative. This selects exactly the reflected pairs, even when the
proposed reconstruction is allowed to be an arbitrary function.
-/

noncomputable section
open Complex Filter Topology RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Factoring through the square of a simple analytic coordinate forces
a zero first derivative. No regularity of the outer function is needed. -/
theorem derivative_vanishes_through_squared_coordinate {D M : ℂ → ℂ}
    (hD : AnalyticAt ℂ D 0) (h₀ : D 0=0) (hn : deriv D 0≠0) (hM : DifferentiableAt ℂ M 0)
    (P : ℂ → ℂ) (hP : ∀ᶠ s in 𝓝 0, P ((D s)^2)=M s) : deriv M 0=0 := by
  let A := hD.hasStrictDerivAt.localInverse _ _ _ hn
  have hl : ∀ᶠ s in 𝓝 0, A (D s)=s := hD.hasStrictDerivAt.eventually_left_inverse hn
  have hA0 : A 0=0 := by simpa only [h₀] using hl.self_of_nhds
  have hr : ∀ᶠ w in 𝓝 0, D (A w)=w := by
    simpa only [h₀] using (hD.hasStrictDerivAt.eventually_right_inverse hn : ∀ᶠ w in 𝓝 (D 0), D (A w)=w)
  have hA : HasDerivAt A (deriv D 0)⁻¹ 0 := by
    simpa only [h₀] using (hD.hasStrictDerivAt.to_localInverse hn).hasDerivAt
  have ha : Tendsto A (𝓝 0) (𝓝 0) := by simpa only [hA0] using hA.continuousAt.tendsto
  let E (w : ℂ) := M (A w)
  have hE : HasDerivAt E (deriv M 0*(deriv D 0)⁻¹) 0 :=
    (by simpa only [hA0] using hM.hasDerivAt : HasDerivAt M (deriv M 0) (A 0)).comp 0 hA
  have hs : ∀ᶠ w in 𝓝 0, P (w^2)=E w := by
    filter_upwards [ha.eventually hP,hr] with w hp hi
    rwa [hi] at hp
  have hneg : Tendsto (fun w : ℂ => -w) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg (G:=ℂ)).tendsto 0
  have he : (fun w => E (-w)) =ᶠ[𝓝 0] E := by
    filter_upwards [hs,hneg.eventually hs] with w hw hmw
    rw [←hw,←hmw,neg_sq]
  have hE' : HasDerivAt E (deriv M 0*(deriv D 0)⁻¹) (-0) := by simpa only [neg_zero] using hE
  have heq := (hE'.comp 0 (hasDerivAt_id (0:ℂ)).neg).unique (hE.congr_of_eventuallyEq he)
  have hzero : deriv M 0*(deriv D 0)⁻¹=0 := by
    change (deriv M 0*(deriv D 0)⁻¹)*(-1)=deriv M 0*(deriv D 0)⁻¹ at heq
    linear_combination (-1/2:ℂ)*heq
  exact (mul_eq_zero.mp hzero).resolve_right (inv_ne_zero hn)

private theorem sheet_origin_derivative {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hr : heatModelFwd m ρ=0) : HasDerivAt (collisionZero τ z m ρ) ρ 0 := by
  obtain ⟨hY,h₀,_,_⟩ := collisionBranch_spec hc hr
  have h := ((hasDerivAt_id (0:ℂ)).mul hY.differentiableAt.hasDerivAt).const_add z
  have he : (fun w => z+(id * collisionBranch τ z m ρ) w)=collisionZero τ z m ρ := by funext w; rfl
  simpa only [he,id_eq,h₀,one_mul,zero_mul,add_zero] using h

/-- Among distinct sheets, the signed roots must be opposites exactly
when the unordered squared gap determines the midpoint near the collision. -/
theorem IsCollision.midpoint_from_gap_iff_opposite {τ z ρ η : ℂ} {m : ℕ}
    (hc : IsCollision τ z m) (hρ : heatModelFwd m ρ=0) (hη : heatModelFwd m η=0)
    (hne : ρ≠η) :
    (∃ P : ℂ → ℂ, ∀ᶠ s in 𝓝 0,
      P ((collisionZero τ z m ρ s-collisionZero τ z m η s)^2)=
        (collisionZero τ z m ρ s+collisionZero τ z m η s)/2) ↔ η= -ρ := by
  let X := collisionZero τ z m ρ
  let Y := collisionZero τ z m η
  let D := X-Y
  let M (s : ℂ) := (X s+Y s)/2
  have hx := sheet_origin_derivative hc hρ
  have hy := sheet_origin_derivative hc hη
  have hD : HasDerivAt D (ρ-η) 0 := hx.sub hy
  have hM : HasDerivAt M ((ρ+η)/2) 0 := (hx.add hy).div_const 2
  have hX : AnalyticAt ℂ X 0 := analyticAt_const.add (analyticAt_id.mul (collisionBranch_spec hc hρ).1)
  have hY : AnalyticAt ℂ Y 0 := analyticAt_const.add (analyticAt_id.mul (collisionBranch_spec hc hη).1)
  constructor
  · rintro ⟨P,hP⟩
    have hd : deriv D 0≠0 := hD.deriv.trans_ne (sub_ne_zero.mpr hne)
    have hz := derivative_vanishes_through_squared_coordinate (hX.sub hY)
      (by simp [X,Y,collisionZero]) hd hM.differentiableAt P hP
    have hzero := hM.deriv.symm.trans hz
    change (ρ+η)/2=0 at hzero
    linear_combination 2*hzero
  · rintro rfl
    have hn : ρ≠0 := fun h => hne (by rw [h,neg_zero])
    obtain ⟨_,P,_,_,_,_,_,hs⟩ := hc.time_and_midpoint_of_squared_gap hρ hn
    exact ⟨P,hs.mono fun _ hp => hp.2⟩

#print axioms derivative_vanishes_through_squared_coordinate
#print axioms IsCollision.midpoint_from_gap_iff_opposite
end GaloisForLFunctions.GaloisTheoryOfZeros
