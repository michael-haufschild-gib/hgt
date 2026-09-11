import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPulseHorizonSource

/-!
# Fixed-clock moment of the original radial pulse contact

At every exterior radius, the actual source contact with the explicit incoming
field retains only mixed-onset and derivative-square terms. Their unchanged
common exponent is -6. The exact translation moment vanishes before any horizon
limit is taken. This does not assert vanishing of the causal pulse response or
identify the temporal test with the complete physical left-QNM action.
-/

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMPulseHorizonSource
open D4BMJointSource D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse
open D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMLaplaceRadial
open D4BMIncomingClockTranslation D4BMSourceClockTranslation
noncomputable section
set_option autoImplicit false

private theorem incoming_time_coefficient (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r v : ℝ) (z : Point) (j : Fin 2) :
    (incomingJet q branch a r v z j).first 0 =
      (responseProfile (physicalRate q branch) a r*fullAngularCovector q branch j z+
        profile (physicalRate q branch) a r*fullSquareCovector q j z)*
          timeOnsetFirst (2*physicalRate q branch) v := by
  change (responseProfile (physicalRate q branch) a r*timeOnsetFirst (2*physicalRate q branch) v)*
      fullAngularCovector q branch j z+
    (profile (physicalRate q branch) a r*timeOnsetFirst (2*physicalRate q branch) v)*
      fullSquareCovector q j z = _
  ring

private theorem incoming_radial_coefficient (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r v : ℝ) (z : Point) (j : Fin 2) :
    (incomingJet q branch a r v z j).first 1 =
      (responseProfileFirst (physicalRate q branch) a r*fullAngularCovector q branch j z+
        profileFirst (physicalRate q branch) a r*fullSquareCovector q j z)*
          timeOnset (2*physicalRate q branch) v := by
  change (responseProfileFirst (physicalRate q branch) a r*timeOnset (2*physicalRate q branch) v)*
      fullAngularCovector q branch j z+
    (profileFirst (physicalRate q branch) a r*timeOnset (2*physicalRate q branch) v)*
      fullSquareCovector q j z = _
  ring

/-- At every radius, both differentiated incoming jets retain only the two contact profiles. -/
theorem compactPulseContact_profile (q : XiZeroCopy) (a b : ℂ) (u : ℝ) (z : Point) :
    let r := u⁻¹
    let amp := fun branch : Bool => if branch then a else b
    let A := fun branch j =>
      responseProfile (physicalRate q branch) (amp branch) r*fullAngularCovector q branch j z+
        profile (physicalRate q branch) (amp branch) r*fullSquareCovector q j z
    let D := fun branch j =>
      responseProfileFirst (physicalRate q branch) (amp branch) r*fullAngularCovector q branch j z+
        profileFirst (physicalRate q branch) (amp branch) r*fullSquareCovector q j z
    let P := fun branch j =>
      2*power (2*physicalRate q branch) (1+u)*(amp branch)^2/((u:ℂ)*(1+(u:ℂ)))*
        (((2*physicalRate q branch+1)*(u:ℂ)+1)*fullAngularCovector q branch j z-
          physicalRate q branch*(physicalRate q branch-1)/4*(u:ℂ)^2*
            ((2*physicalRate q branch+3)*(u:ℂ)+3)*fullSquareCovector q j z)
    let B := (∑ j : Fin 2,
      ((((r:ℂ)^2-1)*D true j+2*physicalRate q true*A true j)*P false j-
        (((r:ℂ)^2-1)*D false j+2*physicalRate q false*A false j)*P true j))/(r:ℂ)^2
    let C := (∑ j : Fin 2, (A true j*P false j-A false j*P true j))/(r:ℂ)^2
    ∀ v, compactPulseContact q a b v u z =
      horizonProfile 0 B C v*Complex.exp (-6*(v:ℂ)) := by
  intro r amp A D P B C v
  have he : Complex.exp (2*physicalRate q true*(v:ℂ))*
      Complex.exp (2*physicalRate q false*(v:ℂ)) = Complex.exp (-6*(v:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [physicalRate,Bool.false_eq_true,↓reduceIte]
    ring
  simp only [compactPulseContact,incoming_time_coefficient,incoming_radial_coefficient]
  let f : ℂ := (r:ℂ)^2-1
  let dχ : ℂ := ((deriv Real.smoothTransition v:ℝ):ℂ)
  change (∑ j : Fin 2,
    ((f*(D true j*timeOnset (2*physicalRate q true) v)+
        A true j*timeOnsetFirst (2*physicalRate q true) v)*
      (P false j*dχ*Complex.exp (2*physicalRate q false*(v:ℂ))) -
    (f*(D false j*timeOnset (2*physicalRate q false) v)+
        A false j*timeOnsetFirst (2*physicalRate q false) v)*
      (P true j*dχ*Complex.exp (2*physicalRate q true*(v:ℂ))))) / (r:ℂ)^2 =
    horizonProfile 0 B C v*Complex.exp (-6*(v:ℂ))
  dsimp only [B,C,f,dχ]
  simp only [timeOnset,timeOnsetFirst,horizonProfile,Fin.sum_univ_two]
  rw [← he]
  ring

/-- The full original radial contact has zero translation mass before any horizon limit. -/
theorem compactPulseContact_clockMoment (q : XiZeroCopy) (a b : ℂ) (u : ℝ)
    (z : Point) (h : NNReal) :
    clockMoment (-6) h (fun v => compactPulseContact q a b v u z) = 0 := by
  simp only [compactPulseContact_profile]
  rw [horizonProfile_clockMoment]
  simp

/-- The same zero moment holds with the original static-chart source normalization. -/
theorem originalPulseContact_clockMoment (q : XiZeroCopy) (a b : ℂ)
    (x : Set.Iio (0:ℝ)) (z : UpperHalfPlane) (h : NNReal) :
    clockMoment (-6) h (fun v => originalPulseContact q a b v x (coordinates z)) = 0 := by
  have he : (fun v => originalPulseContact q a b v x (coordinates z)) =
      fun v => compactPulseContact q a b v (radialUnit x) (coordinates z) := by
    funext v
    exact originalPulseContact_eq_compact q a b v x z
  rw [he]
  exact compactPulseContact_clockMoment q a b (radialUnit x) (coordinates z) h

end
end RHTower.D4BMPulseHorizonSource
