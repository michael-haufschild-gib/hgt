import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingHydrodynamics
import Mathlib.Tactic

/-!
# Traveling Hasimoto acceleration and momentum balance

For every derivative-certified nonvanishing curvature profile, the Galilean-complete velocity
`c + 2Dτ` satisfies the paper's acceleration law.  The corresponding momentum density and flux
satisfy the conservative momentum equation, with the inverse-curvature quantum stress as source.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def travelingHydroVelocityT
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  4 * c * D * k₀ ^ 2 * τ₀ * K.κ₁ (s - c * t) /
    (K.κ (s - c * t) : ℝ) ^ 3

noncomputable def travelingHydroVelocityX
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  -4 * D * k₀ ^ 2 * τ₀ * K.κ₁ (s - c * t) /
    (K.κ (s - c * t) : ℝ) ^ 3

noncomputable def travelingHydroAccelerationForce
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  -8 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2 * K.κ₁ (s - c * t) /
    (K.κ (s - c * t) : ℝ) ^ 5

theorem hasDerivAt_travelingHydroVelocity_space
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (travelingHydroVelocity D k₀ τ₀ c K t)
      (travelingHydroVelocityX D k₀ τ₀ c K t s) s := by
  have hinner : HasDerivAt (fun y : ℝ => y - c * t) 1 s :=
    (hasDerivAt_id s).sub_const _
  have hκ := (K.hasDerivAt (s - c * t)).scomp s hinner
  have hsq := hκ.pow 2
  have hdiv := (hasDerivAt_const s (2 * D * (k₀ ^ 2 * τ₀))).div hsq
    (pow_ne_zero 2 (K.κ (s - c * t)).ne_zero)
  have h := hdiv.const_add c
  change HasDerivAt
    (fun y : ℝ => c + 2 * D * (k₀ ^ 2 * τ₀ /
      (K.κ (y - c * t) : ℝ) ^ 2))
    (travelingHydroVelocityX D k₀ τ₀ c K t s) s
  have hfun :
      (fun y : ℝ => c + 2 * D * (k₀ ^ 2 * τ₀ /
        (K.κ (y - c * t) : ℝ) ^ 2)) =
        fun y : ℝ => c +
          (2 * D * (k₀ ^ 2 * τ₀)) /
            (((fun z : ℝ => (K.κ z : ℝ)) ∘ fun z : ℝ => z - c * t) y) ^ 2 := by
    funext y
    simp only [Function.comp_apply]
    ring
  rw [hfun]
  apply h.congr_deriv
  rw [travelingHydroVelocityX]
  simp only [Function.comp_apply, Pi.pow_apply, one_smul, Nat.cast_ofNat, zero_mul, zero_sub]
  field_simp [K.κ (s - c * t) |>.ne_zero]
  ring

theorem hasDerivAt_travelingHydroVelocity_time
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => travelingHydroVelocity D k₀ τ₀ c K r s)
      (travelingHydroVelocityT D k₀ τ₀ c K t s) t := by
  have hinner : HasDerivAt (fun r : ℝ => s - c * r) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub s
  have hκ := (K.hasDerivAt (s - c * t)).scomp t hinner
  have hsq := hκ.pow 2
  have hdiv := (hasDerivAt_const t (2 * D * (k₀ ^ 2 * τ₀))).div hsq
    (pow_ne_zero 2 (K.κ (s - c * t)).ne_zero)
  have h := hdiv.const_add c
  change HasDerivAt
    (fun r : ℝ => c + 2 * D * (k₀ ^ 2 * τ₀ /
      (K.κ (s - c * r) : ℝ) ^ 2))
    (travelingHydroVelocityT D k₀ τ₀ c K t s) t
  have hfun :
      (fun r : ℝ => c + 2 * D * (k₀ ^ 2 * τ₀ /
        (K.κ (s - c * r) : ℝ) ^ 2)) =
        fun r : ℝ => c +
          (2 * D * (k₀ ^ 2 * τ₀)) /
            (((fun z : ℝ => (K.κ z : ℝ)) ∘ fun z : ℝ => s - c * z) r) ^ 2 := by
    funext r
    simp only [Function.comp_apply]
    ring
  rw [hfun]
  apply h.congr_deriv
  rw [travelingHydroVelocityT]
  simp only [Function.comp_apply, Pi.pow_apply, smul_eq_mul, Nat.cast_ofNat, zero_mul, zero_sub]
  field_simp [K.κ (s - c * t) |>.ne_zero]
  ring

/-- Paper equation (54), valid after adding the traveling drift to the fluid velocity. -/
theorem travelingHydroAccelerationEquation
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    travelingHydroVelocityT D k₀ τ₀ c K t s +
        travelingHydroVelocity D k₀ τ₀ c K t s *
          travelingHydroVelocityX D k₀ τ₀ c K t s =
      travelingHydroAccelerationForce D k₀ τ₀ c K t s ∧
    HasDerivAt (fun r : ℝ => travelingHydroVelocity D k₀ τ₀ c K r s)
      (travelingHydroVelocityT D k₀ τ₀ c K t s) t ∧
    HasDerivAt (travelingHydroVelocity D k₀ τ₀ c K t)
      (travelingHydroVelocityX D k₀ τ₀ c K t s) s := by
  refine ⟨?_, hasDerivAt_travelingHydroVelocity_time D k₀ τ₀ c K t s,
    hasDerivAt_travelingHydroVelocity_space D k₀ τ₀ c K t s⟩
  rw [travelingHydroVelocityT, travelingHydroVelocity,
    travelingHydroVelocityX, travelingHydroAccelerationForce,
    fluidSpeed, torsion]
  field_simp [K.κ (s - c * t) |>.ne_zero]
  ring

noncomputable def travelingMomentumDensity
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  travelingMassCurrent D k₀ τ₀ c K t s

noncomputable def travelingMomentumDensityT
    (K : CurvatureProfileJet) (c t s : ℝ) : ℝ :=
  c * travelingDensityT K c t s

noncomputable def travelingMomentumFlux
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  travelingDensity K c t s * travelingHydroVelocity D k₀ τ₀ c K t s ^ 2

noncomputable def travelingQuantumStress
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  4 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2 /
    (K.κ (s - c * t) : ℝ) ^ 2

noncomputable def travelingQuantumStressX
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  -8 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2 * K.κ₁ (s - c * t) /
    (K.κ (s - c * t) : ℝ) ^ 3

noncomputable def travelingMomentumFluxX
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  c ^ 2 * travelingDensityX K c t s + travelingQuantumStressX D k₀ τ₀ c K t s

theorem travelingMomentumFlux_eq
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    travelingMomentumFlux D k₀ τ₀ c K t s =
      c ^ 2 * travelingDensity K c t s +
        4 * c * D * k₀ ^ 2 * τ₀ +
        travelingQuantumStress D k₀ τ₀ c K t s := by
  rw [travelingMomentumFlux, travelingHydroVelocity,
    travelingDensity, travelingQuantumStress]
  have hmass := density_mul_fluidSpeed D k₀ τ₀ (K.κ (s - c * t))
  have hmom := density_mul_fluidSpeed_sq D k₀ τ₀ (K.κ (s - c * t))
  simp only [density] at hmass hmom
  calc
    (K.κ (s - c * t) : ℝ) ^ 2 *
        (c + fluidSpeed D k₀ τ₀ (K.κ (s - c * t))) ^ 2 =
      c ^ 2 * (K.κ (s - c * t) : ℝ) ^ 2 +
        2 * c * ((K.κ (s - c * t) : ℝ) ^ 2 *
          fluidSpeed D k₀ τ₀ (K.κ (s - c * t))) +
        (K.κ (s - c * t) : ℝ) ^ 2 *
          fluidSpeed D k₀ τ₀ (K.κ (s - c * t)) ^ 2 := by ring
    _ = _ := by rw [hmass, hmom]; ring

theorem hasDerivAt_travelingMomentumDensity_time
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => travelingMomentumDensity D k₀ τ₀ c K r s)
      (travelingMomentumDensityT K c t s) t := by
  have hfun : (fun r : ℝ => travelingMomentumDensity D k₀ τ₀ c K r s) =
      fun r : ℝ => c * travelingDensity K c r s + 2 * D * k₀ ^ 2 * τ₀ := by
    funext r
    exact travelingMassCurrent_eq D k₀ τ₀ c K r s
  rw [hfun, travelingMomentumDensityT]
  exact (hasDerivAt_travelingDensity_time K c t s).const_mul c |>.add_const _

theorem hasDerivAt_travelingQuantumStress_space
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (travelingQuantumStress D k₀ τ₀ c K t)
      (travelingQuantumStressX D k₀ τ₀ c K t s) s := by
  have hinner : HasDerivAt (fun y : ℝ => y - c * t) 1 s :=
    (hasDerivAt_id s).sub_const _
  have hκ := (K.hasDerivAt (s - c * t)).scomp s hinner
  have hsq := hκ.pow 2
  have hdiv := (hasDerivAt_const s (4 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2)).div hsq
    (pow_ne_zero 2 (K.κ (s - c * t)).ne_zero)
  change HasDerivAt
    (fun y : ℝ => 4 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2 /
      (K.κ (y - c * t) : ℝ) ^ 2)
    (travelingQuantumStressX D k₀ τ₀ c K t s) s
  apply hdiv.congr_deriv
  rw [travelingQuantumStressX]
  simp only [Function.comp_apply, Pi.pow_apply, one_smul, Nat.cast_ofNat, zero_mul, zero_sub]
  field_simp [K.κ (s - c * t) |>.ne_zero]
  ring

theorem hasDerivAt_travelingMomentumFlux_space
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (travelingMomentumFlux D k₀ τ₀ c K t)
      (travelingMomentumFluxX D k₀ τ₀ c K t s) s := by
  have hfun : travelingMomentumFlux D k₀ τ₀ c K t =
      fun y : ℝ => c ^ 2 * travelingDensity K c t y +
        4 * c * D * k₀ ^ 2 * τ₀ + travelingQuantumStress D k₀ τ₀ c K t y := by
    funext y
    exact travelingMomentumFlux_eq D k₀ τ₀ c K t y
  rw [hfun, travelingMomentumFluxX]
  exact (((hasDerivAt_travelingDensity_space K c t s).const_mul (c ^ 2)).add_const _).add
    (hasDerivAt_travelingQuantumStress_space D k₀ τ₀ c K t s)

/-- Paper equation (56), upgraded to the Galilean-complete traveling flow. -/
theorem travelingMomentumEquation
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    travelingMomentumDensityT K c t s +
        travelingMomentumFluxX D k₀ τ₀ c K t s =
      travelingQuantumStressX D k₀ τ₀ c K t s ∧
    HasDerivAt (fun r : ℝ => travelingMomentumDensity D k₀ τ₀ c K r s)
      (travelingMomentumDensityT K c t s) t ∧
    HasDerivAt (travelingMomentumFlux D k₀ τ₀ c K t)
      (travelingMomentumFluxX D k₀ τ₀ c K t s) s ∧
    HasDerivAt (travelingQuantumStress D k₀ τ₀ c K t)
      (travelingQuantumStressX D k₀ τ₀ c K t s) s := by
  refine ⟨?_, hasDerivAt_travelingMomentumDensity_time D k₀ τ₀ c K t s,
    hasDerivAt_travelingMomentumFlux_space D k₀ τ₀ c K t s,
    hasDerivAt_travelingQuantumStress_space D k₀ τ₀ c K t s⟩
  rw [travelingMomentumDensityT, travelingMomentumFluxX,
    travelingDensityT, travelingDensityX]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
