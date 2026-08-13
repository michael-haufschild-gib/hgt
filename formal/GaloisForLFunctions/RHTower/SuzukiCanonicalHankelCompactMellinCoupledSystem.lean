import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelCompactMellinSystem

/-!
# Suzuki's compact Mellin coupled system

The strong `L¹` equation (4.13) is paired with the literal moving-aperture Mellin character.
The endpoint contribution from differentiating the moving cutoff is retained.  Mellin integration
by parts on the opposite-sign Euler field then gives a closed inhomogeneous two-sign system at
every aperture `a > 1`, including arithmetic cusp apertures.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Pairing the cutoff Euler field with a clamped Mellin character is its literal interval
integral.  This is the exact scalar bridge from the strong `L¹` equation (4.13). -/
theorem suzukiIntervalL1ContinuousPairing_cutoff_eulerPhi_eq_integral
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B)
    (z : ℂ) :
    suzukiIntervalL1ContinuousPairing B
        (suzukiClampedMellinWeight
          (B := B) (show 0 < 1 / B by positivity) z)
        (suzukiApertureCutoffL1 a B
          (suzukiHankelEulerPhiL1 epsilon omega a B homega ha (by linarith))) =
      ∫ x in (0 : ℝ)..a,
        suzukiClampedMellinWeightValue (1 / B) z x *
          suzukiHankelEulerPhi epsilon omega a homega ha x := by
  let w := suzukiClampedMellinWeight
    (B := B) (show 0 < 1 / B by positivity) z
  let E := suzukiHankelEulerPhiL1 epsilon omega a B homega ha
    (by linarith : 0 < B)
  let F : ℝ → ℂ := fun x =>
    suzukiClampedMellinWeightValue (1 / B) z x *
      suzukiHankelEulerPhi epsilon omega a homega ha x
  have hcut := suzukiApertureCutoffL1_ae a B E
  have hE := suzukiHankelEulerPhiL1_ae epsilon homega ha (by linarith : 0 < B)
  rw [suzukiIntervalL1ContinuousPairing_eq_integral]
  calc
    (∫ x : ClosedInterval 0 B,
        w x * suzukiApertureCutoffL1 a B E x ∂volume) =
        ∫ x : ClosedInterval 0 B,
          (suzukiApertureSet a B).indicator (fun x => F (x : ℝ)) x
            ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcut, hE] with x hcutx hEx
      rw [hcutx]
      by_cases hx : x ∈ suzukiApertureSet a B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hEx]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    _ = ∫ x in (0 : ℝ)..a, F x :=
      integral_subtype_apertureSet_eq_intervalIntegral B a (by linarith) haB.le F
    _ = _ := rfl

/-- Exact compact-Mellin form of Suzuki's equation (4.13).  Unlike the paper's subsequent
tail-integral calculation, this identity is valid at every `a > 1`; no arithmetic regular-locus
exception remains. -/
theorem hasDerivAt_suzukiHankelCompactMellinRight_coupled
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelCompactMellinRight epsilon omega homega z)
      ((-((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) *
            suzukiHankelCompactMellin epsilon omega a homega ha z +
          suzukiHankelMu omega a homega ha *
            suzukiClampedMellinWeightValue (1 / (a + 1)) z a -
          I * z * suzukiHankelCompactMellin
            epsilon.opposite omega a homega ha z) / (a : ℂ)) a := by
  let B : ℝ := a + 1
  let hB : 1 < B := by dsimp only [B]; linarith
  let haB : a < B := by dsimp only [B]; linarith
  let w := suzukiClampedMellinWeight
    (B := B) (show 0 < 1 / B by positivity) z
  let L := suzukiIntervalL1ContinuousPairing B w
  let dP := suzukiFixedWindowPhiDerivativeL1
    epsilon omega B homega hB a (by linarith : 0 < a) haB
  let P := suzukiFixedWindowPhiL1 epsilon omega B homega hB a
  let Eopp := suzukiHankelEulerPhiL1
    epsilon.opposite omega a B homega ha (by linarith : 0 < B)
  let C := suzukiHankelCompactMellin epsilon omega a homega ha z
  let Copp := suzukiHankelCompactMellin epsilon.opposite omega a homega ha z
  let mu := suzukiHankelMu omega a homega ha
  let D := L (suzukiApertureCutoffL1 a B dP)
  have h413 := suzuki_equation_413_L1 epsilon homega hB ha haB
  have hpair := congrArg (fun f : IntervalL1 0 B =>
    L (suzukiApertureCutoffL1 a B f)) h413
  change L (suzukiApertureCutoffL1 a B
      ((a : ℂ) • dP + ((1 / 2 : ℂ) + epsilon.coeff * mu) • P)) =
    L (suzukiApertureCutoffL1 a B Eopp) at hpair
  simp only [map_add, map_smul, smul_eq_mul] at hpair
  have hPpair : L (suzukiApertureCutoffL1 a B P) = C := by
    exact suzukiIntervalL1ContinuousPairing_fixedWindowPhi_eq_compactMellin
      epsilon homega hB ha haB z
  have hEpair :
      L (suzukiApertureCutoffL1 a B Eopp) =
        (a : ℂ) * suzukiHankelPhiGlobal
            epsilon.opposite omega a homega ha a * w ⟨a, ⟨by linarith, haB.le⟩⟩ -
          I * z * Copp := by
    rw [suzukiIntervalL1ContinuousPairing_cutoff_eulerPhi_eq_integral
      epsilon.opposite homega hB ha haB z]
    have hIBP := suzukiHankelEulerPhi_compactMellin_integrationByParts
      epsilon.opposite homega ha haB z
    simpa only [w, B, Eopp, Copp, suzukiClampedMellinWeight_apply] using hIBP
  have hD :
      (a : ℂ) * D + ((1 / 2 : ℂ) + epsilon.coeff * mu) * C =
        (a : ℂ) * suzukiHankelPhiGlobal
            epsilon.opposite omega a homega ha a * w ⟨a, ⟨by linarith, haB.le⟩⟩ -
          I * z * Copp := by
    rw [hPpair, hEpair] at hpair
    exact hpair
  have hderiv := hasDerivAt_suzukiHankelCompactMellinRight epsilon homega ha z
  have hmu := suzukiHankelMu_eq_sign_sum epsilon homega ha
  change mu = (a : ℂ) *
      suzukiHankelPhiGlobal epsilon omega a homega ha a +
    (a : ℂ) * suzukiHankelPhiGlobal
      epsilon.opposite omega a homega ha a at hmu
  have ha0C : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  change HasDerivAt (suzukiHankelCompactMellinRight epsilon omega homega z)
    (D + w ⟨a, ⟨by linarith, haB.le⟩⟩ *
      suzukiHankelPhiGlobal epsilon omega a homega ha a) a at hderiv
  have hcoefficient :
      D + w ⟨a, ⟨by linarith, haB.le⟩⟩ *
          suzukiHankelPhiGlobal epsilon omega a homega ha a =
        (-((1 / 2 : ℂ) + epsilon.coeff * mu) * C +
          mu * w ⟨a, ⟨by linarith, haB.le⟩⟩ - I * z * Copp) / (a : ℂ) := by
    rw [eq_div_iff ha0C]
    calc
      (D + w ⟨a, ⟨by linarith, haB.le⟩⟩ *
          suzukiHankelPhiGlobal epsilon omega a homega ha a) * (a : ℂ) =
          (a : ℂ) * D +
            (a : ℂ) * w ⟨a, ⟨by linarith, haB.le⟩⟩ *
              suzukiHankelPhiGlobal epsilon omega a homega ha a := by
        ring
      _ = -((1 / 2 : ℂ) + epsilon.coeff * mu) * C +
            (a : ℂ) * suzukiHankelPhiGlobal
                epsilon.opposite omega a homega ha a *
              w ⟨a, ⟨by linarith, haB.le⟩⟩ -
            I * z * Copp +
            (a : ℂ) * w ⟨a, ⟨by linarith, haB.le⟩⟩ *
              suzukiHankelPhiGlobal epsilon omega a homega ha a := by
        linear_combination hD
      _ = -((1 / 2 : ℂ) + epsilon.coeff * mu) * C +
            mu * w ⟨a, ⟨by linarith, haB.le⟩⟩ - I * z * Copp := by
        rw [hmu]
        ring
  simpa only [B, w, C, Copp, mu, suzukiClampedMellinWeight_apply] using
    hderiv.congr_deriv hcoefficient

end RHTower
