import GaloisForLFunctions.RHTower.ThetaPrimeResonantModulusDecrease
import GaloisForLFunctions.RHTower.CCMPositiveNoetherPhaseWitness

/-!
# Actual prime-dominated localization and its conservative phase flow

At a genuine prime resonance, both localization errors are negative and the
prime error is strictly more negative than the continuous error. The source
and its modulus still have positive full Weil energies. Their compact binary
phase gives a positive arithmetic potential and an exact conservative flow.
The flow is the previously constructed selected positive-speed energy curve;
its kinetic term is not asserted to be canonical arithmetic dynamics.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

private theorem primeEnergy_ordered_difference (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y) :
    thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction =
      -2 * (thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
        thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi - psi)).toBoundedContinuousFunction) := by
  have hsq (x : ℝ) : ‖thetaComplexify (phi + psi) x‖ ^ 2 =
      ‖thetaComplexify (phi - psi) x‖ ^ 2 := by
    have hzero : phi x * psi x = 0 := by
      by_cases hp : phi x = 0
      · simp [hp]
      by_cases hq : psi x = 0
      · simp [hq]
      have := hsep x hq x hp
      linarith
    simp only [thetaComplexify_apply, add_apply, sub_apply, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    nlinarith only [hzero]
  have hdiag : thetaPrimeScalingDiagonal thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction =
      thetaPrimeScalingDiagonal thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction := by
    unfold thetaPrimeScalingDiagonal
    simp only [SchwartzMap.toBoundedContinuousFunction_apply, hsq]
  rw [thetaPrimeScalingEnergy_eq_diagonal_sub_cross,
    thetaPrimeScalingEnergy_eq_diagonal_sub_cross, hdiag]
  ring

theorem exists_ccmPrime_resonant_localization_dominance :
    ∃ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)), HasCompactSupport theta ∧
      (∀ x, v x = (‖u x‖ : ℂ)) ∧
      (∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) ∧
      ccmCosLocalizedSource u theta = v ∧
      (∀ x, ccmSinLocalizedSource u theta x = 0) ∧
      ccmThetaPrimeLocalizationError u theta < ccmThetaContinuousLocalizationError u theta ∧
      ccmThetaContinuousLocalizationError u theta < 0 ∧
      0 < ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector ∧
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector <
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  obtain ⟨n, phi, psi, r, _, _, hr, hgap, hpc, hqc, hps, hqs,
    hp, hq, _, _, hmod, _, hpositive, hdecrease⟩ :=
    exists_arbitrarily_large_prime_resonant_modulus_decrease 0
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      screwSignThreshold ≤ x - y := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    linarith [hx.1, hy.2]
  have hsep0 := fun x hx y hy => screwSignThreshold_pos.trans_le (hsep x hx y hy)
  have hd : Disjoint (tsupport phi) (tsupport psi) :=
    disjoint_tsupport_of_positive_gap phi psi screwSignThreshold_pos hsep
  have hcross := thetaGammaPolarGroundCrossPairing_pos_of_balls phi psi hr hps hqs hp hq hgap
  obtain ⟨theta, htc, htp, htq⟩ :=
    exists_schwartz_separating_angle isClosed_closure hqc hd Real.pi
  obtain ⟨A, hA, hbound⟩ := (hpc.union hqc).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hsub : tsupport phi ∪ tsupport psi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x hx)
  have hfsub : tsupport (phi - psi : 𝓢(ℝ, ℝ)) ⊆ Ioo (-a.1) a.1 :=
    (tsupport_sub phi psi).trans hsub
  have hgsub : tsupport (phi + psi : 𝓢(ℝ, ℝ)) ⊆ Ioo (-a.1) a.1 :=
    (tsupport_add phi psi).trans hsub
  let u := ccmThetaSourceOfCompactRealProfile a (phi - psi) (hpc.sub hqc) hfsub
  let v := ccmThetaSourceOfCompactRealProfile a (phi + psi) (hpc.add hqc) hgsub
  have hu (x : ℝ) : u x = (thetaCuspFullSource x : ℂ) * ((phi x - psi x : ℝ) : ℂ) := rfl
  have hv (x : ℝ) : v x = (thetaCuspFullSource x : ℂ) * ((phi x + psi x : ℝ) : ℂ) := rfl
  have hvalues (x : ℝ) :
      Real.cos (theta x) * (phi x - psi x) = phi x + psi x ∧
      Real.sin (theta x) * (phi x - psi x) = 0 := by
    by_cases hphi : phi x = 0
    · by_cases hpsi : psi x = 0
      · simp only [hphi, hpsi, sub_self, add_zero, mul_zero, and_self]
      · simp [hphi, htq x (subset_tsupport _ hpsi)]
    · have hpsi : psi x = 0 := by
        by_contra hpsi
        exact Set.disjoint_left.mp hd (subset_tsupport _ hphi) (subset_tsupport _ hpsi)
      simp [hpsi, htp x (subset_tsupport _ hphi)]
  have hcos : ccmCosLocalizedSource u theta = v := by
    apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
    funext x
    rw [ccmCosLocalizedSource_apply, hu, hv, mul_left_comm, ← Complex.ofReal_mul, (hvalues x).1]
  have hsin (x : ℝ) : ccmSinLocalizedSource u theta x = 0 := by
    rw [ccmSinLocalizedSource_apply, hu, mul_left_comm, ← Complex.ofReal_mul,
      (hvalues x).2, Complex.ofReal_zero, mul_zero]
  have hphase : ∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi := by
    intro x hx
    by_cases hphi : phi x = 0
    · have hpsi : psi x ≠ 0 := by
        intro hpsi
        exact hx (by rw [hu, hphi, hpsi]; simp)
      exact Or.inr (htq x (subset_tsupport _ hpsi))
    · exact Or.inl (htp x (subset_tsupport _ hphi))
  have hsinprofile : ccmThetaGroundProfile (ccmSinLocalizedSource u theta) = 0 := by
    ext x
    simp only [ccmThetaGroundProfile_apply, hsin, zero_div, zero_apply]
  have hzero : thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
      (0 : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction = 0 := by
    simp only [thetaPrimeScalingEnergy, thetaPrimeScalingEnergyDensity, thetaPrimeProfileIncrement,
      SchwartzMap.toBoundedContinuousFunction_apply, zero_apply, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, integral_zero]
  have hprime : ccmThetaPrimeLocalizationError u theta =
      -2 * (thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
        thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi - psi)).toBoundedContinuousFunction) := by
    rw [ccmThetaPrimeLocalizationError_eq, hcos, hsinprofile, hzero, add_zero,
      show ccmThetaGroundProfile v = thetaComplexify (phi + psi) from
        ccmThetaGroundProfile_ofCompactRealProfile _ _ _ _,
      show ccmThetaGroundProfile u = thetaComplexify (phi - psi) from
        ccmThetaGroundProfile_ofCompactRealProfile _ _ _ _]
    exact primeEnergy_ordered_difference phi psi hsep0
  have hloc := ccmRestrictedWeilSourceQuadratic_localization u theta
  rw [hcos, ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hsin, add_zero] at hloc
  have hdiff := thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep0
  have hQu : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      thetaRealArithmeticQuadratic (phi - psi) := ccmCompactRealProfileEnergy_eq _ _ _ _
  have hQv : ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector =
      thetaRealArithmeticQuadratic (phi + psi) := ccmCompactRealProfileEnergy_eq _ _ _ _
  have hcontinuous : ccmThetaContinuousLocalizationError u theta =
      -4 * thetaGammaPolarGroundCrossPairing phi psi := by
    rw [hQu, hQv] at hloc
    linarith only [hloc, hdiff, hprime]
  refine ⟨a, u, v, theta, htc, ?_, hphase, hcos, hsin, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hu, hv, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x), ← Complex.ofReal_mul]
    exact congrArg (fun z : ℝ => ((thetaCuspFullSource x * z : ℝ) : ℂ)) (hmod x)
  · rw [hQu, hQv] at hloc
    linarith only [hloc, hdecrease]
  · rw [hcontinuous]
    linarith
  · rwa [hQv]
  · rwa [hQv, hQu]

/-- Every continuous local scalar potential leaves this strict modulus decrease unchanged. -/
theorem exists_ccmSmooth_modulus_decrease_all_local_potentials :
    ∃ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a),
      (∀ x, v x = (‖u x‖ : ℂ)) ∧
      ∀ V : C(ℝ, ℝ), ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector +
          ccmSmoothLocalPotentialEnergy V v <
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
          ccmSmoothLocalPotentialEnergy V u := by
  obtain ⟨a, u, v, _, _, hmod, _, _, _, _, _, _, hlt⟩ :=
    exists_ccmPrime_resonant_localization_dominance
  refine ⟨a, u, v, hmod, fun V => ?_⟩
  have heq : ccmSmoothLocalPotentialEnergy V u = ccmSmoothLocalPotentialEnergy V v := by
    unfold ccmSmoothLocalPotentialEnergy
    apply integral_congr_ae
    filter_upwards with x
    rw [hmod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [heq]
  linarith

theorem exists_ccmPrime_resonant_positive_noether_flow :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B : ℝ), HasCompactSupport theta ∧ B < 0 ∧
      ccmThetaPrimeLocalizationError u theta < ccmThetaContinuousLocalizationError u theta ∧
      ccmThetaContinuousLocalizationError u theta < 0 ∧
      (∀ q : ℝ, ccmPhaseLocalizationEnergy u theta q =
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + arithmeticPhasePotential B q) ∧
      (∀ q : ℝ, 0 < ccmPhaseLocalizationEnergy u theta q) ∧
      (∀ q t : ℝ, (deriv (arithmeticPhaseFlow B q) t) ^ 2 / 2 +
        ccmPhaseLocalizationEnergy u theta (arithmeticPhaseFlow B q t) =
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + 2 * |B| + 1) ∧
      (∀ t : ℝ, deriv (deriv (arithmeticPhaseTrajectory B)) t =
        -deriv (ccmPhaseLocalizationEnergy u theta) (arithmeticPhaseTrajectory B t)) := by
  obtain ⟨a, u, v, theta, htc, _, hphase, hcos, hsin, hdom, hcont, hQv, hless⟩ :=
    exists_ccmPrime_resonant_localization_dominance
  let B := (ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2
  have hB : B < 0 := by dsimp only [B]; linarith
  have he (q : ℝ) : ccmPhaseLocalizationEnergy u theta q =
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + arithmeticPhasePotential B q :=
    ccmPhaseLocalizationEnergy_eq u theta hphase q
  have hd := hasDerivAt_ccmPhaseLocalizationEnergy u theta hphase
  have hscaled : ccmScaledPhaseAngle theta Real.pi = theta := by
    rw [ccmScaledPhaseAngle, div_self Real.pi_ne_zero, one_smul]
  have hEpi : ccmPhaseLocalizationEnergy u theta Real.pi =
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector := by
    rw [ccmPhaseLocalizationEnergy, hscaled, hcos,
      ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hsin, add_zero]
  refine ⟨a, u, theta, B, htc, hB, hdom, hcont, he, ?_, ?_, ?_⟩
  · intro q
    have hpi := he Real.pi
    rw [hEpi, arithmeticPhasePotential, Real.cos_pi] at hpi
    rw [he, arithmeticPhasePotential]
    have h := mul_le_mul_of_nonpos_left (show 1 - Real.cos q ≤ 2 by
      linarith [Real.neg_one_le_cos q]) hB.le
    linarith only [hQv, hpi, h]
  · intro q t
    rw [he]
    have h := arithmeticPhaseFlow_energy B q t
    unfold arithmeticPhaseMechanicalEnergy arithmeticPhaseEnergyLevel at h
    linarith only [h]
  · intro t
    rw [arithmeticPhaseTrajectory_newton, (hd _).deriv, neg_mul]

end RHTower
