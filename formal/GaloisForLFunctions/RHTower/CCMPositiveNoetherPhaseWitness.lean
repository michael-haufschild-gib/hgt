import GaloisForLFunctions.RHTower.ThetaFarPositiveInterference
import GaloisForLFunctions.RHTower.CCMFarGapPhaseCoercivity
import GaloisForLFunctions.RHTower.CCMArithmeticPhaseFlow

/-!
# A nonconstant arithmetic Noether potential with positive full Weil baseline

Far separated positive-energy modulus witnesses produce an actual compact smooth
source whose phase potential is `Q(u) + B (1 - cos q)`, with both `Q(u)` and `B`
strictly positive. The previously constructed action and global phase flow thus
have an explicitly positive arithmetic potential and an exact conserved charge.

The flow remains the selected positive-speed energy curve of the inverse-Noether
construction. This supplies no positivity claim for arbitrary Weil sources.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem exists_ccmArithmetic_positive_baseline_phase_potential :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B : ℝ),
      0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ∧ 0 < B ∧
      HasCompactSupport theta ∧
      (∀ q : ℝ, ccmPhaseLocalizationEnergy u theta q =
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + B * (1 - Real.cos q)) ∧
      (∀ q : ℝ, HasDerivAt (ccmPhaseLocalizationEnergy u theta) (B * Real.sin q) q) ∧
      (∀ q : ℝ, 0 < ccmPhaseLocalizationEnergy u theta q) := by
  obtain ⟨phi, psi, c, r, _, hfar, hpc, hqc, hps, hqs, _, _, _, hminus, hinc⟩ :=
    exists_arbitrarily_far_positive_modulus_increase 1
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 1 ≤ x - y := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    linarith [hx.1, hy.2]
  have hd : Disjoint (tsupport phi) (tsupport psi) :=
    disjoint_tsupport_of_positive_gap phi psi (by positivity : (0 : ℝ) < 1) hsep
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
  have hQu : 0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
    simpa only [u, ccmCompactRealProfileEnergy_eq] using hminus
  have hQinc : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector <
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector := by
    simpa only [u, v, ccmCompactRealProfileEnergy_eq] using hinc
  have hscaled : ccmScaledPhaseAngle theta Real.pi = theta := by
    rw [ccmScaledPhaseAngle, div_self Real.pi_ne_zero, one_smul]
  have hEpi : ccmPhaseLocalizationEnergy u theta Real.pi =
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector := by
    rw [ccmPhaseLocalizationEnergy, hscaled, hcos,
      ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hsin, add_zero]
  let B := (ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2
  have he (q : ℝ) : ccmPhaseLocalizationEnergy u theta q =
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + B * (1 - Real.cos q) :=
    ccmPhaseLocalizationEnergy_eq u theta hphase q
  have hB : 0 < B := by
    have h := he Real.pi
    rw [hEpi, Real.cos_pi] at h
    linarith
  refine ⟨a, u, theta, B, hQu, hB, htc, he,
    hasDerivAt_ccmPhaseLocalizationEnergy u theta hphase, fun q => ?_⟩
  rw [he]
  exact add_pos_of_pos_of_nonneg hQu (mul_nonneg hB.le (sub_nonneg.mpr (Real.cos_le_one q)))

/-- Positive actual arithmetic potential, conservative global flow, and the exact Newton law
for the action already constructed from that potential. -/
theorem exists_ccmArithmetic_positive_noether_flow :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B : ℝ),
      0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ∧ 0 < B ∧
      HasCompactSupport theta ∧
      (∀ q : ℝ, ccmPhaseLocalizationEnergy u theta q =
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + arithmeticPhasePotential B q) ∧
      (∀ q : ℝ, 0 < ccmPhaseLocalizationEnergy u theta q) ∧
      (∀ q t : ℝ, (deriv (arithmeticPhaseFlow B q) t) ^ 2 / 2 +
        ccmPhaseLocalizationEnergy u theta (arithmeticPhaseFlow B q t) =
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + 2 * B + 1) ∧
      (∀ t : ℝ, deriv (deriv (arithmeticPhaseTrajectory B)) t =
        -deriv (ccmPhaseLocalizationEnergy u theta) (arithmeticPhaseTrajectory B t)) := by
  obtain ⟨a, u, theta, B, hQu, hB, htc, he, hd, hp⟩ :=
    exists_ccmArithmetic_positive_baseline_phase_potential
  refine ⟨a, u, theta, B, hQu, hB, htc, he, hp, ?_, ?_⟩
  · intro q t
    rw [he]
    have h := arithmeticPhaseFlow_energy B q t
    unfold arithmeticPhaseMechanicalEnergy arithmeticPhaseEnergyLevel arithmeticPhasePotential at h
    rw [abs_of_pos hB] at h
    linarith
  · intro t
    rw [arithmeticPhaseTrajectory_newton, (hd _).deriv, neg_mul]

end RHTower
