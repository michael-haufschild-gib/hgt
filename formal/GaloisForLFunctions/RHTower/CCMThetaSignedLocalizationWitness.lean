import GaloisForLFunctions.RHTower.CCMThetaSeparatedAngle
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarInverse

/-!
# Both signs of the exact arithmetic localization error

A single compact smooth angle swaps a signed source and its pointwise
modulus. Both prime localization errors vanish exactly, because no prime
translation joins the two support components. The full continuous errors
are nonzero and opposite. This refutes a universal favorable-error sign;
it does not give a negative Weil quadratic or refute RH.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmSmoothSourceQuadratic_eq_zero_of_pointwise {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (hu : ∀ x, u x = 0) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector = 0 := by
  have hp : ccmThetaGroundProfile u = 0 := by
    ext x
    simp only [ccmThetaGroundProfile_apply, hu, zero_div, zero_apply]
  rw [ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference, hp]
  simp only [thetaPrimeScalingEnergy, thetaPrimeScalingEnergyDensity, thetaPrimeProfileIncrement,
    SchwartzMap.toBoundedContinuousFunction_apply, zero_apply, sub_self, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, integral_zero,
    thetaGammaPolarScalingEnergy, thetaGammaPolarScalingDensity, mul_zero]

/-- A phase constant on each of two prime-disconnected components costs no prime localization error. -/
theorem ccmThetaPrimeLocalizationError_eq_zero_of_separated_components
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (theta : 𝓢(ℝ, ℝ)) (phi psi : ℝ → ℝ) (phase : ℝ)
    (hs : Function.support u ⊆ Function.support phi ∪ Function.support psi)
    (hp : ∀ x ∈ Function.support phi, theta x = 0)
    (hq : ∀ x ∈ Function.support psi, theta x = phase)
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) :
    ccmThetaPrimeLocalizationError u theta = 0 := by
  unfold ccmThetaPrimeLocalizationError
  apply integral_eq_zero_of_ae
  filter_upwards with p
  by_cases hn : 2 ≤ p.1
  · by_cases hx : u p.2 = 0
    · simp [ccmThetaPrimeLocalizationDensity, ccmThetaLocalizationCross, hx]
    by_cases hy : u (p.2 + Real.log p.1) = 0
    · simp [ccmThetaPrimeLocalizationDensity, ccmThetaLocalizationCross, hy]
    have hphase : theta (p.2 + Real.log p.1) = theta p.2 := by
      rcases hs hx with hx | hx <;> rcases hs hy with hy | hy
      · rw [hp _ hx, hp _ hy]
      · exact False.elim (hatom _ hy _ hx p.1 hn (by ring))
      · have hlog : 0 ≤ Real.log p.1 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.1))
        have := hsep _ hx _ hy
        linarith
      · rw [hq _ hx, hq _ hy]
    simp only [ccmThetaPrimeLocalizationDensity, ccmThetaLocalizationCross,
      thetaLocalizationWeight, hphase, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, zero_mul, mul_zero, Pi.zero_apply]
  · have hn' : p.1 = 0 ∨ p.1 = 1 := by omega
    rcases hn' with hn' | hn' <;> simp [ccmThetaPrimeLocalizationDensity, hn']

private theorem separator_flip_values (phi psi theta : ℝ → ℝ)
    (hd : Disjoint (tsupport phi) (tsupport psi))
    (hp : ∀ x ∈ tsupport phi, theta x = 0)
    (hq : ∀ x ∈ tsupport psi, theta x = Real.pi) (x : ℝ) :
    Real.cos (theta x) * (phi x - psi x) = phi x + psi x ∧
    Real.cos (theta x) * (phi x + psi x) = phi x - psi x ∧
    Real.sin (theta x) * (phi x - psi x) = 0 ∧
    Real.sin (theta x) * (phi x + psi x) = 0 := by
  by_cases hphi : phi x = 0
  · by_cases hpsi : psi x = 0
    · simp [hphi, hpsi]
    · simp [hphi, hq x (subset_tsupport _ hpsi)]
  · have hpsi : psi x = 0 := by
      by_contra hpsi
      exact Set.disjoint_left.mp hd (subset_tsupport _ hphi) (subset_tsupport _ hpsi)
    simp [hpsi, hp x (subset_tsupport _ hphi)]

/-- Same compact angle, same pointwise mass, zero prime error, opposite nonzero continuous errors. -/
theorem exists_ccmTheta_localization_error_both_signs :
    ∃ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)),
      HasCompactSupport theta ∧ (∀ x, v x = (‖u x‖ : ℂ)) ∧
      (∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) ∧
      ccmCosLocalizedSource u theta = v ∧ ccmCosLocalizedSource v theta = u ∧
      (∀ x, ccmSinLocalizedSource u theta x = 0) ∧
      (∀ x, ccmSinLocalizedSource v theta x = 0) ∧
      ccmThetaPrimeLocalizationError u theta = 0 ∧
      ccmThetaPrimeLocalizationError v theta = 0 ∧
      ccmThetaContinuousLocalizationError u theta < 0 ∧
      0 < ccmThetaContinuousLocalizationError v theta ∧
      ccmThetaContinuousLocalizationError u theta =
        -ccmThetaContinuousLocalizationError v theta := by
  obtain ⟨phi, psi, hpc, hqc, hp, hq, hd, hsep, hatom, hc, htheta⟩ :=
    exists_separated_thetaArithmetic_phase_pair
  obtain ⟨theta, htc, htp, htq⟩ := htheta Real.pi
  have hcompact : IsCompact (tsupport phi ∪ tsupport psi) := hpc.union hqc
  obtain ⟨A, hA, hbound⟩ := hcompact.isBounded.exists_pos_norm_lt
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
  have hflip := separator_flip_values phi psi theta hd htp htq
  have hcosu : ccmCosLocalizedSource u theta = v := by
    apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
    funext x
    rw [ccmCosLocalizedSource_apply, hu, hv, mul_left_comm, ← Complex.ofReal_mul,
      (hflip x).1]
  have hcosv : ccmCosLocalizedSource v theta = u := by
    apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
    funext x
    rw [ccmCosLocalizedSource_apply, hu, hv, mul_left_comm, ← Complex.ofReal_mul,
      (hflip x).2.1]
  have hsinu (x : ℝ) : ccmSinLocalizedSource u theta x = 0 := by
    rw [ccmSinLocalizedSource_apply, hu, mul_left_comm, ← Complex.ofReal_mul,
      (hflip x).2.2.1, Complex.ofReal_zero, mul_zero]
  have hsinv (x : ℝ) : ccmSinLocalizedSource v theta x = 0 := by
    rw [ccmSinLocalizedSource_apply, hv, mul_left_comm, ← Complex.ofReal_mul,
      (hflip x).2.2.2, Complex.ofReal_zero, mul_zero]
  have hsupp (w : CCMComplexSmoothInteriorSource a)
      (hw : ∀ x, phi x = 0 → psi x = 0 → w x = 0) :
      Function.support w ⊆ Function.support phi ∪ Function.support psi := by
    intro x hx
    by_cases hf : phi x = 0
    · exact Or.inr (fun hg => hx (hw x hf hg))
    · exact Or.inl hf
  have hpu : ccmThetaPrimeLocalizationError u theta = 0 :=
    ccmThetaPrimeLocalizationError_eq_zero_of_separated_components u theta phi psi Real.pi
      (hsupp u (by intros; simp [*]))
      (fun x hx => htp x (subset_tsupport _ hx))
      (fun x hx => htq x (subset_tsupport _ hx)) hsep hatom
  have hpv : ccmThetaPrimeLocalizationError v theta = 0 :=
    ccmThetaPrimeLocalizationError_eq_zero_of_separated_components v theta phi psi Real.pi
      (hsupp v (by intros; simp [*]))
      (fun x hx => htp x (subset_tsupport _ hx))
      (fun x hx => htq x (subset_tsupport _ hx)) hsep hatom
  have hdiff : ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector -
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      4 * thetaGammaPolarGroundCrossPairing phi psi := by
    simp only [ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic, u, v,
      ccmThetaGroundProfile_ofCompactRealProfile]
    exact thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hatom
  have hlocu := ccmRestrictedWeilSourceQuadratic_localization u theta
  have hlocv := ccmRestrictedWeilSourceQuadratic_localization v theta
  rw [hcosu, ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hsinu, hpu] at hlocu
  rw [hcosv, ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hsinv, hpv] at hlocv
  refine ⟨a, u, v, theta, htc, ?_, ?_, hcosu, hcosv, hsinu, hsinv, hpu, hpv,
    by linarith, by linarith, by linarith⟩
  · intro x
    have habs : phi x + psi x = |phi x - psi x| := by
      by_cases hphi : phi x = 0
      · simp [hphi, abs_of_nonneg (hq x)]
      · have hpsi : psi x = 0 := by
          by_contra hpsi
          exact Set.disjoint_left.mp hd (subset_tsupport _ hphi) (subset_tsupport _ hpsi)
        simp [hpsi, abs_of_nonneg (hp x)]
    rw [hu, hv, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x),
      Complex.ofReal_mul, ← habs]
  · intro x hx
    rcases hsupp u (by intros; simp [*]) hx with hphi | hpsi
    · exact Or.inl (htp x (subset_tsupport _ hphi))
    · exact Or.inr (htq x (subset_tsupport _ hpsi))

end RHTower
