import GaloisForLFunctions.RHTower.ThetaPrimeIslandCoercivity
import GaloisForLFunctions.RHTower.CCM.CCMFarGapPhaseCoercivity

/-!
# Arbitrary complex sources and local phases on prime islands

The real support-region gap extends to every complex profile, to literal CCM
source sums, and to smooth phase angles varying inside every component. These
are selected support regions, with no assertion of a dense exhaustion.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators SchwartzMap

namespace RHTower

open ThetaSourceWard

private theorem physicalNorm_toAperture (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture a v‖ = ‖ccmArchimedeanFormEmbedding a v‖ := rfl

theorem thetaRealComponent_finite_sum {ι : Type*} [Fintype ι] (chi : ι → 𝓢(ℝ, ℂ)) :
    thetaRealComponent (∑ i, chi i) = ∑ i, thetaRealComponent (chi i) :=
  map_sum (SchwartzMap.postcompCLM Complex.reCLM) chi Finset.univ

theorem thetaImagComponent_finite_sum {ι : Type*} [Fintype ι] (chi : ι → 𝓢(ℝ, ℂ)) :
    thetaImagComponent (∑ i, chi i) = ∑ i, thetaImagComponent (chi i) :=
  map_sum (SchwartzMap.postcompCLM Complex.imCLM) chi Finset.univ

theorem exists_cofinal_thetaComplex_primeIsland_coercivity :
    ∃ k : ℝ, 0 < k ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r : ℝ), 0 < r ∧
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        ∀ chi : Option (Fin n) → 𝓢(ℝ, ℂ),
          (∀ i, HasCompactSupport (chi i)) →
          (∀ i, tsupport (chi i) ⊆ Metric.ball (i.elim 0 (fun j => Real.log (p j))) r) →
          k * (∑ i, thetaGroundNormSq (chi i)) ≤
            thetaFullArithmeticQuadratic (∑ i, chi i) := by
  obtain ⟨k, hk, hreal⟩ := exists_cofinal_thetaReal_primeIsland_coercivity
  refine ⟨k, hk, fun N n => ?_⟩
  obtain ⟨p, r, hr, hp, hsep, hgap⟩ := hreal N n
  refine ⟨p, r, hr, hp, hsep, fun chi hc hs => ?_⟩
  have hRe := hgap (fun i => thetaRealComponent (chi i))
    (fun i => hasCompactSupport_thetaRealComponent _ (hc i))
    (fun i => (closure_mono (support_thetaRealComponent_subset (chi i))).trans (hs i))
  have hIm := hgap (fun i => thetaImagComponent (chi i))
    (fun i => hasCompactSupport_thetaImagComponent _ (hc i))
    (fun i => (closure_mono (support_thetaImagComponent_subset (chi i))).trans (hs i))
  have hmass := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => thetaGroundNormSq_realImag (chi i))
  rw [Finset.sum_add_distrib] at hmass
  rw [hmass, mul_add, thetaFullArithmeticQuadratic_realImag,
    thetaRealComponent_finite_sum, thetaImagComponent_finite_sum]
  exact add_le_add hRe hIm

theorem exists_cofinal_ccm_primeIsland_coercivity :
    ∃ k : ℝ, 0 < k ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r : ℝ), 0 < r ∧
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        ∀ (a : SuzukiPositiveAperture) (u : Option (Fin n) → CCMComplexSmoothInteriorSource a),
          (∀ i, tsupport (u i) ⊆ Metric.ball (i.elim 0 (fun j => Real.log (p j))) r) →
          k * (∑ i, ‖ccmArchimedeanFormEmbedding a (u i).toCCMFormVector‖ ^ 2) ≤
            ccmRestrictedWeilSourceQuadratic a (ccmSmoothFiniteSum u (fun _ => 1)).toCCMFormVector := by
  obtain ⟨k, hk, hcomplex⟩ := exists_cofinal_thetaComplex_primeIsland_coercivity
  refine ⟨k, hk, fun N n => ?_⟩
  obtain ⟨p, r, hr, hp, hsep, hgap⟩ := hcomplex N n
  refine ⟨p, r, hr, hp, hsep, fun a u hs => ?_⟩
  have h := hgap (fun i => ccmThetaGroundProfile (u i))
    (fun i => hasCompactSupport_ccmThetaGroundProfile (u i)) (fun i => by
      change closure (Function.support (ccmThetaGroundProfile (u i))) ⊆ _
      rw [support_ccmThetaGroundProfile]
      exact hs i)
  simp_rw [thetaGroundNormSq_ccmProfile_eq_physical, physicalNorm_toAperture] at h
  rw [ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic,
    ccmThetaGroundProfile_finiteSum]
  simpa only [one_smul] using h

theorem ccmCosLocalizedSource_finiteSum {ι : Type*} [Fintype ι] {a : SuzukiPositiveAperture}
    (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) (theta : 𝓢(ℝ, ℝ)) :
    ccmCosLocalizedSource (ccmSmoothFiniteSum u z) theta =
      ccmSmoothFiniteSum (fun i => ccmCosLocalizedSource (u i) theta) z := by
  apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
  funext x
  simp only [ccmCosLocalizedSource_apply, ccmSmoothFiniteSum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ccmSinLocalizedSource_finiteSum {ι : Type*} [Fintype ι] {a : SuzukiPositiveAperture}
    (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) (theta : 𝓢(ℝ, ℝ)) :
    ccmSinLocalizedSource (ccmSmoothFiniteSum u z) theta =
      ccmSmoothFiniteSum (fun i => ccmSinLocalizedSource (u i) theta) z := by
  apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
  funext x
  simp only [ccmSinLocalizedSource_apply, ccmSmoothFiniteSum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_cofinal_ccm_primeIsland_phaseEnergy_gap :
    ∃ k : ℝ, 0 < k ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r : ℝ), 0 < r ∧
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        ∀ (a : SuzukiPositiveAperture) (u : Option (Fin n) → CCMComplexSmoothInteriorSource a),
          (∀ i, tsupport (u i) ⊆ Metric.ball (i.elim 0 (fun j => Real.log (p j))) r) →
          ∀ (theta : 𝓢(ℝ, ℝ)) (t : ℝ),
          k * (∑ i, ‖ccmArchimedeanFormEmbedding a (u i).toCCMFormVector‖ ^ 2) ≤
            ccmPhaseLocalizationEnergy (ccmSmoothFiniteSum u (fun _ => 1)) theta t := by
  obtain ⟨k, hk, hcoercive⟩ := exists_cofinal_ccm_primeIsland_coercivity
  refine ⟨k, hk, fun N n => ?_⟩
  obtain ⟨p, r, hr, hp, hsep, hgap⟩ := hcoercive N n
  refine ⟨p, r, hr, hp, hsep, fun a u hu theta t => ?_⟩
  let angle := ccmScaledPhaseAngle theta t
  have hc := hgap a (fun i => ccmCosLocalizedSource (u i) angle)
    (fun i => (closure_mono (support_ccmCosLocalizedSource_subset (u i) angle)).trans (hu i))
  have hs := hgap a (fun i => ccmSinLocalizedSource (u i) angle)
    (fun i => (closure_mono (support_ccmSinLocalizedSource_subset (u i) angle)).trans (hu i))
  rw [ccmPhaseLocalizationEnergy, ccmCosLocalizedSource_finiteSum,
    ccmSinLocalizedSource_finiteSum]
  have hmass := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => ccmPhysicalMass_localization (u i) angle)
  simp_rw [physicalNorm_toAperture] at hmass
  rw [Finset.sum_add_distrib] at hmass
  have h := add_le_add hc hs
  rw [← mul_add, hmass] at h
  exact h

end RHTower
