import GaloisForLFunctions.RHTower.XiExternalInternalReflectionSeparation
import GaloisForLFunctions.RHTower.PrimeValuationReflectedHellingerCriticalProfile
import GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort
import GaloisForLFunctions.HTGeometry.MutuallySingularTotalVariation

/-!
# Xi reflection-sector geometry

This module tests a source-sector interpretation of RH against two obvious falsifiers.

First, scalar mass cannot be the relevant coordinate. Every prime-Poisson state has total mass
one, but an off-wall reflected pair is mutually singular and therefore maximally separated in
total variation. No predicate of total mass can classify the critical wall.

Second, RH cannot mean that all critical zeros belong to one product sector: distinct critical
heights are still mutually singular. The neutral statement is only fibrewise reflection sewing
at fixed height. At the shrinking displacement `c / log N`, exact neutrality remains rigid:
the limiting reflected Hellinger affinity is one exactly at `c = 0`, while every nonzero `c`
leaves a strict nonzero angle.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry
open Filter Topology

namespace RHTower

noncomputable section

/-- Reflected prime-Poisson states have equal probability mass off wall but maximal
total-variation separation. -/
theorem primePoisson_reflection_equalMass_maximalTotalVariation
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2) :
    (primePoissonMeasure sigma t hsigma) Set.univ =
        (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) Set.univ ∧
      ((primePoissonMeasure sigma t hsigma).toSignedMeasure -
          (primePoissonMeasure (1 - sigma) t
            (sub_pos.mpr hsigma1)).toSignedMeasure).totalVariation Set.univ = 2 := by
  refine ⟨by simp, ?_⟩
  exact HTGeometry.totalVariation_univ_eq_of_isProbability _ _
    (primePoissonMeasure_reflection_mutuallySingular_of_ne_half
      sigma t hsigma hsigma1 hwall)

/-- Equal probability mass does not identify the longitudinal coordinate: distinct critical
heights are maximally separated in total variation. -/
theorem primePoisson_criticalHeights_equalMass_maximalTotalVariation
    {t u : ℝ} (htu : t ≠ u) :
    (primePoissonMeasure (1 / 2) t (by norm_num)) Set.univ =
        (primePoissonMeasure (1 / 2) u (by norm_num)) Set.univ ∧
      ((primePoissonMeasure (1 / 2) t (by norm_num)).toSignedMeasure -
          (primePoissonMeasure (1 / 2) u
            (by norm_num)).toSignedMeasure).totalVariation Set.univ = 2 := by
  refine ⟨by simp, ?_⟩
  exact HTGeometry.totalVariation_univ_eq_of_isProbability _ _
    (primePoissonMeasure_half_mutuallySingular_of_ne htu)

/-- A hypothetical off-line Xi divisor has probability-normalized reflected source laws, yet
those laws have maximal total-variation separation and admit no source-linear sewing. -/
theorem xiOffLine_reflectionMassBlind_sectorFracture
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    let hstrip := xi_divisor_support_re_mem_open_unit rho
    let mu := primePoissonMeasure (rho : ℂ).re (rho : ℂ).im hstrip.1
    let nu := primePoissonMeasure (1 - (rho : ℂ).re) (rho : ℂ).im
      (sub_pos.mpr hstrip.2)
    mu Set.univ = nu Set.univ ∧
      (mu.toSignedMeasure - nu.toSignedMeasure).totalVariation Set.univ = 2 ∧
      XiPrimePoissonReflectionDisjoint rho ∧
      ¬ XiPrimePoissonReflectionSewing rho := by
  dsimp only
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  have hmass := primePoisson_reflection_equalMass_maximalTotalVariation
    (rho : ℂ).re (rho : ℂ).im hstrip.1 hstrip.2 hoff
  have hnosew : ¬ XiPrimePoissonReflectionSewing rho := by
    rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
      xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]
    exact hoff
  exact ⟨hmass.1, hmass.2,
    xiPrimePoissonReflectionDisjoint_of_offLine rho hoff, hnosew⟩

/-- No scalar predicate of total probability mass can classify the critical wall. -/
theorem no_primePoisson_totalMass_wallClassifier (t : ℝ) :
    ¬ ∃ P : ENNReal → Prop,
      ∀ (sigma : ℝ) (hsigma : 0 < sigma) (_hsigma1 : sigma < 1),
        P ((primePoissonMeasure sigma t hsigma) Set.univ) ↔ sigma = 1 / 2 := by
  rintro ⟨P, hP⟩
  have hcenter : P 1 := by
    have h := (hP (1 / 2) (by norm_num) (by norm_num)).2 rfl
    simpa using h
  have hoff := (hP (1 / 3) (by norm_num) (by norm_num)).1 (by simpa using hcenter)
  norm_num at hoff

/-- Unit limiting reflected affinity occurs exactly at zero scaled transverse charge. -/
theorem reflectedPrimeValuationCriticalAffinity_eq_one_iff (c : ℝ) :
    Real.exp (-primeClockUniversalProfile c) = 1 ↔ c = 0 := by
  rw [Real.exp_eq_one_iff, neg_eq_zero]
  exact GaloisForLFunctions.IrregularStokes.primeClockUniversalProfile_eq_zero_iff c

/-- Every nonzero scaled transverse charge leaves a strict but nonzero limiting Hellinger
affinity in the `1 / log N` critical window. -/
theorem reflectedPrimeValuationCriticalAffinity_mem_Ioo_of_ne_zero
    {c : ℝ} (hc : c ≠ 0) :
    Real.exp (-primeClockUniversalProfile c) ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, (Real.exp_lt_one_iff).2 ?_⟩
  have hpos :=
    (GaloisForLFunctions.IrregularStokes.primeClockUniversalProfile_pos_iff c).2 hc
  linarith

/-- At the `1 / log N` reflection scale, exact neutrality is still rigid: zero scaled charge
has unit limiting affinity, while every nonzero scaled charge leaves a strict, nonzero angle. -/
theorem reflectedPrimeValuationCriticalWindow_exactNeutrality (c : ℝ) :
    Tendsto (fun N : ℕ => reflectedPrimeValuationSquaredHellingerLE N c)
        atTop (𝓝 (Real.exp (-primeClockUniversalProfile c))) ∧
      (Real.exp (-primeClockUniversalProfile c) = 1 ↔ c = 0) ∧
      (c ≠ 0 →
        Real.exp (-primeClockUniversalProfile c) ∈ Set.Ioo (0 : ℝ) 1) := by
  exact ⟨tendsto_reflectedPrimeValuationSquaredHellingerLE_critical_profile c,
    reflectedPrimeValuationCriticalAffinity_eq_one_iff c,
    reflectedPrimeValuationCriticalAffinity_mem_Ioo_of_ne_zero⟩

end

end RHTower
