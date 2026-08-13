import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff
import GaloisForLFunctions.RHTower.RouteROperatorTopologyCompactnessDichotomy
import GaloisForLFunctions.RHTower.RouteRRationalCartierPrimeDilationLanding

/-!
# Route R Xi-jet principal Calkin non-erasure

The first nonzero multiplicity-exact Xi jet forces a unique Calkin principal
coefficient for the fixed `(2,3)` Stokes--Sonin receiver.  Every other
jet-matched coefficient differs from it by a compact operator, and the
forced coefficient is compact exactly on the critical fibre.

Thus singular Xi division supplies a canonical nonzero class off line, not
an annihilator.  Lower Laurent coefficients and compact counterterms cannot
alter this leading obstruction.
-/

open Complex

namespace RHTower

noncomputable section

/-- First nonzero multiplicity-exact Xi jet used to normalize the singular
operator coefficient. -/
def routeRXiFirstNonzeroJet (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho

theorem routeRXiFirstNonzeroJet_ne_zero (rho : XiDivisorSupport) :
    routeRXiFirstNonzeroJet rho ≠ 0 :=
  ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho

/-- Forced leading coefficient of a singular Xi multiplier whose first
nonzero jet recovers the fixed physical receiver. -/
def routeRTwoThreeXiJetPrincipalCalkinCoefficient
    (A : ℝ) (rho : XiDivisorSupport) : RouteRPhysicalOperator :=
  (routeRXiFirstNonzeroJet rho)⁻¹ •
    routeRTwoThreeStokesSoninCommutator A
      (primeDepthBVWoldXiCenteredRate rho)

/-- Multiplication by the first nonzero Xi jet recovers the receiver exactly. -/
theorem routeRXiFirstNonzeroJet_smul_principalCalkinCoefficient
    (A : ℝ) (rho : XiDivisorSupport) :
    routeRXiFirstNonzeroJet rho •
        routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho =
      routeRTwoThreeStokesSoninCommutator A
        (primeDepthBVWoldXiCenteredRate rho) := by
  rw [routeRTwoThreeXiJetPrincipalCalkinCoefficient, smul_smul,
    mul_inv_cancel₀ (routeRXiFirstNonzeroJet_ne_zero rho), one_smul]

/-- Exact scaling law for the forced principal Calkin norm. -/
theorem essentialNorm_routeRTwoThreeXiJetPrincipalCalkinCoefficient
    (A : ℝ) (rho : XiDivisorSupport) :
    essentialNorm (routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho) =
      ‖routeRXiFirstNonzeroJet rho‖⁻¹ *
        essentialNorm
          (routeRTwoThreeStokesSoninCommutator A
            (primeDepthBVWoldXiCenteredRate rho)) := by
  rw [routeRTwoThreeXiJetPrincipalCalkinCoefficient, essentialNorm_smul,
    norm_inv]

/-- The forced singular principal coefficient is compact exactly on the
critical fibre. -/
theorem routeRTwoThreeXiJetPrincipalCalkinCoefficient_isCompactOperator_iff
    {A : ℝ} (hA : 0 < A) (rho : XiDivisorSupport) :
    IsCompactOperator (routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hprincipal
    have hreceiver := hprincipal.smul (routeRXiFirstNonzeroJet rho)
    have hreceiver' : IsCompactOperator
        (routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho)) := by
      change IsCompactOperator
        ⇑(routeRXiFirstNonzeroJet rho •
          routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho) at hreceiver
      rw [routeRXiFirstNonzeroJet_smul_principalCalkinCoefficient] at hreceiver
      exact hreceiver
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp
      ((routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff
        hA _).mp hreceiver')
  · intro hline
    have hreceiver : IsCompactOperator
        (routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho)) :=
      (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA _).mpr
        ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr hline)
    exact hreceiver.smul (routeRXiFirstNonzeroJet rho)⁻¹

/-- **Principal Calkin uniqueness.**  Any operator coefficient matching the
same first Xi jet modulo compacts differs from the forced coefficient by a
compact operator. -/
theorem routeRTwoThreeXiJetPrincipalCalkinCoefficient_unique_mod_compact
    (A : ℝ) (rho : XiDivisorSupport) (S : RouteRPhysicalOperator)
    (hmatch : IsCompactOperator
      (routeRXiFirstNonzeroJet rho • S -
        routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho))) :
    IsCompactOperator
      (S - routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho) := by
  have hscaled : IsCompactOperator
      (routeRXiFirstNonzeroJet rho •
        (S - routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho)) := by
    rw [smul_sub,
      routeRXiFirstNonzeroJet_smul_principalCalkinCoefficient]
    exact hmatch
  exact (IsCompactOperator.smul_iff₀
    (routeRXiFirstNonzeroJet_ne_zero rho)).mp hscaled

/-- A compact jet-matched leading coefficient forces critical-line
placement; no compact singular source lift can retain an off-line receiver. -/
theorem re_eq_half_of_compact_jetMatched_principalCoefficient
    {A : ℝ} (hA : 0 < A) (rho : XiDivisorSupport)
    (S : RouteRPhysicalOperator) (hS : IsCompactOperator S)
    (hmatch : IsCompactOperator
      (routeRXiFirstNonzeroJet rho • S -
        routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho))) :
    (rho : ℂ).re = 1 / 2 := by
  have hdiff :=
    routeRTwoThreeXiJetPrincipalCalkinCoefficient_unique_mod_compact
      A rho S hmatch
  have hprincipal : IsCompactOperator
      (routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho) := by
    have hsum := hS.sub hdiff
    change IsCompactOperator (fun x => S x -
      (S x - routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho x)) at hsum
    simpa only [sub_sub_cancel] using hsum
  exact
    (routeRTwoThreeXiJetPrincipalCalkinCoefficient_isCompactOperator_iff
      hA rho).mp hprincipal

/-- Existence on every Xi fibre of some compact leading coefficient which
matches the first nonzero Xi jet modulo the compact ideal.  The coefficient
may vary arbitrarily with the divisor; no regularity or canonical-choice
hypothesis is imposed. -/
def RouteRCompactXiJetPrincipalLanding (A : ℝ) : Prop :=
  ∀ rho : XiDivisorSupport,
    ∃ S : RouteRPhysicalOperator,
      IsCompactOperator S ∧
      IsCompactOperator
        (routeRXiFirstNonzeroJet rho • S -
          routeRTwoThreeStokesSoninCommutator A
            (primeDepthBVWoldXiCenteredRate rho))

/-- **Choice-free singular landing classification.**  Even allowing an
arbitrary divisor-dependent compact principal coefficient, matching the
physical receiver modulo compacts on every Xi fibre is exactly RH. -/
theorem routeRCompactXiJetPrincipalLanding_iff_rh
    {A : ℝ} (hA : 0 < A) :
    RouteRCompactXiJetPrincipalLanding A ↔ RiemannHypothesis := by
  constructor
  · intro hlanding
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    obtain ⟨S, hS, hmatch⟩ := hlanding rho
    exact re_eq_half_of_compact_jetMatched_principalCoefficient
      hA rho S hS hmatch
  · intro hRH rho
    have hprincipal : IsCompactOperator
        (routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho) :=
      (routeRTwoThreeXiJetPrincipalCalkinCoefficient_isCompactOperator_iff
        hA rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)
    refine
      ⟨routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho,
        hprincipal, ?_⟩
    rw [routeRXiFirstNonzeroJet_smul_principalCalkinCoefficient, sub_self]
    exact isCompactOperator_zero

/-! ## Exact regular Xi/Calkin operator algebra -/

/-- Operator class generated by one regular bounded Xi multiplier and the
compact ideal.  Finite sums of such terms reduce to this normal form. -/
def routeRRegularXiCalkinClass (z : ℂ) : Set RouteRPhysicalOperator :=
  {T | ∃ S K : RouteRPhysicalOperator,
    IsCompactOperator K ∧ T = XiC z • S + K}

/-- Complete fibre classification: away from the Xi divisor the regular
class is the whole operator algebra; at the divisor it is exactly the compact
ideal. -/
theorem mem_routeRRegularXiCalkinClass_iff
    (z : ℂ) (T : RouteRPhysicalOperator) :
    T ∈ routeRRegularXiCalkinClass z ↔
      XiC z ≠ 0 ∨ IsCompactOperator T := by
  constructor
  · rintro ⟨S, K, hK, rfl⟩
    by_cases hz : XiC z = 0
    · right
      simpa [hz] using hK
    · exact Or.inl hz
  · rintro (hz | hT)
    · refine ⟨(XiC z)⁻¹ • T, 0, isCompactOperator_zero, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hz, one_smul, add_zero]
    · exact ⟨0, T, hT, by simp⟩

theorem routeRRegularXiCalkinClass_eq_univ_of_ne_zero
    {z : ℂ} (hz : XiC z ≠ 0) :
    routeRRegularXiCalkinClass z = Set.univ := by
  ext T
  rw [mem_routeRRegularXiCalkinClass_iff]
  simp [hz]

theorem routeRRegularXiCalkinClass_eq_compactOperatorSet_of_eq_zero
    {z : ℂ} (hz : XiC z = 0) :
    routeRRegularXiCalkinClass z = routeRCompactOperatorSet := by
  ext T
  rw [mem_routeRRegularXiCalkinClass_iff]
  simp [hz, routeRCompactOperatorSet]

/-- The regular Xi/Calkin class is already operator-norm closed.  Norm
completion therefore adds no singular divisor coefficient. -/
theorem isClosed_routeRRegularXiCalkinClass (z : ℂ) :
    IsClosed (routeRRegularXiCalkinClass z) := by
  by_cases hz : XiC z = 0
  · rw [routeRRegularXiCalkinClass_eq_compactOperatorSet_of_eq_zero hz,
      routeRCompactOperatorSet]
    exact isClosed_setOf_isCompactOperator
  · rw [routeRRegularXiCalkinClass_eq_univ_of_ne_zero hz]
    exact isClosed_univ

/-- On an actual Xi fibre, membership of the fixed receiver in the complete
regular Xi/Calkin algebra is exactly critical-line placement. -/
theorem routeRTwoThreeStokesReceiver_mem_regularXiCalkinClass_iff
    {A : ℝ} (hA : 0 < A) (rho : XiDivisorSupport) :
    routeRTwoThreeStokesSoninCommutator A
        (primeDepthBVWoldXiCenteredRate rho) ∈
        routeRRegularXiCalkinClass (xiSpectralPointSupport rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [mem_routeRRegularXiCalkinClass_iff,
    XiC_xiSpectralPointSupport_eq_zero]
  simp only [ne_eq, not_true, false_or]
  rw [routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global regular Xi/Calkin membership of the fixed receiver is RH. -/
theorem routeRTwoThreeStokesReceiver_global_mem_regularXiCalkinClass_iff_rh
    {A : ℝ} (hA : 0 < A) :
    (∀ rho : XiDivisorSupport,
      routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho) ∈
        routeRRegularXiCalkinClass (xiSpectralPointSupport rho)) ↔
      RiemannHypothesis := by
  constructor
  · intro hmem
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact
      (routeRTwoThreeStokesReceiver_mem_regularXiCalkinClass_iff
        hA rho).mp (hmem rho)
  · intro hRH rho
    exact
      (routeRTwoThreeStokesReceiver_mem_regularXiCalkinClass_iff
        hA rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- Global removability of the forced principal Calkin coefficient is
exactly RH.  This is a classification theorem, not a construction of the
required source removability law. -/
theorem routeRTwoThreeXiJetPrincipalCalkinCoefficient_globalCompact_iff_rh
    {A : ℝ} (hA : 0 < A) :
    (∀ rho : XiDivisorSupport,
      IsCompactOperator
        (routeRTwoThreeXiJetPrincipalCalkinCoefficient A rho)) ↔
      RiemannHypothesis := by
  constructor
  · intro hcompact
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact
      (routeRTwoThreeXiJetPrincipalCalkinCoefficient_isCompactOperator_iff
        hA rho).mp (hcompact rho)
  · intro hRH rho
    exact
      (routeRTwoThreeXiJetPrincipalCalkinCoefficient_isCompactOperator_iff
        hA rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
