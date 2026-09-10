import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialEnergyBoundary

/-!
# The entire centered-potential fiber of a finite polynomial profile

Discarding the scalar energy reference retains one finite connection class. Exactly
for a quadratic profile it adds one opposite connection class, whose density has
infinite mass and whose Schwartz ground kernel is zero. This makes the reconstruction
loss and its positive finite-sector survivor explicit in the scalar Gomes experiment.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Every constant-amplitude shift of the opposite of a finite profile has infinite mass. -/
theorem gomesFinitePolynomialOppositeShift_infinite (P : GomesFinitePolynomialProfile) (c : ℝ) :
    gomesDilatonMeasure (-P.val + C c) Set.univ = ∞ := by
  by_contra ht
  have hf : IsFiniteMeasure (gomesDilatonMeasure (-P.val + C c)) := by
    rw [isFiniteMeasure_iff, lt_top_iff_ne_top]
    exact ht
  have hn : IsFiniteMeasure (gomesDilatonMeasure (-P.val)) := by
    apply (gomesPolynomialAffineTilt_finite_iff (-P.val) 0 c).mp
    simpa only [gomesPolynomialAffineTilt, map_zero, zero_mul, zero_add] using hf
  exact gomesFinitePolynomialProfiles_no_dual P.val ⟨P.property, hn⟩

/-- A finite profile and its opposite can never induce the same first-order connection. -/
theorem gomesFinitePolynomialConnection_dual_ne (P : GomesFinitePolynomialProfile) :
    dilatonSuperchargeCLM P.val ≠ dilatonSuperchargeCLM (-P.val) := by
  intro h
  have hh := ((gomesDilatonHamiltonian_origin_slope_iff P.val (-P.val)).mpr h).1
  obtain ⟨a, b, hab⟩ := (gomesDilatonHamiltonian_dual_eq_iff P.val).mp hh
  apply gomesFinitePolynomialProfile_curvature_ne_zero P
  rw [hab]
  simp

/-- The full centered-potential fiber consists of its original class and, only for quadratics, its dual. -/
theorem gomesFinitePolynomialCenteredPotential_arbitrary_iff (P : GomesFinitePolynomialProfile) (K : ℝ[X]) :
    gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential K ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM K ∨
        (P.val.derivative.derivative.derivative = 0 ∧
          dilatonSuperchargeCLM (-P.val) = dilatonSuperchargeCLM K) := by
  rw [gomesDilatonCenteredPotential_eq_iff]
  constructor
  · rintro ⟨k, h⟩
    rcases (gomesFinitePolynomialEnergyShift_arbitrary_iff P K k).mp h with ⟨hc, _⟩ | ⟨_, hd, c, hc⟩
    · exact Or.inl hc
    · refine Or.inr ⟨by rw [hd, derivative_C], ?_⟩
      rw [hc, gomesDilatonConnection_constant]
  · rintro (hc | ⟨ht, hc⟩)
    · exact ⟨0, (gomesFinitePolynomialEnergyShift_arbitrary_iff P K 0).mpr (Or.inl ⟨hc, rfl⟩)⟩
    · obtain ⟨k, hk, hd⟩ := (gomesFinitePolynomialProfile_third_derivative_zero_iff P).mp ht
      obtain ⟨c, he⟩ := (gomesDilatonConnection_constant_iff K (-P.val)).mp hc.symm
      exact ⟨k, (gomesFinitePolynomialEnergyShift_arbitrary_iff P K k).mpr (Or.inr ⟨hk, hd, c, he⟩)⟩

/-- Connection recovery fails exactly in the distinct opposite class of a finite quadratic. -/
theorem gomesFinitePolynomialCenteredPotential_failure_iff (P : GomesFinitePolynomialProfile) (K : ℝ[X]) :
    (gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential K ∧
      dilatonSuperchargeCLM P.val ≠ dilatonSuperchargeCLM K) ↔
        P.val.derivative.derivative.derivative = 0 ∧
          dilatonSuperchargeCLM (-P.val) = dilatonSuperchargeCLM K := by
  constructor
  · rintro ⟨h, hn⟩
    exact ((gomesFinitePolynomialCenteredPotential_arbitrary_iff P K).mp h).resolve_left hn
  · intro h
    refine ⟨(gomesFinitePolynomialCenteredPotential_arbitrary_iff P K).mpr (Or.inr h), ?_⟩
    intro he
    exact gomesFinitePolynomialConnection_dual_ne P (he.trans h.2.symm)

/-- Every exceptional centered-potential competitor has zero normalized density. -/
theorem gomesFinitePolynomialCenteredPotential_zero_normalized_iff
    (P : GomesFinitePolynomialProfile) (K : ℝ[X]) :
    (gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential K ∧
      gomesDilatonMassNormalized K = 0) ↔
        P.val.derivative.derivative.derivative = 0 ∧
          dilatonSuperchargeCLM (-P.val) = dilatonSuperchargeCLM K := by
  constructor
  · rintro ⟨h, hz⟩
    apply (gomesFinitePolynomialCenteredPotential_failure_iff P K).mp
    refine ⟨h, ?_⟩
    intro hc
    obtain ⟨c, he⟩ := (gomesDilatonConnection_constant_iff K P.val).mp hc.symm
    have hm := (gomesDilatonMassNormalized_zero_iff K).mp hz
    have hf : IsFiniteMeasure (gomesDilatonMeasure K) := by
      rw [he]
      have hh := (gomesPolynomialAffineTilt_finite_iff P.val 0 c).mpr P.property
      simpa only [gomesPolynomialAffineTilt, map_zero, zero_mul, zero_add] using hh
    have ht := (isFiniteMeasure_iff _).mp hf
    rw [hm] at ht
    exact lt_irrefl _ ht
  · intro h
    obtain ⟨c, hc⟩ := (gomesDilatonConnection_constant_iff K (-P.val)).mp h.2.symm
    refine ⟨(gomesFinitePolynomialCenteredPotential_arbitrary_iff P K).mpr (Or.inr h), ?_⟩
    apply (gomesDilatonMassNormalized_zero_iff K).mpr
    rw [hc]
    exact gomesFinitePolynomialOppositeShift_infinite P c

/-- An exceptional connection class exists exactly for finite quadratic profiles. -/
theorem gomesFinitePolynomialCenteredPotential_extra_class_iff (P : GomesFinitePolynomialProfile) :
    (∃ K : ℝ[X], gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential K ∧
      dilatonSuperchargeCLM P.val ≠ dilatonSuperchargeCLM K) ↔
        P.val.derivative.derivative.derivative = 0 := by
  constructor
  · rintro ⟨K, h⟩
    exact ((gomesFinitePolynomialCenteredPotential_failure_iff P K).mp h).1
  · intro h
    exact ⟨-P.val, (gomesFinitePolynomialCenteredPotential_failure_iff P (-P.val)).mpr ⟨h, rfl⟩⟩

/-- All exceptional competitors share the same opposite connection, despite arbitrary amplitudes. -/
theorem gomesFinitePolynomialCenteredPotential_exceptional_class_unique
    (P : GomesFinitePolynomialProfile)
    (K L : {K : ℝ[X] // gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential K ∧
      dilatonSuperchargeCLM P.val ≠ dilatonSuperchargeCLM K}) :
    dilatonSuperchargeCLM K.val = dilatonSuperchargeCLM L.val := by
  have hk := ((gomesFinitePolynomialCenteredPotential_failure_iff P K.val).mp K.property).2
  have hl := ((gomesFinitePolynomialCenteredPotential_failure_iff P L.val).mp L.property).2
  exact hk.symm.trans hl

end GaloisForLFunctions.HTGeometry
