import GaloisForLFunctions.HTGeometry.GomesConstantPolynomialPotential

/-!
# Exact information loss from Hamiltonians to normalized polynomial densities

The reconstruction experiment distinguishes three observations: a first-order connection,
its Hamiltonian, and its normalized density. Opposite affine slopes explain the first
loss; the zero normalization of every infinite-mass profile explains the second.
All statements concern the actual corpus operators and measures on the same real base.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Every affine profile has infinite mass, including the zero-slope case. -/
theorem gomesDilatonMeasure_affine_mass (a b : ℝ) :
    gomesDilatonMeasure (C a * X + C b) Set.univ = ∞ := by
  have hn : ¬ IsFiniteMeasure (gomesDilatonMeasure (C a * X + C b)) := by
    intro h
    apply gomesFinitePolynomialProfiles_zero_not_mem
    apply (gomesPolynomialAffineTilt_finite_iff 0 a b).mp
    simpa only [gomesPolynomialAffineTilt, zero_add] using h
  by_contra ht
  apply hn
  rw [isFiniteMeasure_iff, lt_top_iff_ne_top]
  exact ht

/-- All affine profiles collapse to the same zero normalized measure. -/
theorem gomesDilatonMassNormalized_affine (a b : ℝ) :
    gomesDilatonMassNormalized (C a * X + C b) = 0 :=
  (gomesDilatonMassNormalized_zero_iff _).mpr (gomesDilatonMeasure_affine_mass a b)

/-- The affine exception never carries a nonzero Schwartz ground state. -/
theorem gomesDilatonHamiltonian_affine_kernel (a b : ℝ) :
    LinearMap.ker (dilatonHamiltonianCLM (C a * X + C b)).toLinearMap = ⊥ := by
  apply (gomesPolynomialHamiltonian_ker_bot_iff _).mpr
  intro h
  have hm := (isFiniteMeasure_iff _).mp h
  rw [gomesDilatonMeasure_affine_mass] at hm
  exact lt_irrefl _ hm

/-- Normalization retains Hamiltonian information exactly until the infinite-mass collapse. -/
theorem gomesDilatonMassNormalized_hamiltonian_iff (H K : ℝ[X]) :
    gomesDilatonMassNormalized H = gomesDilatonMassNormalized K ↔
      dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∨
        (gomesDilatonMeasure H Set.univ = ∞ ∧ gomesDilatonMeasure K Set.univ = ∞) := by
  constructor
  · intro h
    rcases (gomesDilatonMassNormalized_eq_iff H K).mp h with hc | hi
    · exact Or.inl ((gomesDilatonHamiltonian_profile_fibers H K).mpr (Or.inl hc))
    · exact Or.inr hi
  · rintro (hh | hi)
    · rcases (gomesDilatonHamiltonian_profile_fibers H K).mp hh with hc | ⟨a, b, c, rfl, rfl⟩
      · exact (gomesDilatonMassNormalized_eq_iff H K).mpr (Or.inl hc)
      · rw [gomesDilatonMassNormalized_affine, gomesDilatonMassNormalized_affine]
    · exact (gomesDilatonMassNormalized_eq_iff H K).mpr (Or.inr hi)

/-- The complete failure of connection recovery is a pair of nonzero opposite affine slopes. -/
theorem gomesDilatonHamiltonian_connection_failure_iff (H K : ℝ[X]) :
    (dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∧
      dilatonSuperchargeCLM H ≠ dilatonSuperchargeCLM K) ↔
        ∃ a b c : ℝ, a ≠ 0 ∧ H = C a * X + C b ∧ K = C (-a) * X + C c := by
  constructor
  · rintro ⟨hh, hn⟩
    rcases (gomesDilatonHamiltonian_profile_fibers H K).mp hh with hc | ⟨a, b, c, hb, hc⟩
    · exact False.elim (hn ((gomesDilatonConnection_constant_iff H K).mpr hc))
    · refine ⟨a, b, c, ?_, hb, hc⟩
      intro hz
      apply hn
      rw [hb, hc, gomesDilatonConnection_affine_eq_iff, hz, neg_zero]
  · rintro ⟨a, b, c, ha, rfl, rfl⟩
    constructor
    · apply (gomesDilatonHamiltonian_affine_eq_iff a b (-a) c).mpr
      ring
    · intro h
      have he := (gomesDilatonConnection_affine_eq_iff a b (-a) c).mp h
      apply ha
      linarith

/-- Every finite polynomial profile has nonzero curvature, so no affine exception is possible. -/
theorem gomesFinitePolynomialProfile_curvature_ne_zero (P : GomesFinitePolynomialProfile) :
    P.val.derivative.derivative ≠ 0 := by
  intro hz
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, P.val = C a * X + C b := by
    simpa using (gomesDilaton_secondDerivative_constant_iff P.val 0).mp (by simpa using hz)
  have hm := (isFiniteMeasure_iff _).mp P.property
  rw [hab, gomesDilatonMeasure_affine_mass] at hm
  exact lt_irrefl _ hm

/-- A finite profile is reconstructed up to amplitude even against arbitrary competing profiles. -/
theorem gomesFinitePolynomialHamiltonian_arbitrary_fiber
    (P : GomesFinitePolynomialProfile) (K : ℝ[X]) :
    dilatonHamiltonianCLM P.val = dilatonHamiltonianCLM K ↔
      ∃ c : ℝ, P.val = K + C c :=
  gomesDilatonHamiltonian_curved_fibers
    ⟨P.val, gomesFinitePolynomialProfile_curvature_ne_zero P⟩ K

end GaloisForLFunctions.HTGeometry
