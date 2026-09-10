import GaloisForLFunctions.HTGeometry.GomesTruncatedJetResonance
import GaloisForLFunctions.HTGeometry.GomesFiniteFockTaylorArc

/-!
# The full joint symmetry algebra has unique resonant finite symbols

This classifies arbitrary matrices, not a preselected family of symmetries.
The only surviving coefficient positions are multiples of the actual phase order.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The algebra of all matrices preserving both actual finite clock structures. -/
def gomesTruncatedJetJointAlgebra (n : ℕ) (z : ℂ) :
    Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
  Subalgebra.centralizer ℂ {fockShiftMatrix (n + 1), RHTower.truncatedJetClock n z}

/-- Membership is precisely simultaneous commutation with the two supplied structures. -/
theorem gomesTruncatedJetJointAlgebra_mem_iff (n : ℕ) (z : ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    M ∈ gomesTruncatedJetJointAlgebra n z ↔
      Commute M (fockShiftMatrix (n + 1)) ∧ Commute M (RHTower.truncatedJetClock n z) := by
  rw [gomesTruncatedJetJointAlgebra, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h _ (by simp)).symm, (h _ (by simp)).symm⟩
  · rintro ⟨hd, hz⟩ a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hd.symm.eq
    · rcases Set.mem_singleton_iff.mp ha with rfl
      exact hz.symm.eq

/-- The full joint commutation problem has exactly one resonant finite coefficient vector. -/
theorem gomesTruncatedJetJointAlgebra_unique_symbol (n : ℕ) (z : ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    M ∈ gomesTruncatedJetJointAlgebra n z ↔
      ∃! c : Fin (n + 1) → ℂ,
        gomesFiniteFockPolynomialHom (n + 1) (gomesFiniteFockCoefficientPolynomial (n + 1) c) = M ∧
          ∀ k : Fin (n + 1), c k = 0 ∨ orderOf z ∣ k.val := by
  rw [gomesTruncatedJetJointAlgebra_mem_iff]
  constructor
  · rintro ⟨hd, hz⟩
    obtain ⟨c, hc, hu⟩ := (gomesFiniteFock_commute_iff_unique_symbol (n + 1) M).mp hd
    refine ⟨c, ⟨hc, ?_⟩, fun d hd => hu d hd.1⟩
    rw [← hc] at hz
    simpa only [gomesFiniteFockCoefficientPolynomial_coeff] using
      (gomesTruncatedJetClock_polynomial_commute_iff n z _).mp hz
  · rintro ⟨c, ⟨hc, hr⟩, _⟩
    constructor
    · exact (gomesFiniteFock_commute_iff_polynomial (n + 1) M).mpr ⟨_, hc⟩
    · rw [← hc]
      apply (gomesTruncatedJetClock_polynomial_commute_iff n z _).mpr
      simpa only [gomesFiniteFockCoefficientPolynomial_coeff] using hr

/-- The actual phase-order clock power belongs to the full joint symmetry algebra. -/
theorem gomesTruncatedJetJointAlgebra_orderPower_mem (n : ℕ) (z : ℂ) :
    fockShiftMatrix (n + 1) ^ orderOf z ∈ gomesTruncatedJetJointAlgebra n z := by
  rw [gomesTruncatedJetJointAlgebra_mem_iff]
  exact ⟨(Commute.refl _).pow_left _, gomesTruncatedJetClock_orderPower_commute n z⟩

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
