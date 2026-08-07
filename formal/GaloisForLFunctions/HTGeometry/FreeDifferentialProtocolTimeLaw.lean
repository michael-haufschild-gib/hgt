import GaloisForLFunctions.HTGeometry.FiniteShadowCapacitySpectrum
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTimeLaw

/-!
# The projective time law on the free differential rational field

Specializing the nonautonomous phase-tail theory to the free differential rational field on one
generator removes every structural hypothesis: the base field is a field of constants, the
generator is differentially independent and its jets generate everything, all by construction.

What remains is a protocol — a sequence of derivation-preserving algebra endomorphisms — and the
theorem: the phase tails transport exactly, they are either all trivial or all nontrivial, in the
nontrivial phase each carries a hypertranscendental coordinate, successive coordinates are related
by a fractional-linear transformation with constant coefficients whose class in the projective
linear group is unique, and the Schwarzian of the coordinate is a nonconstant observable carried
unchanged through time.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

open JetField

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- The jet coordinates are exactly the free rational coordinates. -/
theorem jet_eq_freeCoordinate (p : Unit × ℕ) :
    (jet p : JetField C Unit) = freeCoordinate C (Unit × ℕ) p := rfl

omit [CharZero C] in
/-- The jets of the free generator are all the jet coordinates. -/
theorem differentialJetSet_jet_zero :
    differentialJetSet ({(jet ((), 0) : JetField C Unit)} : Set (JetField C Unit)) =
      Set.range (fun p : Unit × ℕ => (jet p : JetField C Unit)) := by
  ext z
  constructor
  · rintro ⟨x, hx, n, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨((), n), (differentialJet_jet_of_zero () n).symm⟩
  · rintro ⟨⟨j, n⟩, rfl⟩
    refine ⟨jet ((), 0), rfl, n, ?_⟩
    have : j = () := rfl
    subst this
    exact differentialJet_jet_of_zero () n

/-- **The free generator generates the free differential rational field.** -/
theorem differentialAdjoin_jet_zero_eq_top :
    differentialAdjoin C ({(jet ((), 0) : JetField C Unit)} : Set (JetField C Unit)) = ⊤ := by
  rw [differentialAdjoin, differentialJetSet_jet_zero]
  have hrange : Set.range (fun p : Unit × ℕ => (jet p : JetField C Unit))
      = freeCoordinate C (Unit × ℕ) '' Set.univ := by
    ext z
    simp only [Set.image_univ, jet_eq_freeCoordinate]
    exact Iff.rfl
  rw [hrange]
  exact freeCoordinateField_univ (C := C) (σ := Unit × ℕ)

omit [CharZero C] in
/-- The base field acts by constants on the free differential rational field. -/
theorem deriv_algebraMap_jetField (a : C) :
    ((algebraMap C (JetField C Unit)) a)′ = 0 :=
  JetField.deriv_algebraMap a

omit [CharZero C] in
/-- The free generator is differentially independent over the base. -/
theorem differentialIndependent_jet_zero :
    DifferentialIndependent C (fun _ : Unit ↦ (jet ((), 0) : JetField C Unit)) :=
  JetField.differentialIndependent_jet

/-- **The projective time law of a differential protocol on the free differential rational
field.**  The phase tails transport exactly; either every tail is the base field, or every tail is
carried by a hypertranscendental coordinate, successive coordinates are fractional-linear in each
other over the constants with a coefficient matrix determined up to a scalar, and the Schwarzian of
the coordinate is a nonconstant observable transported unchanged along the protocol. -/
theorem freeDifferentialProtocol_projective_time_law
    (φ : ℕ → JetField C Unit →ₐ[C] JetField C Unit)
    (hφ : ∀ i x, φ i x′ = (φ i x)′) :
    (∀ i, IntermediateField.map (φ i) (nonautonomousTail φ (i + 1)) = nonautonomousTail φ i) ∧
      ((∀ i, nonautonomousTail φ i = ⊥) ∨
        ∃ u : ℕ → JetField C Unit,
          (∀ i, HypertranscendentalOver C (u i)) ∧
          (∀ i, differentialAdjoin C ({u i} : Set (JetField C Unit)) = nonautonomousTail φ i) ∧
          (∀ i, ∃ a b c d : C, a * d - b * c ≠ 0 ∧
            φ i (u (i + 1)) * (algebraMap C (JetField C Unit) c * u i
                + algebraMap C (JetField C Unit) d)
              = algebraMap C (JetField C Unit) a * u i
                + algebraMap C (JetField C Unit) b) ∧
          (∀ i, ∀ a b c d a' b' c' d' : C, a * d - b * c ≠ 0 → a' * d' - b' * c' ≠ 0 →
            φ i (u (i + 1)) * (algebraMap C (JetField C Unit) c * u i
                + algebraMap C (JetField C Unit) d)
              = algebraMap C (JetField C Unit) a * u i
                + algebraMap C (JetField C Unit) b →
            φ i (u (i + 1)) * (algebraMap C (JetField C Unit) c' * u i
                + algebraMap C (JetField C Unit) d')
              = algebraMap C (JetField C Unit) a' * u i
                + algebraMap C (JetField C Unit) b' →
            ∃ t : C, t ≠ 0 ∧ a' = t * a ∧ b' = t * b ∧ c' = t * c ∧ d' = t * d) ∧
          (∀ i, φ i (schwarzian (u (i + 1))) = schwarzian (u i)) ∧
          (∀ i, ∀ t : C, schwarzian (u i) ≠ algebraMap C (JetField C Unit) t)) := by
  classical
  letI : Differential C := ⟨0⟩
  haveI : DifferentialAlgebra C (JetField C Unit) :=
    ⟨fun a => by rw [deriv_algebraMap_jetField a]; exact (map_zero _).symm⟩
  refine ⟨fun i => map_nonautonomousTail_eq φ i, ?_⟩
  rcases nonautonomousTail_dichotomy φ with hbot | hne
  · exact Or.inl hbot
  refine Or.inr ?_
  choose u hu1 hu2 using fun i =>
    exists_nonautonomousTail_hypertranscendental_generator deriv_algebraMap_jetField
      differentialIndependent_jet_zero differentialAdjoin_jet_zero_eq_top φ hφ i (hne i)
  refine ⟨u, hu1, hu2, ?_, ?_, ?_, ?_⟩
  · intro i
    exact nonautonomousTail_projective_transition deriv_algebraMap_jetField
      differentialIndependent_jet_zero differentialAdjoin_jet_zero_eq_top φ hφ hne
      (hu2 i) (hu2 (i + 1))
  · intro i a b c d a' b' c' d' hdet hdet' h h'
    have htu : Transcendental C (u i) := by
      simpa using hypertranscendentalOver_jet_transcendental (hu1 i) 0
    exact mobius_coefficients_unique htu hdet hdet' h h'
  · intro i
    exact nonautonomousTail_schwarzian_transport deriv_algebraMap_jetField
      differentialIndependent_jet_zero differentialAdjoin_jet_zero_eq_top φ hφ hne
      (hu2 i) (hu2 (i + 1))
  · intro i t
    exact schwarzian_ne_constant_of_hypertranscendentalOver (hu1 i) t

end

end GaloisForLFunctions.HTGeometry
