import GaloisForLFunctions.HTGeometry.ToricIsogenyTailLaw
import GaloisForLFunctions.HTGeometry.FreeDifferentialProtocolTimeLaw

/-!
# Unconditional split-torus isogeny tail

The free differential rational field on finitely many generators supplies the generic point,
differential independence, generation, and constant-field structure required by the abstract toric
power-isogeny theorem.  Thus no external genericity or differential-algebra hypotheses remain.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance freeToricComplexDifferential : Differential ℂ := ⟨0⟩

local instance freeToricDifferentialAlgebra (r : ℕ) :
    DifferentialAlgebra ℂ (JetField ℂ (Fin r)) := by
  refine ⟨fun z => ?_⟩
  rw [JetField.deriv_algebraMap z]
  exact (map_zero _).symm

/-- The order-zero jets are the concrete generic point of the split torus. -/
def freeTorusGenerator (r : ℕ) (i : Fin r) : JetField ℂ (Fin r) :=
  JetField.jet (i, 0)

/-- All differential jets of the concrete generic point are exactly the free coordinates. -/
theorem differentialJetSet_freeTorusGenerator (r : ℕ) :
    differentialJetSet (Set.range (freeTorusGenerator r)) =
      Set.range (fun p : Fin r × ℕ => (JetField.jet p : JetField ℂ (Fin r))) := by
  ext z
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, n, rfl⟩
    exact ⟨(i, n), (JetField.differentialJet_jet_of_zero i n).symm⟩
  · rintro ⟨⟨i, n⟩, rfl⟩
    exact ⟨freeTorusGenerator r i, ⟨i, rfl⟩, n,
      JetField.differentialJet_jet_of_zero i n⟩

/-- The concrete generic point differentially generates the entire free jet field. -/
theorem differentialAdjoin_freeTorusGenerator_eq_top (r : ℕ) :
    differentialAdjoin ℂ (Set.range (freeTorusGenerator r)) = ⊤ := by
  rw [differentialAdjoin, differentialJetSet_freeTorusGenerator]
  have hrange :
      Set.range (fun p : Fin r × ℕ => (JetField.jet p : JetField ℂ (Fin r))) =
        freeCoordinate ℂ (Fin r × ℕ) '' Set.univ := by
    ext z
    simp only [Set.image_univ]
    rfl
  rw [hrange]
  exact freeCoordinateField_univ (C := ℂ) (σ := Fin r × ℕ)

/-- The concrete torus generators are differentially independent. -/
theorem differentialIndependent_freeTorusGenerator (r : ℕ) :
    DifferentialIndependent ℂ (freeTorusGenerator r) := by
  exact JetField.differentialIndependent_jet

/-- The chosen complex base differential is zero. -/
theorem deriv_complex_eq_zero (z : ℂ) : z′ = 0 := by
  rfl

/-- **Unconditional split-torus power-isogeny tail.**  For every finite rank and every power at
least two, the stable tail is exactly the logarithmic-velocity field.  The velocity coordinates are
differentially independent, meet the position field only in the constants, and transform with
weight one.  Genericity, generation, and constant-field compatibility are discharged by the free
differential field construction. -/
theorem freeToricPowerIsogenyTail (r : ℕ) (N : {n : ℕ // 2 ≤ n}) :
    let x := freeTorusGenerator r
    let hx := differentialIndependent_freeTorusGenerator r
    let hgen := differentialAdjoin_freeTorusGenerator_eq_top r
    stableRangeCore
        (torusEndo hx hgen
          (det_scalarMatrix_ne_zero (r := r) (ne_zero_of_two_le N.property)))
        = torusVelocityField ℂ x
      ∧ DifferentialIndependent ℂ (fun k => Differential.logDeriv (x k))
      ∧ torusVelocityField ℂ x ⊓ IntermediateField.adjoin ℂ (Set.range x)
          = (⊥ : IntermediateField ℂ (JetField ℂ (Fin r)))
      ∧ ∀ i, torusEndo hx hgen
            (det_scalarMatrix_ne_zero (r := r) (ne_zero_of_two_le N.property))
            (Differential.logDeriv (x i))
          = (N.1 : JetField ℂ (Fin r)) * Differential.logDeriv (x i) := by
  exact toricPowerIsogenyTail
    (differentialIndependent_freeTorusGenerator r)
    (differentialAdjoin_freeTorusGenerator_eq_top r)
    deriv_complex_eq_zero N.property

end

end GaloisForLFunctions.HTGeometry
