import GaloisForLFunctions.HTGeometry.ScalarAdditiveDifferentialTorsor
import GaloisForLFunctions.HTGeometry.ScalarEigenDifferentialTorsor
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonComplementarity

/-!
# Additive and eigen differential torsors are disjoint

A translation by one fixes the derivative coordinate.  A constant-unit eigen action scales the
same derivative coordinate by that unit.  Hypertranscendence makes the derivative nonzero, so a
single automorphism cannot realize both mechanisms: derivative compatibility forces the unit to
be one, while the value equations would then force `q + 1 = q`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Additive/eigen torsor disjointness law.**  No derivation-preserving automorphism can act on
one hypertranscendental scalar both as unit translation and as multiplication by a constant unit. -/
theorem DifferentialAlgEquiv.not_translate_one_and_unit_eigenvector
    {F T : Type*} [Field F] [Field T] [Algebra F T]
    [Differential F] [Differential T] [DifferentialAlgebra F T]
    (sigma : DifferentialAlgEquiv F T) (q : T)
    (hq : HypertranscendentalOver F q)
    (u : Fˣ) (hconst : ∀ c : F, c′ = 0) :
    ¬ (sigma.toAlgEquiv q = q + algebraMap F T 1 ∧
      sigma.toAlgEquiv q = q * algebraMap F T (u : F)) := by
  rintro ⟨htranslate, heigen⟩
  have hderivFixed : sigma.toAlgEquiv q′ = q′ :=
    sigma.deriv_fixed_of_translate_one q htranslate
  have hderivScaled : sigma.toAlgEquiv q′ = q′ * algebraMap F T (u : F) := by
    calc
      sigma.toAlgEquiv q′ = (sigma.toAlgEquiv q)′ := sigma.map_deriv' q
      _ = (q * algebraMap F T (u : F))′ := congrArg Differential.deriv heigen
      _ = q′ * algebraMap F T (u : F) := by
        rw [Derivation.leibniz, deriv_algebraMap, hconst]
        simp
        ring
  have hqPrimeNe : q′ ≠ 0 := by
    simpa using (hypertranscendentalOver_differentialJet_ne_zero hq 1)
  have hscaleIdentity : algebraMap F T (u : F) = 1 := by
    apply mul_left_cancel₀ hqPrimeNe
    simpa using (hderivFixed.symm.trans hderivScaled).symm
  have hu : (u : F) = 1 := by
    apply (algebraMap F T).injective
    simpa using hscaleIdentity
  have hvalueCollision : q + algebraMap F T 1 = q * algebraMap F T (u : F) :=
    htranslate.symm.trans heigen
  rw [hu] at hvalueCollision
  simp only [map_one, mul_one] at hvalueCollision
  have honeZero : (1 : T) = 0 := by
    apply add_left_cancel (a := q)
    rw [add_zero]
    exact hvalueCollision
  exact one_ne_zero honeZero

/-- In particular, the canonical nontrivial additive translation cannot belong to any
constant-unit eigen branch on the same hypertranscendental coordinate. -/
theorem scalar_translation_one_not_unit_eigenvector
    {F T : Type*} [Field F] [Field T] [Algebra F T]
    [Differential F] [Differential T] [DifferentialAlgebra F T]
    [CharZero T]
    (q : T) (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u : Fˣ) :
    scalarDifferentialTranslationEquiv q hq hgen 1 q ≠
      q * algebraMap F T (u : F) := by
  intro heigen
  let sigmaRaw := scalarDifferentialTranslationEquiv q hq hgen 1
  let sigma : DifferentialAlgEquiv F T :=
    ⟨sigmaRaw, scalarDifferentialTranslationEquiv_deriv q hq hgen 1⟩
  apply sigma.not_translate_one_and_unit_eigenvector q hq u hconst
  refine ⟨?_, heigen⟩
  exact scalarDifferentialTranslationEquiv_apply_q q hq hgen 1

end

end GaloisForLFunctions.HTGeometry
