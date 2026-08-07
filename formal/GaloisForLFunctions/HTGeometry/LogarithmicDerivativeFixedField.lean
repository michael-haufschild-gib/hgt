import GaloisForLFunctions.HTGeometry.FreeDifferentialScalingAutomorphism

/-!
# The logarithmic derivative is the scaling-invariant coordinate

In a freely differentially generated field `F⟨y⟩` the scaling automorphisms `y ↦ a·y` fix the
logarithmic derivative `ℓ = y′/y`, and every jet of `y` is a `F⟨ℓ⟩`-multiple of `y`.  So `y`
generates the whole field over `F⟨ℓ⟩` by a single ordinary adjunction, and the multiplicative deck
group acts on that single coordinate.

This is the `G_m` case of the position–velocity splitting: the erased sector is the whole group,
the reversible position is trivial, and the persistent information is exactly the Maurer–Cartan
velocity `ℓ`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- **The scaling automorphisms fix the logarithmic derivative.** -/
theorem scalingAutomorphism_logDeriv (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    scalingAutomorphism hF ha hy hytop (y′ / y) = y′ / y := by
  have hσ := scalingAutomorphism_deriv hF ha hy hytop y
  have hgen := scalingAutomorphism_generator hF ha hy hytop
  have haE : algebraMap F E a ≠ 0 := by
    intro h
    exact ha ((algebraMap F E).injective (by rw [h, map_zero]))
  rw [map_div₀, hσ, hgen]
  have hderiv : (algebraMap F E a * y)′ = algebraMap F E a * y′ := by
    have hleib := Differential.deriv.leibniz (algebraMap F E a) y
    simp only [smul_eq_mul] at hleib
    rw [hleib, hF a, mul_zero, add_zero]
  rw [hderiv, mul_div_mul_left _ _ haE]

/-- **Every jet of the generator is an `F⟨y′/y⟩`-multiple of the generator.** -/
theorem exists_logDerivField_coeff {y : E} (hy0 : y ≠ 0) (n : ℕ) :
    ∃ p ∈ differentialAdjoin F ({y′ / y} : Set E), differentialJet n y = p * y := by
  induction n with
  | zero =>
      refine ⟨1, (differentialAdjoin F ({y′ / y} : Set E)).one_mem, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨p, hp, hpn⟩ := ih
      refine ⟨p′ + p * (y′ / y), ?_, ?_⟩
      · exact (differentialAdjoin F ({y′ / y} : Set E)).add_mem
          (derivationClosed_differentialAdjoin F _ hp)
          ((differentialAdjoin F ({y′ / y} : Set E)).mul_mem hp
            (subset_differentialAdjoin F _ rfl))
      · rw [differentialJet_succ, hpn]
        have hleib := Differential.deriv.leibniz p y
        simp only [smul_eq_mul] at hleib
        rw [hleib]
        field_simp
        ring

/-- **The generator adjoins the whole field to the logarithmic-derivative field.** -/
theorem adjoin_generator_over_logDerivField {y : E} (hy0 : y ≠ 0)
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    (IntermediateField.adjoin (↥(differentialAdjoin F ({y′ / y} : Set E))) ({y} : Set E)
      ).restrictScalars F = ⊤ := by
  set L : IntermediateField F E := differentialAdjoin F ({y′ / y} : Set E) with hL
  set M : IntermediateField F E :=
    (IntermediateField.adjoin (↥L) ({y} : Set E)).restrictScalars F with hM
  have hjet : ∀ n : ℕ, differentialJet n y ∈ M := by
    intro n
    obtain ⟨p, hp, hpn⟩ := exists_logDerivField_coeff (F := F) hy0 n
    have hpM : p ∈ M := by
      have h := (IntermediateField.adjoin (↥L) ({y} : Set E)).algebraMap_mem ⟨p, hp⟩
      change p ∈ IntermediateField.adjoin (↥L) ({y} : Set E)
      simpa using h
    have hyM : y ∈ M := by
      have : y ∈ IntermediateField.adjoin (↥L) ({y} : Set E) :=
        IntermediateField.subset_adjoin _ _ rfl
      exact this
    rw [hpn]
    exact M.mul_mem hpM hyM
  refine top_le_iff.mp ?_
  rw [← hytop]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro z ⟨x, hx, n, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hjet n

end

end GaloisForLFunctions.HTGeometry
