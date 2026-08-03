import GaloisForLFunctions.HTGeometry.ComplexPolynomialRealParameterGenericity
import GaloisForLFunctions.HTGeometry.SpectralCoefficientPolynomialGenericity

/-!
# Complex spectral-coefficient laws on real parameter spaces

Hermitian matrix families have complex polynomial entries but real control
parameters.  This file pulls the universal unordered spectral-relation
polynomials through complex characteristic-coefficient families and proves
one-witness residual full-measure genericity on the real parameter space.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pull one universal unordered spectral-relation obstruction through a
complex-polynomial characteristic-coefficient family. -/
def complexSpectralCoefficientObstructionPullback
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℂ)
    (k : I → ℤ) :
    MvPolynomial θ ℂ :=
  MvPolynomial.aeval coefficient
    ((spectralRelationCoefficientPolynomial k).map
      (Rat.castHom ℂ))

theorem eval_complexSpectralCoefficientObstructionPullback
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℂ)
    (k : I → ℤ) (z : θ → ℂ) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z
        (complexSpectralCoefficientObstructionPullback
          coefficient k) =
      MvPolynomial.eval₂ (Rat.castHom ℂ)
        (fun i =>
          MvPolynomial.eval₂ (RingHom.id ℂ) z
            (coefficient i))
        (spectralRelationCoefficientPolynomial k) := by
  unfold complexSpectralCoefficientObstructionPullback
  change
    (MvPolynomial.aeval z)
        (MvPolynomial.aeval coefficient
          ((spectralRelationCoefficientPolynomial k).map
            (Rat.castHom ℂ))) = _
  rw [MvPolynomial.comp_aeval_apply]
  rw [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map]
  rfl

/-- A maximally projective real root packet proves that every nonzero
balanced pulled-back complex obstruction has a real parameter witness. -/
theorem
    complexSpectralCoefficientObstructionPullback_has_real_witness
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℂ)
    (p : θ → ℝ)
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (hcoefficient :
      ∀ i,
        MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun t => (p t : ℂ))
            (coefficient i) =
          MvPolynomial.eval₂ (Rat.castHom ℂ)
            (fun a => (energy a : ℂ))
            (MvPolynomial.esymm I ℚ (i.1 + 1)))
    (k : I → ℤ)
    (hbalanced : SpectralCharacterBalanced k)
    (hk : k ≠ 0) :
    MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun t => (p t : ℂ))
        (complexSpectralCoefficientObstructionPullback
          coefficient k) ≠ 0 := by
  rw [eval_complexSpectralCoefficientObstructionPullback]
  simp_rw [hcoefficient]
  rw [
    eval₂_spectralRelationCoefficientPolynomial_complex_esymm,
    eval₂_spectralRelationOrbitPolynomial_complex]
  have hreal :
      spectralRelationOrbitValue k energy ≠ 0 :=
    spectralRelationOrbitValue_ne_zero_of_maximallyProjective
      energy hmax k hbalanced hk
  intro hzero
  apply hreal
  have hcast :
      (spectralRelationOrbitValue k energy : ℂ) =
        spectralRelationOrbitValueComplex k
          (fun a => (energy a : ℂ)) := by
    unfold spectralRelationOrbitValue
      spectralRelationOrbitValueComplex
    push_cast
    rfl
  apply Complex.ofReal_injective
  rw [hcast]
  exact hzero

/-- Real parameters at which every nonzero balanced unordered complex
spectral obstruction survives. -/
def complexSpectralCoefficientProjectiveGenericSet
    {m : ℕ} {I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) →
        MvPolynomial (Fin m) ℂ) :
    Set (Fin m → ℝ) :=
  {p |
    ∀ k : I → ℤ,
      SpectralCharacterBalanced k →
      k ≠ 0 →
      MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun t => (p t : ℂ))
        (complexSpectralCoefficientObstructionPullback
          coefficient k) ≠ 0}

/-- **Complex genericity from parameterwise witnesses.** If every nonzero
balanced obstruction is nonzero at some real parameter, simultaneous
projective independence is dense, residual, and full measure. -/
theorem
    complexSpectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure_of_witness
    {m : ℕ} {I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) →
        MvPolynomial (Fin m) ℂ)
    (hwitness :
      ∀ k : I → ℤ,
        SpectralCharacterBalanced k →
        k ≠ 0 →
        ∃ p : Fin m → ℝ,
          MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun t => (p t : ℂ))
            (complexSpectralCoefficientObstructionPullback
              coefficient k) ≠ 0) :
    Dense
        (complexSpectralCoefficientProjectiveGenericSet
          coefficient) ∧
      complexSpectralCoefficientProjectiveGenericSet
          coefficient ∈
        residual (Fin m → ℝ) ∧
      volume
        (complexSpectralCoefficientProjectiveGenericSet
          coefficient)ᶜ = 0 := by
  let J :=
    {k : I → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}
  letI : Countable J := by
    dsimp [J]
    infer_instance
  letI : Encodable J :=
    Encodable.ofCountable J
  let P : ℕ → MvPolynomial (Fin m) ℂ :=
    fun n =>
      match (Encodable.decode n : Option J) with
      | none => 1
      | some k =>
          complexSpectralCoefficientObstructionPullback
            coefficient k.1
  have hP :
      ∀ n, ∃ p : Fin m → ℝ,
        MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun t => (p t : ℂ)) (P n) ≠ 0 := by
    intro n
    unfold P
    split
    · exact ⟨0, by simp⟩
    · rename_i k hdecode
      exact hwitness k.1 k.2.1 k.2.2
  have hset :
      complexSpectralCoefficientProjectiveGenericSet
          coefficient =
        complexPolynomialRealAvoidanceSet P := by
    ext p
    constructor
    · intro hp n
      unfold P
      split
      · simp
      · rename_i k hdecode
        exact hp k.1 k.2.1 k.2.2
    · intro hp k hbalanced hk
      let j : J :=
        ⟨k, hbalanced, hk⟩
      have hj :=
        hp (Encodable.encode j)
      simpa [P, Encodable.encodek, j] using hj
  rw [hset]
  exact
    complexPolynomialRealAvoidanceSet_dense_residual_fullMeasure
      P hP

/-- **Complex one-witness genericity theorem.** If one real parameter has
a maximally projective real root packet with the prescribed complex
characteristic coefficients, simultaneous projective independence is
dense, residual, and full measure in the real parameter space. -/
theorem
    complexSpectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure
    {m : ℕ} {I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) →
        MvPolynomial (Fin m) ℂ)
    (p₀ : Fin m → ℝ)
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (hcoefficient :
      ∀ i,
        MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun t => (p₀ t : ℂ))
            (coefficient i) =
          MvPolynomial.eval₂ (Rat.castHom ℂ)
            (fun a => (energy a : ℂ))
            (MvPolynomial.esymm I ℚ (i.1 + 1))) :
    Dense
        (complexSpectralCoefficientProjectiveGenericSet
          coefficient) ∧
      complexSpectralCoefficientProjectiveGenericSet
          coefficient ∈
        residual (Fin m → ℝ) ∧
      volume
        (complexSpectralCoefficientProjectiveGenericSet
          coefficient)ᶜ = 0 :=
  complexSpectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure_of_witness
    coefficient
    (fun k hbalanced hk =>
      ⟨p₀,
        complexSpectralCoefficientObstructionPullback_has_real_witness
          coefficient p₀ energy hmax hcoefficient k hbalanced hk⟩)

end

end GaloisForLFunctions.HTGeometry
