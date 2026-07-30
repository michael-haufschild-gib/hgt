import GaloisForLFunctions.HTGeometry.RealPolynomialGenericity
import GaloisForLFunctions.HTGeometry.SpectralRelationOrbitPolynomial
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Generic projective independence from one coefficient witness

Characteristic coefficients are polynomial functions of Hamiltonian
parameters.  Once one parameter value has maximally projective real roots,
every nonzero balanced relation obstruction is a nonzero parameter
polynomial.  Countable real-polynomial avoidance then makes simultaneous
projective independence residual and full measure.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pull one universal unordered spectral-relation obstruction back along a
real-polynomial characteristic-coefficient family. -/
def spectralCoefficientObstructionPullback
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℝ)
    (k : I → ℤ) :
    MvPolynomial θ ℝ :=
  MvPolynomial.aeval coefficient
    ((spectralRelationCoefficientPolynomial k).map
      (Rat.castHom ℝ))

theorem eval_spectralCoefficientObstructionPullback
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℝ)
    (k : I → ℤ) (p : θ → ℝ) :
    MvPolynomial.eval p
        (spectralCoefficientObstructionPullback
          coefficient k) =
      MvPolynomial.eval₂ (Rat.castHom ℝ)
        (fun i =>
          MvPolynomial.eval p (coefficient i))
        (spectralRelationCoefficientPolynomial k) := by
  unfold spectralCoefficientObstructionPullback
  change
    (MvPolynomial.aeval p)
        (MvPolynomial.aeval coefficient
          ((spectralRelationCoefficientPolynomial k).map
            (Rat.castHom ℝ))) = _
  rw [MvPolynomial.comp_aeval_apply]
  rw [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map]
  rfl

/-- Maximal projective independence is invariant under spectral
relabeling. -/
theorem MaximallyProjectiveEnergy.permute
    {I : Type*} [Fintype I]
    {energy : I → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (σ : Equiv.Perm I) :
    MaximallyProjectiveEnergy
      (fun i => energy (σ i)) := by
  intro k hbalanced hzero
  let k' : I → ℤ :=
    fun j => k (σ.symm j)
  have hbalanced' :
      SpectralCharacterBalanced k' := by
    unfold SpectralCharacterBalanced at hbalanced ⊢
    have hsum :=
      σ.bijective.sum_comp (fun j => k' j)
    have hleft :
        (∑ i, k' (σ i)) = 0 := by
      simpa [k'] using hbalanced
    exact hsum.symm.trans hleft
  have hzero' :
      (∑ j, (k' j : ℝ) * energy j) = 0 := by
    have hsum :=
      σ.bijective.sum_comp
        (fun j => (k' j : ℝ) * energy j)
    have hleft :
        (∑ i, (k' (σ i) : ℝ) *
          energy (σ i)) = 0 := by
      simpa [k'] using hzero
    exact hsum.symm.trans hleft
  have hk' : k' = 0 :=
    hmax k' hbalanced' hzero'
  funext i
  have hi := congrFun hk' (σ i)
  simpa [k'] using hi

/-- Every relabeling-orbit obstruction is nonzero on a maximally
projective real spectrum. -/
theorem spectralRelationOrbitValue_ne_zero_of_maximallyProjective
    {I : Type*} [Fintype I]
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (k : I → ℤ)
    (hbalanced : SpectralCharacterBalanced k)
    (hk : k ≠ 0) :
    spectralRelationOrbitValue k energy ≠ 0 := by
  rw [spectralRelationOrbitValue_ne_zero_iff]
  intro σ hzero
  exact hk
    (hmax.permute σ k hbalanced hzero)

/-- One maximally projective root packet proves that the pulled-back
coefficient obstruction for every nonzero balanced character is a nonzero
parameter polynomial. -/
theorem spectralCoefficientObstructionPullback_ne_zero_of_witness
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℝ)
    (p : θ → ℝ)
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (hcoefficient :
      ∀ i,
        MvPolynomial.eval p (coefficient i) =
          MvPolynomial.eval₂ (Rat.castHom ℝ)
            energy
            (MvPolynomial.esymm I ℚ (i + 1)))
    (k : I → ℤ)
    (hbalanced : SpectralCharacterBalanced k)
    (hk : k ≠ 0) :
    spectralCoefficientObstructionPullback
      coefficient k ≠ 0 := by
  have heval :
      MvPolynomial.eval p
          (spectralCoefficientObstructionPullback
            coefficient k) ≠ 0 := by
    rw [eval_spectralCoefficientObstructionPullback]
    simp_rw [hcoefficient]
    rw [
      eval₂_spectralRelationCoefficientPolynomial_real_esymm,
      eval₂_spectralRelationOrbitPolynomial_real]
    exact
      spectralRelationOrbitValue_ne_zero_of_maximallyProjective
        energy hmax k hbalanced hk
  intro hzero
  apply heval
  rw [hzero]
  simp

/-- Parameters at which every nonzero balanced unordered spectral
obstruction survives. -/
def spectralCoefficientProjectiveGenericSet
    {θ I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) → MvPolynomial θ ℝ) :
    Set (θ → ℝ) :=
  {p |
    ∀ k : I → ℤ,
      SpectralCharacterBalanced k →
      k ≠ 0 →
      MvPolynomial.eval p
        (spectralCoefficientObstructionPullback
          coefficient k) ≠ 0}

/-- **One-witness genericity theorem.** If one parameter value has a
maximally projective real root packet with the prescribed characteristic
coefficients, simultaneous avoidance of every projective spectral relation
is dense, residual, and full measure. -/
theorem
    spectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure
    {m : ℕ} {I : Type*} [Fintype I]
    (coefficient :
      Fin (Fintype.card I) →
        MvPolynomial (Fin m) ℝ)
    (p₀ : Fin m → ℝ)
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (hcoefficient :
      ∀ i,
        MvPolynomial.eval p₀ (coefficient i) =
          MvPolynomial.eval₂ (Rat.castHom ℝ)
            energy
            (MvPolynomial.esymm I ℚ (i + 1))) :
    Dense
        (spectralCoefficientProjectiveGenericSet
          coefficient) ∧
      spectralCoefficientProjectiveGenericSet
          coefficient ∈
        residual (Fin m → ℝ) ∧
      volume
        (spectralCoefficientProjectiveGenericSet
          coefficient)ᶜ = 0 := by
  let J :=
    {k : I → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}
  letI : Countable J := by
    dsimp [J]
    infer_instance
  letI : Encodable J :=
    Encodable.ofCountable J
  let P : ℕ → MvPolynomial (Fin m) ℝ :=
    fun n =>
      match (Encodable.decode n : Option J) with
      | none => 1
      | some k =>
          spectralCoefficientObstructionPullback
            coefficient k.1
  have hP : ∀ n, P n ≠ 0 := by
    intro n
    unfold P
    split
    · simp
    · rename_i k hdecode
      exact
        spectralCoefficientObstructionPullback_ne_zero_of_witness
          coefficient p₀ energy hmax hcoefficient
          k.1 k.2.1 k.2.2
  have hset :
      spectralCoefficientProjectiveGenericSet
          coefficient =
        realPolynomialAvoidanceSet P := by
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
    realPolynomialAvoidanceSet_dense_residual_fullMeasure
      P hP

end

end GaloisForLFunctions.HTGeometry
