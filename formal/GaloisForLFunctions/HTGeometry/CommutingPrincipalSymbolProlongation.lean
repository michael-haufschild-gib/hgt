import GaloisForLFunctions.HTGeometry.GeneralPrincipalSymbolHorizonIdeal

/-!
# Commuting principal symbols require prolongation

Pairwise commuting derivations do not permit an arbitrary terminal principal symbol followed by a
free differential tail.  Commutativity one step past the terminal layer forces a first
prolongation identity.  If the first tail derivatives are linearly independent in disjoint
direction blocks, this identity forces the entire terminal symbol to vanish as soon as law space
has at least two directions.

This is the integrability obstruction missed by the naive symmetric-Fock realization.  Arbitrary
projective horizons are unconditional for free word derivations, but an abelian realization must
build a non-free prolonged terminal module satisfying these identities.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {ι η : Type w}
  [Field K] [Field L] [Algebra K L] [Fintype ι] [Fintype η]

/-- **First principal-symbol prolongation law.**  If the boundary derivative of `z` in direction
`i` is the terminal linear form with coefficient row `a i`, then pairwise commutativity forces the
displayed cross-derivative identity on every pair of rows. -/
theorem commutingDerivations_principalSymbol_firstProlongation
    (δ : ι → Derivation K L L) (z : L) (a : ι → η → K) (y : η → L)
    (hcomm : ∀ i k, Function.Commute (δ i) (δ k))
    (hboundary : ∀ i, δ i z = ∑ j, a i j • y j) :
    ∀ i k, ∑ j, a i j • δ k (y j) = ∑ j, a k j • δ i (y j) := by
  intro i k
  have h := hcomm i k z
  rw [hboundary k, hboundary i, map_sum, map_sum] at h
  simpa only [Derivation.map_smul] using h.symm

/-- **Free-tail obstruction for abelian law space.**  If every law direction has a distinct first
tail block and those blocks are linearly independent, commuting derivations force every boundary
principal-symbol coefficient to be zero. -/
theorem commutingDerivations_freeTail_forces_zeroSymbol
    (δ : ι → Derivation K L L) (z : L) (a : ι → η → K) (y : η → L)
    (hcomm : ∀ i k, Function.Commute (δ i) (δ k))
    (hboundary : ∀ i, δ i z = ∑ j, a i j • y j)
    (htail : LinearIndependent K (fun q : ι × η ↦ δ q.1 (y q.2)))
    (hother : ∀ i : ι, ∃ k : ι, k ≠ i) :
    ∀ i j, a i j = 0 := by
  classical
  intro i j
  obtain ⟨k, hki⟩ := hother i
  have hprolong := commutingDerivations_principalSymbol_firstProlongation
    δ z a y hcomm hboundary i k
  let leftCoeff : ι × η → K := fun q ↦ if q.1 = k then a i q.2 else 0
  let rightCoeff : ι × η → K := fun q ↦ if q.1 = i then a k q.2 else 0
  have hleft : Fintype.linearCombination K (fun q : ι × η ↦ δ q.1 (y q.2)) leftCoeff =
      ∑ j, a i j • δ k (y j) := by
    simp [Fintype.linearCombination_apply, leftCoeff, Fintype.sum_prod_type]
  have hright : Fintype.linearCombination K (fun q : ι × η ↦ δ q.1 (y q.2)) rightCoeff =
      ∑ j, a k j • δ i (y j) := by
    simp [Fintype.linearCombination_apply, rightCoeff, Fintype.sum_prod_type]
  have hcoeff : leftCoeff = rightCoeff := by
    apply htail.fintypeLinearCombination_injective
    exact hleft.trans (hprolong.trans hright.symm)
  have hpoint := congrFun hcoeff (k, j)
  simpa [leftCoeff, rightCoeff, hki] using hpoint

/-- Algebraic independence of the first tail packet is already more than enough to trigger the
free-tail obstruction. -/
theorem commutingDerivations_algebraicallyIndependentTail_forces_zeroSymbol
    (δ : ι → Derivation K L L) (z : L) (a : ι → η → K) (y : η → L)
    (hcomm : ∀ i k, Function.Commute (δ i) (δ k))
    (hboundary : ∀ i, δ i z = ∑ j, a i j • y j)
    (htail : AlgebraicIndependent K (fun q : ι × η ↦ δ q.1 (y q.2)))
    (hother : ∀ i : ι, ∃ k : ι, k ≠ i) :
    ∀ i j, a i j = 0 :=
  commutingDerivations_freeTail_forces_zeroSymbol
    δ z a y hcomm hboundary htail.linearIndependent hother

end

end GaloisForLFunctions.HTGeometry
