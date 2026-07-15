import GaloisForLFunctions.HTGeometry.TailCompletePrimeValuationFusionRepresentation

/-!
# Tail-complete prime-valuation fusion duality

The full homogeneous prime-tail relation system does more than remember ranks.  It reconstructs
the homogeneous algebraic hull of the source constraint, and it detects exactly when a homogeneous
polynomial map descends between two such reconstructed geometries.  Together with the faithful
fusion representation, this is the object-and-morphism form of prime-valuation reconstruction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Set

noncomputable section

/-- The homogeneous algebraic hull of a source constraint: the common zero locus of all
homogeneous polynomials vanishing on the source. -/
def homogeneousConstraintHull
    {σ : Type*} (K : Set (σ → ℂ)) : Set (σ → ℂ) :=
  {v | ∀ m (Q : homogeneousSubmodule σ ℂ m),
    Q ∈ homogeneousConstraintVanishingSubmodule K m → eval v Q.1 = 0}

/-- Every source constraint is contained in its homogeneous algebraic hull. -/
theorem subset_homogeneousConstraintHull
    {σ : Type*} (K : Set (σ → ℂ)) :
    K ⊆ homogeneousConstraintHull K := by
  intro v hv m Q hQ
  exact hQ v hv

/-- Passing to the homogeneous hull changes no homogeneous relation in any degree. -/
theorem homogeneousConstraintVanishingSubmodule_hull
    {σ : Type*} (K : Set (σ → ℂ)) (m : ℕ) :
    homogeneousConstraintVanishingSubmodule (homogeneousConstraintHull K) m =
      homogeneousConstraintVanishingSubmodule K m := by
  ext Q
  constructor
  · intro hQ v hv
    exact hQ v (subset_homogeneousConstraintHull K hv)
  · intro hQ v hv
    exact hv m Q hQ

/-- The homogeneous hull operation is idempotent. -/
theorem homogeneousConstraintHull_idempotent
    {σ : Type*} (K : Set (σ → ℂ)) :
    homogeneousConstraintHull (homogeneousConstraintHull K) =
      homogeneousConstraintHull K := by
  ext v
  constructor
  · intro hv m Q hQ
    apply hv m Q
    rw [homogeneousConstraintVanishingSubmodule_hull]
    exact hQ
  · intro hv
    exact subset_homogeneousConstraintHull (homogeneousConstraintHull K) hv

/-- **Homogeneous reconstruction duality.**  Two constraints have the same homogeneous
algebraic hull exactly when all of their homogeneous vanishing spaces agree. -/
theorem homogeneousConstraintHull_eq_iff_vanishingSubmodules_eq
    {σ : Type*} (K L : Set (σ → ℂ)) :
    homogeneousConstraintHull K = homogeneousConstraintHull L ↔
      ∀ m, homogeneousConstraintVanishingSubmodule K m =
        homogeneousConstraintVanishingSubmodule L m := by
  constructor
  · intro h m
    rw [← homogeneousConstraintVanishingSubmodule_hull K m, h,
      homogeneousConstraintVanishingSubmodule_hull L m]
  · intro h
    ext v
    constructor
    · intro hv m Q hQL
      apply hv m Q
      rw [h m]
      exact hQL
    · intro hv m Q hQK
      apply hv m Q
      rw [← h m]
      exact hQK

/-- **Object reconstruction from the arithmetic tail.**  For tail-complete sources, equality of
the entire labelled prime-valuation relation system is equivalent to equality of the homogeneous
algebraic source hulls. -/
theorem cofiniteTailDenseOn_homogeneousRelationSystem_eq_iff_constraintHull_eq
    {σ : Type*} [Fintype σ]
    (x y : Nat.Primes → σ → ℂ)
    (K L : Set (σ → ℂ))
    (hx : CofiniteTailDenseOn x K) (hy : CofiniteTailDenseOn y L) :
    (∀ m, homogeneousTailRelationSubmodule x m =
        homogeneousTailRelationSubmodule y m) ↔
      homogeneousConstraintHull K = homogeneousConstraintHull L := by
  constructor
  · intro h
    apply (homogeneousConstraintHull_eq_iff_vanishingSubmodules_eq K L).2
    exact (cofiniteTailDenseOn_homogeneousRelationSystem_eq_iff_constraintSystem_eq
      x y K L hx hy).1 h
  · intro h
    apply (cofiniteTailDenseOn_homogeneousRelationSystem_eq_iff_constraintSystem_eq
      x y K L hx hy).2
    exact (homogeneousConstraintHull_eq_iff_vanishingSubmodules_eq K L).1 h

/-- **Geometric morphism criterion.**  A homogeneous polynomial map sends a constraint into the
homogeneous hull of another constraint exactly when pullback sends every target homogeneous
relation into a source homogeneous relation. -/
theorem HomogeneousConstraintMap.mapsTo_hull_iff_pullback_vanishing
    {σ τ : Type*} {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (K : Set (σ → ℂ)) (L : Set (τ → ℂ)) :
    Set.MapsTo Φ.apply K (homogeneousConstraintHull L) ↔
      ∀ m (Q : homogeneousSubmodule τ ℂ m),
        Q ∈ homogeneousConstraintVanishingSubmodule L m →
          Φ.pullback Q ∈ homogeneousConstraintVanishingSubmodule K (q * m) := by
  constructor
  · intro hmap m Q hQ v hv
    rw [Φ.eval_pullback]
    exact hmap hv m Q hQ
  · intro hpull v hv m Q hQ
    rw [← Φ.eval_pullback]
    exact hpull m Q hQ v hv

/-- **Arithmetic morphism reconstruction.**  Between tail-complete sources, a homogeneous map
lands in the reconstructed target geometry exactly when its pullback preserves the complete
labelled prime-tail relation system with the forced degree dilation `m ↦ q*m`. -/
theorem cofiniteTailDenseOn_homogeneousMap_mapsTo_hull_iff_pullback_tailRelations
    {σ τ : Type*} [Fintype σ] [Fintype τ] {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (x : Nat.Primes → σ → ℂ) (y : Nat.Primes → τ → ℂ)
    (K : Set (σ → ℂ)) (L : Set (τ → ℂ))
    (hx : CofiniteTailDenseOn x K) (hy : CofiniteTailDenseOn y L) :
    Set.MapsTo Φ.apply K (homogeneousConstraintHull L) ↔
      ∀ m (Q : homogeneousSubmodule τ ℂ m),
        Q ∈ homogeneousTailRelationSubmodule y m →
          Φ.pullback Q ∈ homogeneousTailRelationSubmodule x (q * m) := by
  constructor
  · intro hmap m Q hQ
    have hQL : Q ∈ homogeneousConstraintVanishingSubmodule L m := by
      rw [← homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
        y L hy m]
      exact hQ
    have hQK :=
      (Φ.mapsTo_hull_iff_pullback_vanishing K L).1 hmap m Q hQL
    rw [homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
      x K hx (q * m)]
    exact hQK
  · intro hpull
    apply (Φ.mapsTo_hull_iff_pullback_vanishing K L).2
    intro m Q hQ
    have hQtail : Q ∈ homogeneousTailRelationSubmodule y m := by
      rw [homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
        y L hy m]
      exact hQ
    have hresult := hpull m Q hQtail
    rw [homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
      x K hx (q * m)] at hresult
    exact hresult

end

end GaloisForLFunctions.HTGeometry
