import GaloisForLFunctions.EffectiveScalingGeometry.DirichletPersistenceEquivalence
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeArithmeticPersistence

/-!
# Exact deaths of Dirichlet-weighted homology classes

The birth/death interpretation of persistent homology in Luo--Evans,
arXiv:2608.28822, applies to the prime-product filtration. Its arithmetic
coordinates give a stronger conclusion: every class dies exactly when all
its nonzero odd-squarefree coordinates have reached their doubled birth height.
The Dirichlet gauge preserves this statement for every complex parameter.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- Dirichlet-weighted homology has the same odd-squarefree interval coordinates. -/
def dirichletHomologyArithmeticIso (s : ℂ) (k : ℕ) :
    primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k ≅
      squarefreeIntervalPersistence ℂ k :=
  (dirichletHomologyPersistenceIso s k).symm ≪≫ primeHomologySquarefreeIntervalIso ℂ k

/-- Arithmetic coordinates of an actual Dirichlet-weighted homology class. -/
def dirichletHomologyCoordinates (s : ℂ) (k N : ℕ) :
    (primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k).obj N ≃ₗ[ℂ]
      squarefreeCriticalCoordinates ℂ k N :=
  ((dirichletHomologyArithmeticIso s k).app N).toLinearEquiv

/-- A class vanishes precisely when every coordinate has passed its death height. -/
theorem squarefreeCriticalMap_eq_zero_iff (R : Type*) [CommRing R]
    (k N d : ℕ) (x : squarefreeCriticalCoordinates R k N) :
    squarefreeCriticalMap R k N (N+d) x = 0 ↔
      ∀ m : SquarefreeDegree k, x.val m ≠ 0 → 2*m.val ≤ N+d := by
  classical
  constructor
  · intro hz m hm
    have hsource : m ∈ squarefreeCriticalLabels k N := by
      by_contra h
      exact hm (((Finsupp.mem_supported' R x.val).mp x.property) m h)
    by_contra hdeath
    have htarget : m ∈ squarefreeCriticalLabels k (N+d) :=
      ⟨hsource.1, by have := hsource.2.1; omega, by omega⟩
    have he := congrArg (fun y : squarefreeCriticalCoordinates R k (N+d) => y.val m) hz
    rw [squarefreeCriticalMap_apply, if_pos htarget] at he
    exact hm he
  · intro h
    apply Subtype.ext
    ext m
    rw [squarefreeCriticalMap_apply]
    by_cases ht : m ∈ squarefreeCriticalLabels k (N+d)
    · rw [if_pos ht]
      by_contra hm
      exact (not_le_of_gt ht.2.2) (h m hm)
    · rw [if_neg ht]
      rfl

/-- Naturality identifies the actual homology map with coordinate deletion. -/
theorem dirichletHomologyCoordinates_map (s : ℂ) (k N d : ℕ)
    (x : (primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k).obj N) :
    dirichletHomologyCoordinates s k (N+d)
        ((primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k).map
          (homOfLE (Nat.le_add_right N d)) x) =
      squarefreeCriticalMap ℂ k N (N+d) (dirichletHomologyCoordinates s k N x) := by
  exact congrArg (fun f => f x)
    ((dirichletHomologyArithmeticIso s k).hom.naturality
      (homOfLE (Nat.le_add_right N d)))

/-- Exact hole-filling criterion, with no restriction on the Dirichlet parameter. -/
theorem dirichletHomology_death_iff (s : ℂ) (k N d : ℕ)
    (x : (primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k).obj N) :
    (primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k).map
        (homOfLE (Nat.le_add_right N d)) x = 0 ↔
      ∀ m : SquarefreeDegree k,
        (dirichletHomologyCoordinates s k N x).val m ≠ 0 → 2*m.val ≤ N+d := by
  rw [← (dirichletHomologyCoordinates s k (N+d)).map_eq_zero_iff,
    dirichletHomologyCoordinates_map, squarefreeCriticalMap_eq_zero_iff]

/-- Every hole present at height `N` has filled by height `2N`. -/
theorem dirichletHomology_doubling_map_zero (s : ℂ) (k N : ℕ) :
    (primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k).map
      (homOfLE (Nat.le_add_right N N)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (dirichletHomology_death_iff s k N N x).mpr
  intro m hm
  have hsource : m ∈ squarefreeCriticalLabels k N := by
    by_contra h
    exact hm (((Finsupp.mem_supported' ℂ (dirichletHomologyCoordinates s k N x).val).mp
      (dirichletHomologyCoordinates s k N x).property) m h)
  have := hsource.2.1
  omega

end GaloisForLFunctions.EffectiveScalingGeometry
