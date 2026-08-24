import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.HollowSimplexBouquetHasse
import GaloisForLFunctions.HTGeometry.ConstitutiveNonabelianRecoveryHasse
import GaloisForLFunctions.HTGeometry.TwoReplicaLocalCommutatorHasse
import GaloisForLFunctions.HTGeometry.FiniteTwoReplicaSingleSiteHasse
import GaloisForLFunctions.HTGeometry.StanleyReisnerEmptyTriangleHasse

/-!
# Topological and combinatorial Hasse-family applications

Canonical local places outside arithmetic: hollow-simplex components, primitive permutation
cycles, Pauli axes, and site/axis pairs.  Each complete local packet separates a global quotient;
the hollow-simplex packet additionally glues arbitrary local coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F alpha : Type*} [Field F] [DecidableEq alpha] [Fintype alpha]

/-- Pairwise-disjoint hollow-simplex detectors jointly determine first Koszul homology modulo
their common invisible sector. -/
def hollowBouquetQuotientHasseFamily
    (facets : Finset (Finset alpha)) {k : ℕ}
    (sigma : Fin k → Finset alpha) (i0 : Fin k → alpha)
    (hface : ∀ m, ∀ v ∈ sigma m,
      IsFaceOf (↑facets : Set (Finset alpha)) ((sigma m).erase v))
    (hmem : ∀ m, i0 m ∈ sigma m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (sigma m) (sigma n)) :
    HasseFamily
      (SRFirstKoszulHomology F facets ⧸
        LinearMap.ker (hollowBouquetHasseProfile (F := F) facets sigma hface))
      (Fin k) where
  Local := fun _ => F
  profile := fun x m =>
    hollowBouquetHasseQuotientEquiv facets sigma i0 hface hmem hdisj x m
  profile_injective := by
    intro x y hxy
    apply (hollowBouquetHasseQuotientEquiv facets sigma i0 hface hmem hdisj).injective
    funext m
    exact congrFun hxy m

variable {S G : Type*} [Fintype S] [Group G]

/-- Primitive-cycle conjugacy classes jointly determine a global nonabelian gauge class. -/
def groupGaugePrimitiveCycleHasseFamily (T : Equiv.Perm S) :
    HasseFamily (GroupGaugeClasses T G)
      (Quotient (Equiv.Perm.SameCycle.setoid T)) where
  Local := fun _ => ConjClasses G
  profile := groupGaugeClassHasseMap T
  profile_injective := groupGaugeClassHasseMap_injective T

/-- The three Pauli-axis commutators jointly determine a two-replica operator modulo
identity/swap gauge. -/
def twoReplicaPauliAxisHasseFamily :
    HasseFamily (TwoReplicaLocalMatrix ⧸ twoReplicaLocalGaugePlane) (Fin 3) where
  Local := fun _ => TwoReplicaLocalMatrix
  profile := fun x a => (twoReplicaLocalCommutatorHasseEquivRealizedProfiles x).1 a
  profile_injective := by
    intro x y hxy
    apply twoReplicaLocalCommutatorHasseEquivRealizedProfiles.injective
    apply Subtype.ext
    funext a
    exact congrFun hxy a

/-- Every site/Pauli-axis pair jointly determines a finite-register two-replica operator modulo
the product-Clifford twirl sector. -/
def finiteTwoReplicaSingleSiteHasseFamily
    {V : Type*} [Fintype V] [DecidableEq V] :
    HasseFamily (FiniteTwoReplicaSingleSiteHasseClass (V := V)) (V × Fin 3) where
  Local := fun _ => FiniteTwoReplicaMatrix V
  profile := fun x p => (finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles x).1 p.1 p.2
  profile_injective := by
    intro x y hxy
    apply finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles.injective
    apply Subtype.ext
    funext j a
    exact congrFun hxy (j, a)

/-- Empty-triangle local coefficient packets modulo globally generated zero-sum packets have their
coefficient sum as one complete obstruction coordinate. -/
noncomputable def srEmptyTriangleObstructionHasseFamily
    (R : Type*) [CommRing R] :=
  HasseFamily.ofEquivSingle (srEmptyTriangleHasseQuotientEquiv (R := R)).toEquiv

end
end GaloisForLFunctions.HTGeometry
