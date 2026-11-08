import GaloisForLFunctions.EffectiveScalingGeometry.PrimeSquarefreeIndices
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeAugmentedHomology

/-!
# The arithmetic barcode of actual prime-cutoff homology

The actual augmented homology persistence functor is naturally isomorphic to
the interval-coordinate functor indexed by odd squarefree integers `m`, with
birth `m`, death `2m`, and exterior degree equal to the number of prime factors.
Reindexing by the prime-support product preserves each coefficient and commutes
with every interval restriction. This includes the empty interval `[1,2)` and
works over every commutative ring. Scalar-extension compatibility is a separate
statement about the canonical maps on actual chains.
-/

noncomputable section
open scoped Classical
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Reindex exterior-face coefficients by their squarefree products. -/
def primeCoordinateReindex (k : ℕ) :
    (Set.powersetCard Nat.Primes k →₀ R) ≃ₗ[R] (SquarefreeDegree k →₀ R) :=
  Finsupp.domLCongr (primeFaceSquarefreeEquiv k)

theorem primeCoordinateReindex_apply (k : ℕ)
    (x : Set.powersetCard Nat.Primes k →₀ R) (m : SquarefreeDegree k) :
    primeCoordinateReindex R k x m = x ((primeFaceSquarefreeEquiv k).symm m) := rfl

/-- Arithmetic coefficients alive on the intervals indexed by odd squarefree integers. -/
abbrev squarefreeCriticalCoordinates (k N : ℕ) :=
  Finsupp.supported R R (squarefreeCriticalLabels k N)

theorem primeCoordinateReindex_mem_iff (k N : ℕ) (x : Set.powersetCard Nat.Primes k →₀ R) :
    primeCoordinateReindex R k x ∈ squarefreeCriticalCoordinates R k N ↔
      x ∈ primeCriticalCoordinates R k N := by
  rw [Finsupp.mem_supported',Finsupp.mem_supported']
  constructor
  · intro h s hs
    have hm : primeFaceSquarefreeEquiv k s ∉ squarefreeCriticalLabels k N :=
      fun hm => hs ((primeFaceSquarefreeEquiv_critical k N s).mp hm)
    have hz := h (primeFaceSquarefreeEquiv k s) hm
    simpa only [primeCoordinateReindex_apply,Equiv.symm_apply_apply] using hz
  · intro h m hm
    rw [primeCoordinateReindex_apply]
    apply h
    intro hs
    have hh := (primeFaceSquarefreeEquiv_critical k N ((primeFaceSquarefreeEquiv k).symm m)).mpr hs
    exact hm (by simpa only [Equiv.apply_symm_apply] using hh)

/-- The literal coordinate equivalence at a height, preserving every coefficient. -/
def primeCriticalArithmeticEquiv (k N : ℕ) :
    primeCriticalCoordinates R k N ≃ₗ[R] squarefreeCriticalCoordinates R k N where
  toFun x := ⟨primeCoordinateReindex R k x.val,
    (primeCoordinateReindex_mem_iff R k N x.val).mpr x.property⟩
  invFun y := ⟨(primeCoordinateReindex R k).symm y.val,
    (primeCoordinateReindex_mem_iff R k N _).mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := Subtype.ext ((primeCoordinateReindex R k).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((primeCoordinateReindex R k).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((primeCoordinateReindex R k).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((primeCoordinateReindex R k).map_smul a x.val)

theorem primeCriticalArithmeticEquiv_apply (k N : ℕ) (x : primeCriticalCoordinates R k N)
    (m : SquarefreeDegree k) :
    (primeCriticalArithmeticEquiv R k N x).val m = x.val ((primeFaceSquarefreeEquiv k).symm m) := rfl

/-- An integer-labelled coefficient disappears when its doubled birth height is reached. -/
def squarefreeCriticalMap (k N M : ℕ) :
    squarefreeCriticalCoordinates R k N →ₗ[R] squarefreeCriticalCoordinates R k M :=
  (Finsupp.restrictDom R R (squarefreeCriticalLabels k M)).comp
    (Finsupp.supported R R (squarefreeCriticalLabels k N)).subtype

theorem squarefreeCriticalMap_apply (k N M : ℕ) (x : squarefreeCriticalCoordinates R k N)
    (m : SquarefreeDegree k) :
    (squarefreeCriticalMap R k N M x).val m =
      if m ∈ squarefreeCriticalLabels k M then x.val m else 0 :=
  Finsupp.filter_apply _ _ _

/-- Reindexing commutes with restriction to every target interval window. -/
theorem primeCriticalArithmeticEquiv_natural (k N M : ℕ) (x : primeCriticalCoordinates R k N) :
    primeCriticalArithmeticEquiv R k M (primeCriticalMap R k N M x) =
      squarefreeCriticalMap R k N M (primeCriticalArithmeticEquiv R k N x) := by
  apply Subtype.ext
  ext m
  rw [primeCriticalArithmeticEquiv_apply,primeCriticalMap_apply,
    squarefreeCriticalMap_apply,primeCriticalArithmeticEquiv_apply]
  have h := (primeFaceSquarefreeEquiv_critical k M ((primeFaceSquarefreeEquiv k).symm m)).symm
  rw [Equiv.apply_symm_apply] at h
  rw [h]

theorem squarefreeCriticalMap_refl (k N : ℕ) :
    squarefreeCriticalMap R k N N = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (primeCriticalArithmeticEquiv R k N).surjective x
  rw [← primeCriticalArithmeticEquiv_natural]
  exact congrArg (primeCriticalArithmeticEquiv R k N)
    (LinearMap.congr_fun (primeCriticalMap_refl R k N) y)

theorem squarefreeCriticalMap_comp (k : ℕ) {N M L : ℕ} (h : N ≤ M) (g : M ≤ L) :
    (squarefreeCriticalMap R k M L).comp (squarefreeCriticalMap R k N M) =
      squarefreeCriticalMap R k N L := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (primeCriticalArithmeticEquiv R k N).surjective x
  change squarefreeCriticalMap R k M L
    (squarefreeCriticalMap R k N M (primeCriticalArithmeticEquiv R k N y)) = _
  rw [← primeCriticalArithmeticEquiv_natural,← primeCriticalArithmeticEquiv_natural,
    ← primeCriticalArithmeticEquiv_natural]
  exact congrArg (primeCriticalArithmeticEquiv R k L)
    (LinearMap.congr_fun (primeCriticalMap_comp R k h g) y)

/-- The arithmetic interval functor in exterior degree `k`. -/
def squarefreeIntervalPersistence (k : ℕ) : ℕ ⥤ ModuleCat R where
  obj N := ModuleCat.of R (squarefreeCriticalCoordinates R k N)
  map {N M} _ := ModuleCat.ofHom (squarefreeCriticalMap R k N M)
  map_id N := ModuleCat.hom_ext (squarefreeCriticalMap_refl R k N)
  map_comp h g := ModuleCat.hom_ext (squarefreeCriticalMap_comp R k h.le g.le).symm

/-- Face-labelled and integer-labelled persistence have identical interval maps. -/
def primeCriticalArithmeticIso (k : ℕ) :
    primeCriticalPersistence R k ≅ squarefreeIntervalPersistence R k :=
  NatIso.ofComponents (fun N => (primeCriticalArithmeticEquiv R k N).toModuleIso)
    (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact primeCriticalArithmeticEquiv_natural R k _ _ x)

/-- Actual augmented homology is naturally the odd-squarefree interval system. -/
def primeHomologySquarefreeIntervalIso (k : ℕ) :
    primeCutoffHomology R (primeChainAugmentation R) k ≅ squarefreeIntervalPersistence R k :=
  primeHomologyCriticalIso R k ≪≫ primeCriticalArithmeticIso R k

#print axioms primeCriticalArithmeticEquiv_natural
#print axioms primeHomologySquarefreeIntervalIso
end GaloisForLFunctions.EffectiveScalingGeometry
