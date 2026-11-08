import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedSquarefreeIndices
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedAugmentedHomology
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeArithmeticPersistence

/-!
# Arithmetic classification of integral prime-weighted persistence

Actual augmented homology is naturally the pair of free coefficients on odd
squarefree labels `m ≤ N < 2m` and parity coefficients on squarefree labels
coprime to six with `2m ≤ N < 3m`. Exterior degree is the number of distinct
prime factors. Raising height retains free coefficients in the new free
window and restricts reduced old free coefficients plus old parity coefficients
to the new torsion window. Reindexing preserves every coefficient and map.
-/

noncomputable section
open scoped Classical
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- Squarefree integer labels for the free and parity parts of weighted homology. -/
abbrev squarefreeValueCoordinates (k N : ℕ) :=
  squarefreeCriticalCoordinates ℤ k N × squarefreeTorsionCoordinates k N

/-- Reindex both coefficient types by the same prime-support product. -/
def primeValueArithmeticEquiv (k N : ℕ) :
    primeValueCoordinates k N ≃ₗ[ℤ] squarefreeValueCoordinates k N :=
  (primeCriticalArithmeticEquiv ℤ k N).prodCongr (primeTorsionArithmeticEquiv k N)

theorem primeValueArithmeticEquiv_free (k N : ℕ) (x : primeValueCoordinates k N)
    (m : SquarefreeDegree k) :
    (primeValueArithmeticEquiv k N x).1.val m = x.1.val ((primeFaceSquarefreeEquiv k).symm m) := rfl

theorem primeValueArithmeticEquiv_torsion (k N : ℕ) (x : primeValueCoordinates k N)
    (m : SquarefreeDegree k) :
    (primeValueArithmeticEquiv k N x).2.val m = x.2.val ((primeFaceSquarefreeEquiv k).symm m) := rfl

/-- Arithmetic height maps transported through the canonical squarefree labels. -/
def squarefreeValueMap (k N M : ℕ) :
    squarefreeValueCoordinates k N →ₗ[ℤ] squarefreeValueCoordinates k M :=
  (primeValueArithmeticEquiv k M).toLinearMap.comp
    ((primeValueCoordinateMap k N M).comp (primeValueArithmeticEquiv k N).symm.toLinearMap)

theorem primeValueArithmeticEquiv_natural (k N M : ℕ) (x : primeValueCoordinates k N) :
    primeValueArithmeticEquiv k M (primeValueCoordinateMap k N M x) =
      squarefreeValueMap k N M (primeValueArithmeticEquiv k N x) := by
  change _ = primeValueArithmeticEquiv k M
    (primeValueCoordinateMap k N M ((primeValueArithmeticEquiv k N).symm (primeValueArithmeticEquiv k N x)))
  rw [LinearEquiv.symm_apply_apply]

/-- A free arithmetic coefficient survives until twice its birth height. -/
theorem squarefreeValueMap_free (k N M : ℕ) (x : squarefreeValueCoordinates k N)
    (m : SquarefreeDegree k) :
    (squarefreeValueMap k N M x).1.val m =
      if m ∈ squarefreeCriticalLabels k M then x.1.val m else 0 := by
  obtain ⟨y,rfl⟩ := (primeValueArithmeticEquiv k N).surjective x
  rw [← primeValueArithmeticEquiv_natural,primeValueArithmeticEquiv_free,
    primeValueCoordinateMap_free,primeCriticalMap_apply,primeValueArithmeticEquiv_free]
  have h := (primeFaceSquarefreeEquiv_critical k M ((primeFaceSquarefreeEquiv k).symm m)).symm
  rw [Equiv.apply_symm_apply] at h
  rw [h]

/-- At a torsion window, old free coefficients reduce modulo two and old parity coefficients persist. -/
theorem squarefreeValueMap_torsion (k N M : ℕ) (x : squarefreeValueCoordinates k N)
    (m : SquarefreeDegree k) :
    (squarefreeValueMap k N M x).2.val m =
      if m ∈ squarefreeTorsionLabels k M then (x.1.val m : ZMod 2)+x.2.val m else 0 := by
  obtain ⟨y,rfl⟩ := (primeValueArithmeticEquiv k N).surjective x
  rw [← primeValueArithmeticEquiv_natural,primeValueArithmeticEquiv_torsion,
    primeValueCoordinateMap_torsion,primeValueArithmeticEquiv_free,primeValueArithmeticEquiv_torsion]
  have h := (primeFaceSquarefreeEquiv_torsion k M ((primeFaceSquarefreeEquiv k).symm m)).symm
  rw [Equiv.apply_symm_apply] at h
  rw [h]

theorem squarefreeValueMap_refl (k N : ℕ) : squarefreeValueMap k N N = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (primeValueArithmeticEquiv k N).surjective x
  rw [← primeValueArithmeticEquiv_natural]
  exact congrArg (primeValueArithmeticEquiv k N)
    (LinearMap.congr_fun (primeValueCoordinateMap_refl k N) y)

theorem squarefreeValueMap_comp (k : ℕ) {N M L : ℕ} (h : N ≤ M) (g : M ≤ L) :
    (squarefreeValueMap k M L).comp (squarefreeValueMap k N M) = squarefreeValueMap k N L := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (primeValueArithmeticEquiv k N).surjective x
  change squarefreeValueMap k M L (squarefreeValueMap k N M (primeValueArithmeticEquiv k N y)) = _
  rw [← primeValueArithmeticEquiv_natural,← primeValueArithmeticEquiv_natural,
    ← primeValueArithmeticEquiv_natural]
  exact congrArg (primeValueArithmeticEquiv k L)
    (LinearMap.congr_fun (primeValueCoordinateMap_comp k h g) y)

/-- Integral weighted arithmetic persistence with free-to-parity transitions. -/
def squarefreeValuePersistence (k : ℕ) : ℕ ⥤ ModuleCat ℤ where
  obj N := ModuleCat.of ℤ (squarefreeValueCoordinates k N)
  map {N M} _ := ModuleCat.ofHom (squarefreeValueMap k N M)
  map_id N := ModuleCat.hom_ext (squarefreeValueMap_refl k N)
  map_comp h g := ModuleCat.hom_ext (squarefreeValueMap_comp k h.le g.le).symm

def primeValueArithmeticIso (k : ℕ) :
    primeValueCoordinatePersistence k ≅ squarefreeValuePersistence k :=
  NatIso.ofComponents (fun N => (primeValueArithmeticEquiv k N).toModuleIso)
    (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact primeValueArithmeticEquiv_natural k _ _ x)

/-- Actual augmented integral prime-weighted homology is the explicit arithmetic persistence functor. -/
def primeValueHomologyArithmeticIso (k : ℕ) :
    primeCutoffHomology ℤ (primeValueFunctional ℤ) k ≅ squarefreeValuePersistence k :=
  primeValueHomologyCoordinateIso k ≪≫ primeValueArithmeticIso k

#print axioms squarefreeValueMap_free
#print axioms squarefreeValueMap_torsion
#print axioms primeValueHomologyArithmeticIso
end GaloisForLFunctions.EffectiveScalingGeometry
