import GaloisForLFunctions.RHTower.PrimeProductCutoffContraction
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Augmented prime-product homology persistence

Exterior chains of prime product at most `N` form a subcomplex for every vertex
functional. Their literal inclusions define a functor of the height, and applying
homology gives the persistence module. Exterior degree zero is the empty face,
so the complex includes reduced topological degree minus one.
-/

noncomputable section
open CategoryTheory RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Deletion boundary restricted to the actual product-cutoff submodules. -/
def primeCutoffDifferential (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    primeChainCutoff R (k+1) N →ₗ[R] primeChainCutoff R k N :=
  (physicalKoszulDifferential k phi).restrict
    (fun _x hx => primeChainDifferential_cutoff R phi k N hx)

theorem primeCutoffDifferential_sq (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    (primeCutoffDifferential R phi k N).comp (primeCutoffDifferential R phi (k+1) N)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (physicalKoszulDifferential_sq k phi) x.val

/-- Augmented chains; exterior degree zero is topological degree minus one. -/
def primeCutoffComplex (phi : (Nat.Primes →₀ R) →ₗ[R] R) (N : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R (primeChainCutoff R k N))
    (fun k => ModuleCat.ofHom (primeCutoffDifferential R phi k N))
    (fun k => ModuleCat.hom_ext (primeCutoffDifferential_sq R phi k N))

theorem primeChainCutoff_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    primeChainCutoff R k N ≤ primeChainCutoff R k M := by
  apply Submodule.span_mono
  rintro x ⟨v,hv,rfl⟩
  exact ⟨v,hv.trans h,rfl⟩

/-- The persistence map is the inclusion of the same exterior chains. -/
def primeCutoffInclusion (phi : (Nat.Primes →₀ R) →ₗ[R] R) {N M : ℕ} (h : N ≤ M) :
    primeCutoffComplex R phi N ⟶ primeCutoffComplex R phi M :=
  ChainComplex.ofHom
    (fun k => ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R k h)))
    (fun k => by
      simp only [primeCutoffComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

theorem primeCutoffInclusion_refl (phi : (Nat.Primes →₀ R) →ₗ[R] R) (N : ℕ) :
    primeCutoffInclusion R phi (le_refl N)=𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  rfl

theorem primeCutoffInclusion_trans (phi : (Nat.Primes →₀ R) →ₗ[R] R)
    {N M L : ℕ} (h : N ≤ M) (g : M ≤ L) :
    primeCutoffInclusion R phi h ≫ primeCutoffInclusion R phi g =
      primeCutoffInclusion R phi (h.trans g) := by
  apply HomologicalComplex.Hom.ext
  funext k
  rfl

/-- Prime-product persistence, with coefficients given by an arbitrary vertex functional. -/
def primeCutoffPersistence (phi : (Nat.Primes →₀ R) →ₗ[R] R) :
    ℕ ⥤ ChainComplex (ModuleCat R) ℕ where
  obj N := primeCutoffComplex R phi N
  map h := primeCutoffInclusion R phi h.le
  map_id N := primeCutoffInclusion_refl R phi N
  map_comp h g := (primeCutoffInclusion_trans R phi h.le g.le).symm

/-- Actual homology persistence; degree zero retains the empty augmented face. -/
def primeCutoffHomology (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k : ℕ) : ℕ ⥤ ModuleCat R :=
  primeCutoffPersistence R phi ⋙
    HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k

#print axioms primeCutoffComplex
#print axioms primeCutoffInclusion_trans
#print axioms primeCutoffHomology
end GaloisForLFunctions.EffectiveScalingGeometry
