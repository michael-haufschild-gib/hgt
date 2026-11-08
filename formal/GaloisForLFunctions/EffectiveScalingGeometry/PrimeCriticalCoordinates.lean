import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleCoordinates
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Surviving coordinates of prime-height persistence

Odd-face coordinates survive at height `N` exactly when their product `m`
satisfies `m ≤ N < 2m`. Projection onto these coordinates is split surjective;
its kernel is precisely the odd half-cutoff. The first isomorphism theorem
therefore identifies the quotient, over every commutative ring. Raising height
retains each coefficient until its two-cone appears. These maps form a functor,
and coordinate projection commutes with the actual odd-chain inclusions.
-/

noncomputable section
open scoped Classical
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Odd faces alive at height `N`, before their prime-two cones appear. -/
def primeCriticalFaces (k N : ℕ) : Set (Set.powersetCard Nat.Primes k) :=
  {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val ∧ N < 2 * primeFaceProduct s}

/-- Coefficients of the odd faces alive at this cutoff. -/
abbrev primeCriticalCoordinates (k N : ℕ) :=
  Finsupp.supported R R (primeCriticalFaces k N)

theorem primeOddCutoff_iff_repr_support (k N : ℕ) (x : PrimeChainSpace R k) :
    x ∈ primeOddCutoff R k N ↔
      (↑((primeChainBasis R k).repr x).support : Set (Set.powersetCard Nat.Primes k)) ⊆
        {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val} := by
  rw [primeOddCutoff_eq_span_basis, Module.Basis.mem_span_image]

/-- Discard exactly the odd coordinates whose two-cones already lie below `N`. -/
def primeCriticalProjection (k N : ℕ) :
    primeOddCutoff R k N →ₗ[R] primeCriticalCoordinates R k N := by
  classical
  exact (Finsupp.restrictDom R R (primeCriticalFaces k N)).comp
    ((primeChainBasis R k).repr.toLinearMap.comp (primeOddCutoff R k N).subtype)

/-- A surviving coefficient vector has its literal exterior-chain lift. -/
def primeCriticalLift (k N : ℕ) :
    primeCriticalCoordinates R k N →ₗ[R] primeOddCutoff R k N :=
  (((primeChainBasis R k).repr.symm.toLinearMap).comp
    (Finsupp.supported R R (primeCriticalFaces k N)).subtype).codRestrict _ (by
      intro x
      apply (primeOddCutoff_iff_repr_support R k N _).mpr
      change (↑((primeChainBasis R k).repr ((primeChainBasis R k).repr.symm x.val)).support :
        Set (Set.powersetCard Nat.Primes k)) ⊆ _
      rw [LinearEquiv.apply_symm_apply]
      intro s hs
      exact ⟨(x.property hs).1, (x.property hs).2.1⟩)

theorem primeCriticalProjection_lift (k N : ℕ) :
    (primeCriticalProjection R k N).comp (primeCriticalLift R k N) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Finsupp.filter (· ∈ primeCriticalFaces k N)
    ((primeChainBasis R k).repr ((primeChainBasis R k).repr.symm x.val)) = x.val
  rw [LinearEquiv.apply_symm_apply]
  exact (Finsupp.filter_eq_self_iff _ _).mpr
    (fun s hs => x.property (Finsupp.mem_support_iff.mpr hs))

theorem primeCriticalProjection_surjective (k N : ℕ) :
    Function.Surjective (primeCriticalProjection R k N) := by
  intro x
  exact ⟨primeCriticalLift R k N x, LinearMap.congr_fun (primeCriticalProjection_lift R k N) x⟩

/-- The discarded coordinates are exactly the odd half-cutoff submodule. -/
theorem primeCriticalProjection_ker (k N : ℕ) :
    (primeCriticalProjection R k N).ker =
      (primeOddCutoff R k (N/2)).comap (primeOddCutoff R k N).subtype := by
  classical
  ext x
  change primeCriticalProjection R k N x = 0 ↔ x.val ∈ primeOddCutoff R k (N/2)
  rw [primeOddCutoff_iff_repr_support]
  have hx := (primeOddCutoff_iff_repr_support R k N x.val).mp x.property
  constructor
  · intro h s hs
    have hz : ((primeChainBasis R k).repr x.val).filter (· ∈ primeCriticalFaces k N) = 0 :=
      congrArg Subtype.val h
    have hs' := hx hs
    refine ⟨?_,hs'.2⟩
    by_contra hn
    have hc : s ∈ primeCriticalFaces k N := ⟨hs'.1,hs'.2,by omega⟩
    exact (Finsupp.mem_support_iff.mp hs) ((Finsupp.filter_eq_zero_iff _ _).mp hz s hc)
  · intro h
    apply Subtype.ext
    change ((primeChainBasis R k).repr x.val).filter (· ∈ primeCriticalFaces k N) = 0
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro s hs
    by_contra hn
    have hl := (h (Finsupp.mem_support_iff.mpr hn)).1
    have hu := hs.2.2
    omega

local instance oddCutoffHasQuotient (k N : ℕ) :
    HasQuotient ↥(primeOddCutoff R k N) (Submodule R ↥(primeOddCutoff R k N)) :=
  @Submodule.hasQuotient R ↥(primeOddCutoff R k N) _ _ _

/-- The first isomorphism theorem for the surviving-coordinate projection. -/
def primeCriticalQuotientEquiv (k N : ℕ) :=
  @LinearMap.quotKerEquivOfSurjective R ↥(primeOddCutoff R k N)
    ↥(primeCriticalCoordinates R k N) (inferInstanceAs (Ring R))
    (primeOddCutoff R k N).addCommGroup
    (Finsupp.supported R R (primeCriticalFaces k N)).addCommGroup
    (primeOddCutoff R k N).module
    (Finsupp.supported R R (primeCriticalFaces k N)).module
    (primeCriticalProjection R k N) (primeCriticalProjection_surjective R k N)

/-- Raising the cutoff can only discard an already born odd coordinate. -/
theorem primeCriticalFilter_trans (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (f : Set.powersetCard Nat.Primes k →₀ R)
    (hf : ∀ s, f s ≠ 0 → primeFaceProduct s ≤ N) :
    (f.filter (· ∈ primeCriticalFaces k N)).filter (· ∈ primeCriticalFaces k M) =
      f.filter (· ∈ primeCriticalFaces k M) := by
  classical
  ext s
  by_cases hm : s ∈ primeCriticalFaces k M
  · rw [Finsupp.filter_apply_pos _ _ hm, Finsupp.filter_apply_pos _ _ hm]
    by_cases hn : s ∈ primeCriticalFaces k N
    · exact Finsupp.filter_apply_pos _ _ hn
    · rw [Finsupp.filter_apply_neg _ _ hn]
      by_contra hz
      exact hn ⟨hf s (Ne.symm hz), hm.2.1, lt_of_le_of_lt h hm.2.2⟩
  · rw [Finsupp.filter_apply_neg _ _ hm, Finsupp.filter_apply_neg _ _ hm]

/-- Persistence retains the same coefficient until its doubled birth height. -/
def primeCriticalMap (k N M : ℕ) :
    primeCriticalCoordinates R k N →ₗ[R] primeCriticalCoordinates R k M := by
  classical
  exact (Finsupp.restrictDom R R (primeCriticalFaces k M)).comp
    (Finsupp.supported R R (primeCriticalFaces k N)).subtype

/-- Every coefficient is retained exactly when its face is alive at the target. -/
theorem primeCriticalMap_apply (k N M : ℕ) (x : primeCriticalCoordinates R k N)
    (s : Set.powersetCard Nat.Primes k) :
    (primeCriticalMap R k N M x).val s =
      if s ∈ primeCriticalFaces k M then x.val s else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

theorem primeCriticalMap_refl (k N : ℕ) :
    primeCriticalMap R k N N = LinearMap.id := by
  classical
  exact Finsupp.restrictDom_comp_subtype _

theorem primeCriticalMap_comp (k : ℕ) {N M L : ℕ} (h : N ≤ M) (g : M ≤ L) :
    (primeCriticalMap R k M L).comp (primeCriticalMap R k N M) =
      primeCriticalMap R k N L := by
  classical
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact primeCriticalFilter_trans R k g x.val
    (fun s hs => ((x.property (Finsupp.mem_support_iff.mpr hs)).1).trans h)

theorem primeCriticalProjection_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeCriticalMap R k N M).comp (primeCriticalProjection R k N) =
      (primeCriticalProjection R k M).comp (Submodule.inclusion (primeOddCutoff_mono R k h)) := by
  classical
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact primeCriticalFilter_trans R k h ((primeChainBasis R k).repr x.val)
    (fun s hs => ((primeOddCutoff_iff_repr_support R k N x.val).mp x.property
      (Finsupp.mem_support_iff.mpr hs)).1)

open CategoryTheory
/-- The explicit interval-coordinate persistence functor. -/
def primeCriticalPersistence (k : ℕ) : ℕ ⥤ ModuleCat R where
  obj N := ModuleCat.of R (primeCriticalCoordinates R k N)
  map {N M} _ := ModuleCat.ofHom (primeCriticalMap R k N M)
  map_id N := ModuleCat.hom_ext (primeCriticalMap_refl R k N)
  map_comp h g := ModuleCat.hom_ext (primeCriticalMap_comp R k h.le g.le).symm

#print axioms primeCriticalProjection_natural
#print axioms primeCriticalPersistence

#print axioms primeCriticalProjection_ker
#print axioms primeCriticalQuotientEquiv
end GaloisForLFunctions.EffectiveScalingGeometry
