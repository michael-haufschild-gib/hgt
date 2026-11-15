import GaloisForLFunctions.HTGeometry.Homology.SquareZeroCyclicExterior
import GaloisForLFunctions.HTGeometry.Homology.ProductCyclicOne
import GaloisForLFunctions.HTGeometry.DirectionalKaehlerWedge
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeHochschild
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Complete exterior classification of the Steinberg cyclic quotient

The native Steinberg algebra is the product of its ordinary and signed prime
square-zero sectors. Its full ordinary cyclic degree one is therefore the
product of two exterior prime-pair spaces. The standard exterior bases give a
complete basis of actual cyclic classes, with explicit tangent representatives.
A two-tensor vanishes exactly when its two prime-moment pairs are dependent.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.SquareZeroCyclic
open PositiveSteinbergCyclic

/-- Both sign sectors of the full ordinary cyclic homology are exterior prime-pair spaces. -/
def deningerCyclicPrimeExteriorEquiv : CyclicOne Quotient ≃ₗ[ℂ]
    (⋀[ℂ]^2 DeningerPrimeSpace) × (⋀[ℂ]^2 DeningerPrimeSpace) :=
  ((cyclicOneEquiv deningerSteinbergPrimeEquiv).trans
    (cyclicOneProductEquiv (A := DeningerPrimeJet) (B := DeningerPrimeJet))).trans
      ((squareZeroCyclicEquiv (V := DeningerPrimeSpace)).prodCongr
        (squareZeroCyclicEquiv (V := DeningerPrimeSpace)))

/-- An actual two-tensor is classified by its ordinary and signed exterior prime moments. -/
theorem deningerCyclicPrimeExteriorEquiv_class (a b : Quotient) :
    deningerCyclicPrimeExteriorEquiv (cyclicClass a b) =
      (tangentWedge (deningerQuotientPrimeMoment a) (deningerQuotientPrimeMoment b),
       tangentWedge (deningerQuotientSignedPrimeMoment a) (deningerQuotientSignedPrimeMoment b)) := by
  simp only [deningerCyclicPrimeExteriorEquiv, LinearEquiv.trans_apply,
    cyclicOneEquiv_class, cyclicOneProductEquiv_class, LinearEquiv.prodCongr_apply,
    squareZeroCyclicEquiv_class]
  rfl

/-- A two-tensor is a cyclic relation exactly when both prime-moment pairs are dependent. -/
theorem deningerCyclicClass_eq_zero_iff (a b : Quotient) :
    cyclicClass a b = 0 ↔
      (¬ LinearIndependent ℂ ![deningerQuotientPrimeMoment a, deningerQuotientPrimeMoment b]) ∧
      (¬ LinearIndependent ℂ
        ![deningerQuotientSignedPrimeMoment a, deningerQuotientSignedPrimeMoment b]) := by
  constructor
  · intro h
    have he := congrArg deningerCyclicPrimeExteriorEquiv h
    rw [deningerCyclicPrimeExteriorEquiv_class, map_zero] at he
    exact ⟨(GaloisForLFunctions.HTGeometry.exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent
      (K := ℂ) (M := DeningerPrimeSpace)
      ![deningerQuotientPrimeMoment a, deningerQuotientPrimeMoment b]).mp (congrArg Prod.fst he),
      (GaloisForLFunctions.HTGeometry.exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent
      (K := ℂ) (M := DeningerPrimeSpace)
      ![deningerQuotientSignedPrimeMoment a, deningerQuotientSignedPrimeMoment b]).mp
        (congrArg Prod.snd he)⟩
  · rintro ⟨h₁, h₂⟩
    apply deningerCyclicPrimeExteriorEquiv.injective
    rw [deningerCyclicPrimeExteriorEquiv_class, map_zero]
    apply Prod.ext
    · exact (GaloisForLFunctions.HTGeometry.exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent
        (K := ℂ) (M := DeningerPrimeSpace) _).mpr h₁
    · exact (GaloisForLFunctions.HTGeometry.exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent
        (K := ℂ) (M := DeningerPrimeSpace) _).mpr h₂

/-- Prime labels carry the numerical order inherited from the natural numbers. -/
local instance deningerPrimeOrder : LinearOrder Nat.Primes :=
  inferInstanceAs (LinearOrder {p : ℕ // Nat.Prime p})

/-- Unordered pairs of distinct prime labels. -/
abbrev DeningerCyclicPrimePair := Set.powersetCard Nat.Primes 2

/-- The standard prime-pair basis in the second exterior power of the prime moment space. -/
def deningerPrimeExteriorBasis : Module.Basis DeningerCyclicPrimePair ℂ (⋀[ℂ]^2 DeningerPrimeSpace) :=
  (Finsupp.basisSingleOne : Module.Basis Nat.Primes ℂ DeningerPrimeSpace).exteriorPower 2

/-- The two coordinate vectors belonging to the increasing enumeration of a prime pair. -/
def deningerPrimePairVector (s : DeningerCyclicPrimePair) (i : Fin 2) : DeningerPrimeSpace :=
  Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s i) 1

/-- A prime-pair basis vector is the exterior product of its two ordered coordinates. -/
theorem deningerPrimeExteriorBasis_wedge (s : DeningerCyclicPrimePair) :
    deningerPrimeExteriorBasis s = tangentWedge (deningerPrimePairVector s 0)
      (deningerPrimePairVector s 1) := by
  rw [deningerPrimeExteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  change exteriorPower.ιMulti ℂ 2 (fun i => deningerPrimePairVector s i) = _
  unfold tangentWedge
  congr 1
  funext i; fin_cases i <;> rfl

/-- A complete basis of actual cyclic homology: one copy of prime pairs in each sign sector. -/
def deningerCyclicBasis : Module.Basis (DeningerCyclicPrimePair ⊕ DeningerCyclicPrimePair)
    ℂ (CyclicOne Quotient) :=
  (deningerPrimeExteriorBasis.prod deningerPrimeExteriorBasis).map
    deningerCyclicPrimeExteriorEquiv.symm

@[simp] theorem deningerCyclicBasis_inl_coordinates (s : DeningerCyclicPrimePair) :
    deningerCyclicPrimeExteriorEquiv (deningerCyclicBasis (Sum.inl s)) =
      (deningerPrimeExteriorBasis s, 0) := by
  rw [deningerCyclicBasis, Module.Basis.map_apply,
    deningerCyclicPrimeExteriorEquiv.apply_symm_apply]
  apply Prod.ext
  · exact Module.Basis.prod_apply_inl_fst _ _ _
  · exact Module.Basis.prod_apply_inl_snd _ _ _

@[simp] theorem deningerCyclicBasis_inr_coordinates (s : DeningerCyclicPrimePair) :
    deningerCyclicPrimeExteriorEquiv (deningerCyclicBasis (Sum.inr s)) =
      (0, deningerPrimeExteriorBasis s) := by
  rw [deningerCyclicBasis, Module.Basis.map_apply,
    deningerCyclicPrimeExteriorEquiv.apply_symm_apply]
  apply Prod.ext
  · exact Module.Basis.prod_apply_inr_fst _ _ _
  · exact Module.Basis.prod_apply_inr_snd _ _ _

/-- Ordinary-sector basis vectors have explicit pure-tangent tensor representatives. -/
theorem deningerCyclicBasis_inl_class (s : DeningerCyclicPrimePair) :
    deningerCyclicBasis (Sum.inl s) =
      cyclicClass (deningerPairedPrimeTangent (deningerPrimePairVector s 0, 0))
        (deningerPairedPrimeTangent (deningerPrimePairVector s 1, 0)) := by
  apply deningerCyclicPrimeExteriorEquiv.injective
  rw [deningerCyclicBasis_inl_coordinates, deningerCyclicPrimeExteriorEquiv_class]
  simp only [deningerQuotientPrimeMoment_paired, deningerQuotientSignedPrimeMoment_paired,
    tangentWedge_zero_left, deningerPrimeExteriorBasis_wedge]

/-- Signed-sector basis vectors have explicit pure-tangent tensor representatives. -/
theorem deningerCyclicBasis_inr_class (s : DeningerCyclicPrimePair) :
    deningerCyclicBasis (Sum.inr s) =
      cyclicClass (deningerPairedPrimeTangent (0, deningerPrimePairVector s 0))
        (deningerPairedPrimeTangent (0, deningerPrimePairVector s 1)) := by
  apply deningerCyclicPrimeExteriorEquiv.injective
  rw [deningerCyclicBasis_inr_coordinates, deningerCyclicPrimeExteriorEquiv_class]
  simp only [deningerQuotientPrimeMoment_paired, deningerQuotientSignedPrimeMoment_paired,
    tangentWedge_zero_left, deningerPrimeExteriorBasis_wedge]

/-- These prime-pair classes are independent across both sign sectors. -/
theorem deningerCyclicBasis_linearIndependent : LinearIndependent ℂ deningerCyclicBasis := by
  generalize deningerCyclicBasis = b
  exact b.linearIndependent

/-- Every cyclic class is a finite linear combination of the prime-pair classes. -/
theorem deningerCyclicBasis_span :
    Submodule.span ℂ (Set.range deningerCyclicBasis) = ⊤ := by
  generalize deningerCyclicBasis = b
  exact b.span_eq

#print axioms deningerCyclicPrimeExteriorEquiv
#print axioms deningerCyclicClass_eq_zero_iff
#print axioms deningerCyclicBasis
#print axioms deningerCyclicBasis_inl_class
#print axioms deningerCyclicBasis_inr_class
#print axioms deningerCyclicBasis_linearIndependent
#print axioms deningerCyclicBasis_span
end RHTower
