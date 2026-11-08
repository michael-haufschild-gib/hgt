import GaloisForLFunctions.RHTower.PrimeProductCutoffContraction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Face coordinates for prime-product cutoffs

The exterior-chain basis is indexed by increasing finite prime supports.
Sorting an injective prime tuple changes only its sign and preserves its
product; a repeated prime makes the atom zero. Thus the tuple-defined cutoff
is exactly the span of the bounded basis faces, over every commutative ring.
Equivalently, cutoff membership is the support condition on face coefficients.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
/-- Prime labels use their inherited numerical order. -/
abbrev primeLabelLinearOrder : LinearOrder Nat.Primes :=
  inferInstanceAs (LinearOrder {p : ℕ // p.Prime})

attribute [local instance] primeLabelLinearOrder

variable (R : Type*) [CommRing R]

/-- Increasing prime supports index the exterior-chain basis. -/
def primeChainBasis (k : ℕ) :
    Module.Basis (Set.powersetCard Nat.Primes k) R (PrimeChainSpace R k) :=
  (Finsupp.basisSingleOne (R := R) (ι := Nat.Primes)).exteriorPower k

def primeFaceProduct {k : ℕ} (s : Set.powersetCard Nat.Primes k) : ℕ :=
  ∏ p ∈ s.val, (p : ℕ)

theorem primeChainBasis_eq_atom {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    primeChainBasis R k s = primeChainAtom R (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  rw [primeChainBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    Finsupp.coe_basisSingleOne]
  rfl

theorem primeFaceProduct_eq_prod_enum {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    primeFaceProduct s = ∏ i, (Set.powersetCard.ofFinEmbEquiv.symm s i : ℕ) := by
  symm
  unfold primeFaceProduct
  refine Finset.prod_bij (fun i _ => Set.powersetCard.ofFinEmbEquiv.symm s i) ?_ ?_ ?_ ?_
  · intro i _
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i,rfl⟩
  · intro i _ j _ hij
    exact (Set.powersetCard.ofFinEmbEquiv.symm s).injective hij
  · intro p hp
    obtain ⟨i,rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s p).mpr hp
    exact ⟨i,mem_univ _,rfl⟩
  · intro i _
    rfl

theorem primeChainBasis_mem_cutoff {k N : ℕ} (s : Set.powersetCard Nat.Primes k)
    (hs : primeFaceProduct s ≤ N) : primeChainBasis R k s ∈ primeChainCutoff R k N := by
  rw [primeChainBasis_eq_atom]
  exact Submodule.subset_span ⟨_, (primeFaceProduct_eq_prod_enum s) ▸ hs, rfl⟩

/-- Sorting preserves the prime product; repeated prime vertices vanish. -/
theorem primeChainAtom_mem_boundedBasis {k N : ℕ} (v : Fin k → Nat.Primes)
    (hv : (∏ i, (v i : ℕ)) ≤ N) :
    primeChainAtom R v ∈ Submodule.span R
      (primeChainBasis R k '' {s | primeFaceProduct s ≤ N}) := by
  classical
  by_cases hinj : Function.Injective v
  · have hcard : (Finset.univ.image v).card = k :=
      (Finset.card_image_of_injective Finset.univ hinj).trans (Finset.card_fin k)
    let s : Set.powersetCard Nat.Primes k := ⟨Finset.univ.image v, hcard⟩
    have hs : primeFaceProduct s ≤ N := by
      unfold primeFaceProduct
      change (∏ p ∈ Finset.univ.image v, (p : ℕ)) ≤ N
      rw [Finset.prod_image]
      · exact hv
      · intro i _ j _ hij
        exact hinj hij
    let σ : Equiv.Perm (Fin k) :=
      (Finset.orderIsoOfFin (Finset.univ.image v) hcard).toEquiv.trans
        ((Equiv.setCongr Fintype.coe_image_univ).trans (Equiv.ofInjective v hinj).symm)
    have hsort : v ∘ σ = Set.powersetCard.ofFinEmbEquiv.symm s := by
      funext i
      simp only [σ, Equiv.trans_apply, Function.comp_apply]
      simp only [Equiv.apply_ofInjective_symm]
      rfl
    have hmem : primeChainAtom R (v ∘ σ) ∈ Submodule.span R
        (primeChainBasis R k '' {s | primeFaceProduct s ≤ N}) := by
      rw [hsort, ← primeChainBasis_eq_atom]
      exact Submodule.subset_span ⟨s, hs, rfl⟩
    change exteriorPower.ιMulti R k ((fun i => Finsupp.single (v i) (1 : R)) ∘ σ) ∈ _ at hmem
    rw [AlternatingMap.map_perm] at hmem
    refine (Submodule.smul_mem_iff_of_isUnit _ (r := (σ.sign : R)) ?_).mp hmem
    rw [isUnit_iff_exists_inv]
    refine ⟨(σ.sign : R), ?_⟩
    norm_cast
    simp only [Int.units_mul_self, Units.val_one, Int.cast_one]
  · have hz : primeChainAtom R v = 0 := by
      apply AlternatingMap.map_eq_zero_of_not_injective
      intro h
      exact hinj (fun i j hij => h (congrArg (fun p => Finsupp.single p (1 : R)) hij))
    rw [hz]
    exact Submodule.zero_mem _

/-- The tuple-defined cutoff is exactly the coordinate submodule of bounded faces. -/
theorem primeChainCutoff_eq_span_basis (k N : ℕ) :
    primeChainCutoff R k N = Submodule.span R
      (primeChainBasis R k '' {s | primeFaceProduct s ≤ N}) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨v, hv, rfl⟩
    exact primeChainAtom_mem_boundedBasis R v hv
  · apply Submodule.span_le.mpr
    rintro x ⟨s, hs, rfl⟩
    exact primeChainBasis_mem_cutoff R s hs

/-- A chain lies below the cutoff exactly when every nonzero face coefficient does. -/
theorem primeChainCutoff_iff_repr_support (k N : ℕ) (x : PrimeChainSpace R k) :
    x ∈ primeChainCutoff R k N ↔
      (↑((primeChainBasis R k).repr x).support : Set (Set.powersetCard Nat.Primes k)) ⊆
        {s | primeFaceProduct s ≤ N} := by
  rw [primeChainCutoff_eq_span_basis, Module.Basis.mem_span_image]

#print axioms primeChainCutoff_eq_span_basis
#print axioms primeChainCutoff_iff_repr_support
end GaloisForLFunctions.EffectiveScalingGeometry
