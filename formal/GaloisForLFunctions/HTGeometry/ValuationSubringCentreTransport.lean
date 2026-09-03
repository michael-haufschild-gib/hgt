import GaloisForLFunctions.HTGeometry.ValuationSubringDecompositionOrder

/-!
# Transport of valuation centres

A Galois automorphism carrying one valuation subring to another carries the corresponding centre
prime in an equivariant integral model to the other centre prime.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open scoped Pointwise

variable {S L F : Type*} [CommRing S] [IsDedekindDomain S]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable [Field F] [Algebra F L]
variable [MulSemiringAction (L ≃ₐ[F] L) S]

/-- Transporting a valuation subring transports its centre prime. -/
theorem smul_centerPrime_eq_of_smul_valuationSubring_eq
    (hact : ∀ (g : L ≃ₐ[F] L) (x : S), algebraMap S L (g • x) = g • algebraMap S L x)
    {W₁ W₂ : ValuationSubring L}
    (hSW₁ : ∀ x : S, algebraMap S L x ∈ W₁)
    (hSW₂ : ∀ x : S, algebraMap S L x ∈ W₂)
    (g : L ≃ₐ[F] L) (hg : g • W₁ = W₂) :
    g • centerPrime W₁ hSW₁ = centerPrime W₂ hSW₂ := by
  have forward {V₁ V₂ : ValuationSubring L}
      (hSV₁ : ∀ x : S, algebraMap S L x ∈ V₁)
      (hSV₂ : ∀ x : S, algebraMap S L x ∈ V₂)
      (a : L ≃ₐ[F] L) (ha : a • V₁ = V₂) :
      a • centerPrime V₁ hSV₁ ≤ centerPrime V₂ hSV₂ := by
    intro x hx
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [mem_centerPrime_iff, IsLocalRing.mem_maximalIdeal] at hx ⊢
    intro hunit
    apply hx
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hunit
    have hymem : (y : L) ∈ a • V₁ := by
      rw [ha]
      exact y.property
    rw [ValuationSubring.mem_smul_pointwise_iff_exists] at hymem
    obtain ⟨z, hz, hzy⟩ := hymem
    have haz : a⁻¹ • (y : L) = z := by
      rw [← hzy, inv_smul_smul]
    refine isUnit_iff_exists_inv.mpr ⟨⟨a⁻¹ • (y : L), haz ▸ hz⟩, ?_⟩
    apply Subtype.ext
    have hyval : algebraMap S L x * (y : L) = 1 := congrArg Subtype.val hy
    have hinv := congrArg (fun t : L => a⁻¹ • t) hyval
    show algebraMap S L (a⁻¹ • x) * (a⁻¹ • (y : L)) = 1
    rw [hact]
    simpa [smul_mul'] using hinv
  apply le_antisymm (forward hSW₁ hSW₂ g hg)
  rw [Ideal.subset_pointwise_smul_iff]
  apply forward hSW₂ hSW₁ g⁻¹
  calc
    g⁻¹ • W₂ = g⁻¹ • (g • W₁) := by rw [hg]
    _ = W₁ := inv_smul_smul g W₁

end
end ValuationInertia
end GaloisForLFunctions.HTGeometry
