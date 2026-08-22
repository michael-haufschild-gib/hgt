import GaloisForLFunctions.HTGeometry.ValuationSubringInertiaDictionary
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# A Galois element transports a valuation subring with its centre

`ValuationSubringInertiaDictionary` shows a valuation subring of a fraction field is the
localization of the ring at its centre.  Consequently the assignment `W ↦ centre W` is equivariant
and injective for the Galois action: an automorphism carrying one centre to another carries the
whole valuation subring along.

```text
smul_valuationSubring_eq_of_smul_centerPrime
    ** g • centre W₁ = centre W₂  ⟹  g • W₁ = W₂ **
```

Combined with mathlib's `Ideal.exists_smul_eq_of_isGaloisGroup` — transitivity of the Galois action
on the primes over a fixed prime — this gives transitivity of the Galois action on the valuation
subrings restricting to a fixed one, which mathlib does not carry: its ramification-group file
defines the decomposition and inertia subgroups and nothing else.

The proof is the fraction description on both sides: an element of `W₁` is `a/s` with `s` off the
centre, its image is `(g•a)/(g•s)`, and `g•s` is off the second centre exactly because `s` is off
the first.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing IsDedekindDomain
open scoped Pointwise

variable {S L : Type*} [CommRing S] [IsDedekindDomain S]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable {F : Type*} [Field F] [Algebra F L]
variable [MulSemiringAction (L ≃ₐ[F] L) S]
variable (hact : ∀ (g : L ≃ₐ[F] L) (x : S), algebraMap S L (g • x) = g • algebraMap S L x)

include hact

/-- **A Galois element carrying one centre to another carries the valuation subring along.** -/
theorem smul_valuationSubring_eq_of_smul_centerPrime
    {W₁ W₂ : ValuationSubring L} (hSW₁ : ∀ x : S, algebraMap S L x ∈ W₁)
    (hSW₂ : ∀ x : S, algebraMap S L x ∈ W₂) (hW₁ : W₁ ≠ ⊤) (hW₂ : W₂ ≠ ⊤)
    {g : L ≃ₐ[F] L} (hg : g • centerPrime W₁ hSW₁ = centerPrime W₂ hSW₂) :
    g • W₁ = W₂ := by
  have hnot : ∀ {s : S}, s ∉ centerPrime W₁ hSW₁ → g • s ∉ centerPrime W₂ hSW₂ := by
    intro s hs hmem
    rw [← hg] at hmem
    have hs' := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hmem
    rw [inv_smul_smul] at hs'
    exact hs hs'
  have hstep : ∀ y ∈ W₁, g • y ∈ W₂ := by
    intro y hy
    obtain ⟨a, s, hs, rfl⟩ := (mem_iff_exists_div W₁ hSW₁ hW₁ y).mp hy
    have hnum : g • algebraMap S L a = algebraMap S L (g • a) := (hact g a).symm
    have hden : g • algebraMap S L s = algebraMap S L (g • s) := (hact g s).symm
    have hdiv : g • (algebraMap S L a / algebraMap S L s)
        = algebraMap S L (g • a) / algebraMap S L (g • s) := by
      rw [← hnum, ← hden]
      exact map_div₀ (g : L ≃+* L) _ _
    rw [hdiv]
    exact (mem_iff_exists_div W₂ hSW₂ hW₂ _).mpr ⟨g • a, g • s, hnot hs, rfl⟩
  have hnot' : ∀ {s : S}, s ∉ centerPrime W₂ hSW₂ → g⁻¹ • s ∉ centerPrime W₁ hSW₁ := by
    intro s hs hmem
    refine hs ?_
    rw [← hg]
    exact (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mpr hmem
  have hstep' : ∀ y ∈ W₂, g⁻¹ • y ∈ W₁ := by
    intro y hy
    obtain ⟨a, s, hs, rfl⟩ := (mem_iff_exists_div W₂ hSW₂ hW₂ y).mp hy
    have hnum : g⁻¹ • algebraMap S L a = algebraMap S L (g⁻¹ • a) := (hact g⁻¹ a).symm
    have hden : g⁻¹ • algebraMap S L s = algebraMap S L (g⁻¹ • s) := (hact g⁻¹ s).symm
    have hdiv : g⁻¹ • (algebraMap S L a / algebraMap S L s)
        = algebraMap S L (g⁻¹ • a) / algebraMap S L (g⁻¹ • s) := by
      rw [← hnum, ← hden]
      exact map_div₀ ((g⁻¹ : L ≃ₐ[F] L) : L ≃+* L) _ _
    rw [hdiv]
    exact (mem_iff_exists_div W₁ hSW₁ hW₁ _).mpr ⟨g⁻¹ • a, g⁻¹ • s, hnot' hs, rfl⟩
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hstep a ha
  · intro hx
    exact ⟨g⁻¹ • x, hstep' x hx, by simp⟩

end

end ValuationInertia
end GaloisForLFunctions.HTGeometry
