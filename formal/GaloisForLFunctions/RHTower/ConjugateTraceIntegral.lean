/-
# Conjugate sums of integer polynomials are rational integers

Let `x ∈ ℂ` be integral over `ℤ` and let `h ∈ ℤ[X]`.  The sum of `h` evaluated over the full
conjugate orbit of `x` — the multiset of complex roots of the minimal polynomial `minpoly ℚ x` — is
a rational integer:
`∑_{r ∈ (minpoly ℚ x).aroots ℂ} h(r) ∈ ℤ`.

The mechanism is the field trace.  Writing `y = h(x) ∈ ℚ(x)`, the trace `Tr_{ℚ(x)/ℚ}(y)` equals the
sum of `σ(y)` over the `ℚ`-embeddings `σ : ℚ(x) → ℂ`, and each `σ` sends the generator to a distinct
root of `minpoly ℚ x`, so `σ(y) = h(σ(gen))` runs exactly over `h(r)` as `r` runs over the roots
(separability makes the root multiset squarefree, matching the embedding count).  Since `x` is an
algebraic integer, so is `y = h(x)`, hence so is its trace; a rational algebraic integer lies in `ℤ`.

This is the symmetric-function integrality tool underlying transcendence arguments over number
fields: it turns a sum ranging over a Galois orbit of algebraic numbers into a single honest integer,
the invariant needed to run the Hermite–Lindemann factorial estimate at a general algebraic exponent
rather than only at rational points.
-/
import Mathlib

open Polynomial Algebra IntermediateField
open scoped Classical

namespace GaloisForLFunctions
namespace RHTower

/-- **Conjugate-orbit sums are integers.**  For `x` integral over `ℤ` and `h ∈ ℤ[X]`, the sum of
`aeval r h` over the roots `r` of `minpoly ℚ x` is a rational integer.  It equals the field trace
`Tr_{ℚ(x)/ℚ}(h(x))`, an algebraic integer that is rational, hence an element of `ℤ`. -/
theorem sum_aroots_aeval_isInt {x : ℂ} (hx : IsIntegral ℤ x) (h : ℤ[X]) :
    ∃ m : ℤ, (((minpoly ℚ x).aroots ℂ).map (fun r => aeval r h)).sum = (m : ℂ) := by
  have hxQ : IsIntegral ℚ x := hx.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hxQ
  haveI : Algebra.IsSeparable ℚ ℚ⟮x⟯ := Algebra.IsSeparable.of_integral _ _
  have hinj : Function.Injective (algebraMap ℚ⟮x⟯ ℂ) := FaithfulSMul.algebraMap_injective _ _
  have hgenZ : IsIntegral ℤ (AdjoinSimple.gen ℚ x) := by
    have hx' : IsIntegral ℤ (algebraMap ℚ⟮x⟯ ℂ (AdjoinSimple.gen ℚ x)) := by
      rwa [AdjoinSimple.algebraMap_gen]
    exact (isIntegral_algebraMap_iff hinj).mp hx'
  set y : ℚ⟮x⟯ := aeval (AdjoinSimple.gen ℚ x) h with hy
  have hyZ : IsIntegral ℤ y :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin ℤ {AdjoinSimple.gen ℚ x})
      hgenZ.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton ℤ _)
  have htr : IsIntegral ℤ (Algebra.trace ℚ ℚ⟮x⟯ y) := Algebra.isIntegral_trace hyZ
  rw [IsIntegrallyClosed.isIntegral_iff] at htr
  obtain ⟨m, hm⟩ := htr
  refine ⟨m, ?_⟩
  set pb := IntermediateField.adjoin.powerBasis hxQ with hpb
  have hgen : pb.gen = AdjoinSimple.gen ℚ x := IntermediateField.adjoin.powerBasis_gen hxQ
  have hmp : minpoly ℚ pb.gen = minpoly ℚ x := by rw [hgen]; exact IntermediateField.minpoly_gen ℚ x
  have hnodup : ((minpoly ℚ pb.gen).aroots ℂ).Nodup :=
    nodup_roots ((separable_map _).mpr (Algebra.IsSeparable.isSeparable ℚ pb.gen))
  have inner : ∀ σ : ℚ⟮x⟯ →ₐ[ℚ] ℂ, (pb.liftEquiv' σ : ℂ) = σ (AdjoinSimple.gen ℚ x) :=
    fun σ => (pb.liftEquiv'_apply_coe σ).trans (congrArg (⇑σ) hgen)
  have hemb := trace_eq_sum_embeddings (K := ℚ) (L := ℚ⟮x⟯) ℂ (x := y)
  have hσ : ∀ σ : ℚ⟮x⟯ →ₐ[ℚ] ℂ, σ y = aeval (σ (AdjoinSimple.gen ℚ x)) h :=
    fun σ => by rw [hy]; exact (aeval_algHom_apply (σ.restrictScalars ℤ) _ h).symm
  have step1 : (∑ σ : ℚ⟮x⟯ →ₐ[ℚ] ℂ, aeval (σ (AdjoinSimple.gen ℚ x)) h)
      = ∑ r : {r // r ∈ (minpoly ℚ pb.gen).aroots ℂ}, aeval (r : ℂ) h :=
    Fintype.sum_equiv pb.liftEquiv' _ _ (fun σ => by rw [inner σ])
  have step2 : (∑ r : {r // r ∈ (minpoly ℚ pb.gen).aroots ℂ}, aeval (r : ℂ) h)
      = ∑ r ∈ ((minpoly ℚ pb.gen).aroots ℂ).toFinset, aeval r h :=
    Finset.sum_mem_multiset _ _ _ (fun _ => rfl)
  have hconv : (∑ σ : ℚ⟮x⟯ →ₐ[ℚ] ℂ, σ y)
      = (((minpoly ℚ x).aroots ℂ).map (fun r => aeval r h)).sum := by
    simp_rw [hσ, step1, step2, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup, hmp]
  rw [← hconv, ← hemb, ← hm]
  simp

end RHTower
end GaloisForLFunctions
