import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryTraceCorrection
import GaloisForLFunctions.HTGeometry.FiniteFreeDiscriminant

/-!
# The radical of the binary alternating trace form

For finite unramified binary algebras, the trace pairing identifies the
corrected radical with the kernel of `x ↦ x + Tr(x)·1`. Its radical is zero
in even dimension and the unit line in odd dimension. For finite fields this
gives nullity equal to degree modulo two and rank equal to degree rounded down
to even.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Module
section General
variable (L : Type*) [CommRing L] [Algebra (ZMod 2) L] [Module.Finite (ZMod 2) L]
    (hnd : (Algebra.traceForm (ZMod 2) L).Nondegenerate)
include hnd

omit [Module.Finite (ZMod 2) L] in
private theorem ker_binaryTraceForm_eq_ker_shear_of_nondegenerate :
    (binaryTraceForm L).ker = (binaryTraceShear L).ker := by
  ext x
  rw [binaryTraceForm_eq_trace_comp]
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hx
    apply hnd.1
    intro y
    exact congrArg (fun f : L →ₗ[ZMod 2] ZMod 2 => f y) hx
  · intro hx
    rw [hx, map_zero]

omit [Module.Finite (ZMod 2) L] in
private theorem mem_ker_binaryTraceForm_of_nondegenerate (x : L) :
    x ∈ (binaryTraceForm L).ker ↔ x = Algebra.trace (ZMod 2) L x • (1 : L) := by
  rw [ker_binaryTraceForm_eq_ker_shear_of_nondegenerate L hnd, LinearMap.mem_ker, binaryTraceShear_apply,
    add_eq_zero_iff_eq_neg, ← neg_smul, CharTwo.neg_eq]

private theorem ker_binaryTraceForm_even_of_nondegenerate (he : finrank (ZMod 2) L % 2 = 0) :
    (binaryTraceForm L).ker = ⊥ := by
  have hc : (finrank (ZMod 2) L : ZMod 2) = 0 := by
    apply ZMod.val_injective 2
    rw [ZMod.val_natCast]
    exact he
  have ht : Algebra.trace (ZMod 2) L 1 = 0 := (binary_trace_one L).trans hc
  apply bot_unique
  intro x hx
  have hxi := (mem_ker_binaryTraceForm_of_nondegenerate L hnd x).mp hx
  have htx : Algebra.trace (ZMod 2) L x = 0 := by
    have h := congrArg (Algebra.trace (ZMod 2) L) hxi
    simpa only [map_smul, ht, smul_zero] using h
  change x = 0
  exact hxi.trans (by rw [htx, zero_smul])

private theorem ker_binaryTraceForm_odd_of_nondegenerate (ho : finrank (ZMod 2) L % 2 = 1) :
    (binaryTraceForm L).ker = Submodule.span (ZMod 2) {(1 : L)} := by
  have hc : (finrank (ZMod 2) L : ZMod 2) = 1 := by
    apply ZMod.val_injective 2
    rw [ZMod.val_natCast]
    exact ho
  have ht : Algebra.trace (ZMod 2) L 1 = 1 := (binary_trace_one L).trans hc
  ext x
  rw [mem_ker_binaryTraceForm_of_nondegenerate L hnd, Submodule.mem_span_singleton]
  constructor
  · intro hx
    exact ⟨Algebra.trace (ZMod 2) L x, hx.symm⟩
  · rintro ⟨c, hc⟩
    rw [← hc, map_smul, ht, smul_eq_mul, mul_one]

private theorem ker_binaryTraceForm_of_nondegenerate :
    (binaryTraceForm L).ker =
      if finrank (ZMod 2) L % 2 = 0 then ⊥ else Submodule.span (ZMod 2) {(1 : L)} := by
  split_ifs with he
  · exact ker_binaryTraceForm_even_of_nondegenerate L hnd he
  · exact ker_binaryTraceForm_odd_of_nondegenerate L hnd (by omega)
end General

/-- For finite unramified binary algebras, the corrected radical is zero in even
dimension and exactly the unit line in odd dimension. -/
theorem ker_binaryTraceForm_formallyUnramified
    (A : Type*) [CommRing A] [Algebra (ZMod 2) A] [Module.Finite (ZMod 2) A]
    [Algebra.FormallyUnramified (ZMod 2) A] :
    (binaryTraceForm A).ker =
      if finrank (ZMod 2) A % 2 = 0 then ⊥ else Submodule.span (ZMod 2) {(1 : A)} :=
  ker_binaryTraceForm_of_nondegenerate A
    (Algebra.traceForm_nondegenerate_of_formallyUnramified_field (ZMod 2) A)

variable (L : Type*) [Field L] [Algebra (ZMod 2) L] [Module.Finite (ZMod 2) L]

/-- For finite extensions of the binary field, the corrected trace pairing is
nondegenerate exactly in even degree. -/
theorem binaryTraceForm_field_nondegenerate_iff :
    (binaryTraceForm L).Nondegenerate ↔ finrank (ZMod 2) L % 2 = 0 := by
  rw [binaryTraceForm_nondegenerate_iff]
  constructor
  · exact And.right
  · intro he
    exact ⟨traceForm_nondegenerate (ZMod 2) L, he⟩

/-- For finite binary fields, the corrected radical is the kernel of the trace shear. -/
theorem ker_binaryTraceForm_eq_ker_shear :
    (binaryTraceForm L).ker = (binaryTraceShear L).ker :=
  ker_binaryTraceForm_eq_ker_shear_of_nondegenerate L (traceForm_nondegenerate (ZMod 2) L)

/-- Every radical vector equals its trace times the unit. -/
theorem mem_ker_binaryTraceForm_iff (x : L) :
    x ∈ (binaryTraceForm L).ker ↔ x = Algebra.trace (ZMod 2) L x • (1 : L) :=
  mem_ker_binaryTraceForm_of_nondegenerate L (traceForm_nondegenerate (ZMod 2) L) x

/-- The corrected radical of a finite binary field is zero or the unit line
according to degree parity. -/
theorem ker_binaryTraceForm_field :
    (binaryTraceForm L).ker =
      if finrank (ZMod 2) L % 2 = 0 then ⊥ else Submodule.span (ZMod 2) {(1 : L)} :=
  ker_binaryTraceForm_of_nondegenerate L (traceForm_nondegenerate (ZMod 2) L)

/-- The radical dimension equals the extension degree modulo two. -/
theorem finrank_ker_binaryTraceForm_field :
    finrank (ZMod 2) (binaryTraceForm L).ker = finrank (ZMod 2) L % 2 := by
  by_cases he : finrank (ZMod 2) L % 2 = 0
  · rw [ker_binaryTraceForm_field, if_pos he, finrank_bot, he]
  · rw [ker_binaryTraceForm_field, if_neg he,
      finrank_span_singleton (one_ne_zero : (1 : L) ≠ 0)]
    omega

/-- The rank is the largest even integer at most the extension degree. -/
theorem finrank_range_binaryTraceForm_field :
    finrank (ZMod 2) (binaryTraceForm L).range =
      finrank (ZMod 2) L - finrank (ZMod 2) L % 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (binaryTraceForm L)
  rw [finrank_ker_binaryTraceForm_field] at h
  omega

#print axioms binaryTraceForm_field_nondegenerate_iff
#print axioms ker_binaryTraceForm_formallyUnramified
#print axioms ker_binaryTraceForm_field
#print axioms finrank_ker_binaryTraceForm_field
#print axioms finrank_range_binaryTraceForm_field
end GaloisForLFunctions.HTGeometry.LinearAlgebra
