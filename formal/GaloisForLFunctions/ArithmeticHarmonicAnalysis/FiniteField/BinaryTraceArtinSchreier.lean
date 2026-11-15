import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.BinaryArtinSchreier
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryTraceRadical
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ArtinSchreierIrreducibility

/-!
# Trace obstructions for binary Artin–Schreier equations

Over a finite binary field, the image of `x ↦ x² + x` is exactly the trace-zero
hyperplane. The native Artin–Schreier polynomial therefore has a root at
trace-zero constants and is irreducible at trace-one constants. The trace
shear is an involution in even degree and projects onto this image in odd
degree. Products of finite fields have componentwise trace obstructions.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Module
open GaloisForLFunctions.HTGeometry.LinearAlgebra

variable (L : Type*) [Field L] [Algebra (ZMod 2) L]

variable [Module.Finite (ZMod 2) L]

/-- The image of the binary Artin–Schreier operator is exactly the trace-zero hyperplane. -/
theorem range_binaryArtinSchreier :
    (binaryArtinSchreier L).range = (Algebra.trace (ZMod 2) L).ker := by
  have hle : (binaryArtinSchreier L).range ≤ (Algebra.trace (ZMod 2) L).ker := by
    rintro x ⟨y, rfl⟩
    exact binary_trace_artinSchreier L y
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hs := LinearMap.finrank_range_add_finrank_ker (binaryArtinSchreier L)
  rw [ker_binaryArtinSchreier, finrank_span_singleton (one_ne_zero : (1 : L) ≠ 0)] at hs
  have ht := LinearMap.finrank_range_add_finrank_ker (Algebra.trace (ZMod 2) L)
  have hr : (Algebra.trace (ZMod 2) L).range = ⊤ :=
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective (ZMod 2) L)
  rw [hr, finrank_top, finrank_self] at ht
  omega

/-- A binary Artin–Schreier equation is solvable exactly when its constant has trace zero. -/
theorem binary_artinSchreier_solvable_iff (a : L) :
    (∃ x : L, x ^ 2 + x = a) ↔ Algebra.trace (ZMod 2) L a = 0 := by
  change (∃ x : L, binaryArtinSchreier L x = a) ↔ _
  rw [← LinearMap.mem_range, range_binaryArtinSchreier, LinearMap.mem_ker]

/-- In odd degree, the trace shear projects onto the Artin–Schreier image. -/
private theorem range_binaryTraceShear_odd (ho : finrank (ZMod 2) L % 2 = 1) :
    (binaryTraceShear L).range = (binaryArtinSchreier L).range := by
  have hc : (finrank (ZMod 2) L : ZMod 2) = 1 := by
    apply ZMod.val_injective 2
    rw [ZMod.val_natCast]
    exact ho
  have ht : Algebra.trace (ZMod 2) L 1 = 1 := (binary_trace_one L).trans hc
  rw [range_binaryArtinSchreier]
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    change Algebra.trace (ZMod 2) L (binaryTraceShear L y) = 0
    rw [binaryTraceShear_apply, map_add, map_smul, ht, smul_eq_mul, mul_one,
      CharTwo.add_self_eq_zero]
  · intro x hx
    refine ⟨x, ?_⟩
    rw [binaryTraceShear_apply, show Algebra.trace (ZMod 2) L x = 0 from hx,
      zero_smul, add_zero]

/-- The trace shear is surjective in even degree and has the Artin–Schreier image in odd degree. -/
theorem range_binaryTraceShear_field :
    (binaryTraceShear L).range =
      if finrank (ZMod 2) L % 2 = 0 then ⊤ else (binaryArtinSchreier L).range := by
  split_ifs with he
  · have hc : (finrank (ZMod 2) L : ZMod 2) = 0 := by
      apply ZMod.val_injective 2
      rw [ZMod.val_natCast]
      exact he
    apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨binaryTraceShear L x, ?_⟩
    rw [binaryTraceShear_square, hc, mul_zero, zero_smul, add_zero]
  · exact range_binaryTraceShear_odd L (by omega)

/-- The corrected trace radical is the Artin–Schreier kernel precisely in odd degree. -/
theorem ker_binaryTraceShear_field :
    (binaryTraceShear L).ker =
      if finrank (ZMod 2) L % 2 = 0 then ⊥ else (binaryArtinSchreier L).ker := by
  rw [← ker_binaryTraceForm_eq_ker_shear, ker_binaryTraceForm_field, ker_binaryArtinSchreier]

/-- The native binary Artin–Schreier polynomial has a root exactly at trace-zero constants. -/
theorem binary_artinSchreierPolynomial_hasRoot_iff (a : L) :
    (∃ x : L, Polynomial.IsRoot (artinSchreierPolynomial 2 a) x) ↔
      Algebra.trace (ZMod 2) L a = 0 := by
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  change (∃ x : L, (Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a).eval x = 0) ↔ _
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  simp only [sub_eq_zero]
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  exact binary_artinSchreier_solvable_iff L a

/-- The native binary Artin–Schreier polynomial is irreducible exactly at trace-one constants. -/
theorem binary_artinSchreierPolynomial_irreducible_iff (a : L) :
    Irreducible (artinSchreierPolynomial 2 a) ↔ Algebra.trace (ZMod 2) L a = 1 := by
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  rw [irreducible_artinSchreierPolynomial_iff]
  simp only [sub_eq_add_neg, CharTwo.neg_eq, binary_artinSchreier_solvable_iff]
  constructor
  · intro h
    simpa using ZMod.pow_card_sub_one_eq_one h
  · intro h
    rw [h]
    exact one_ne_zero

/-- A product of finite binary fields has a componentwise trace obstruction to
Artin–Schreier solvability. -/
theorem binary_artinSchreier_pi_solvable_iff {ι : Type*} (K : ι → Type*)
    [∀ i, Field (K i)] [∀ i, Algebra (ZMod 2) (K i)]
    [∀ i, Module.Finite (ZMod 2) (K i)] (a : ∀ i, K i) :
    (∃ x : ∀ i, K i, x ^ 2 + x = a) ↔
      ∀ i, Algebra.trace (ZMod 2) (K i) (a i) = 0 := by
  constructor
  · rintro ⟨x, hx⟩ i
    exact (binary_artinSchreier_solvable_iff (K i) (a i)).mp ⟨x i, congrFun hx i⟩
  · intro h
    choose x hx using fun i => (binary_artinSchreier_solvable_iff (K i) (a i)).mpr (h i)
    exact ⟨x, funext hx⟩

#print axioms range_binaryArtinSchreier
#print axioms binary_artinSchreier_solvable_iff
#print axioms range_binaryTraceShear_field
#print axioms ker_binaryTraceShear_field
#print axioms binary_artinSchreierPolynomial_hasRoot_iff
#print axioms binary_artinSchreierPolynomial_irreducible_iff
#print axioms binary_artinSchreier_pi_solvable_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
