import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicProductFourierParseval

/-!
# Exact Fourier inversion on products of cyclic residue groups

This file proves the unnormalized Fourier-square identity on the dependent
finite product `∏ i, ZMod (N i)`.  Retaining the exact product-cardinality
factor is essential: it cancels the two Haar Jacobians only after the theorem
is lifted to the full product of p-adic fields.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Finset AddChar ZMod
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (N : ι → ℕ) [∀ i, NeZero (N i)]

omit [DecidableEq ι] in
/-- Negating the source index conjugates the product Fourier character. -/
theorem fieldOneFiniteCyclicProductCharacter_star_neg_left
    (j k : FieldOneFiniteCyclicProduct N) :
    star (fieldOneFiniteCyclicProductCharacter N (-j) k) =
      fieldOneFiniteCyclicProductCharacter N j k := by
  simp only [fieldOneFiniteCyclicProductCharacter, Pi.neg_apply, neg_mul,
    neg_neg, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  change conj (ZMod.stdAddChar (j i * k i)) =
    ZMod.stdAddChar (-(j i * k i))
  rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv]

omit [DecidableEq ι] in
/-- The canonical product Fourier kernel is symmetric. -/
theorem fieldOneFiniteCyclicProductCharacter_comm
    (j k : FieldOneFiniteCyclicProduct N) :
    fieldOneFiniteCyclicProductCharacter N j k =
      fieldOneFiniteCyclicProductCharacter N k j := by
  simp only [fieldOneFiniteCyclicProductCharacter]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

/-- A source scalar factors through the product DFT. -/
theorem fieldOneFiniteCyclicProductDFT_const_mul
    (c : ℂ) (f : FieldOneFiniteCyclicProduct N → ℂ) :
    fieldOneFiniteCyclicProductDFT N (fun j => c * f j) =
      fun k => c * fieldOneFiniteCyclicProductDFT N f k := by
  funext k
  simp only [fieldOneFiniteCyclicProductDFT, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact unnormalized Fourier inversion on a product of cyclic residue
groups: applying the DFT twice gives reflection times the product
cardinality. -/
theorem fieldOneFiniteCyclicProductDFT_dft
    (f : FieldOneFiniteCyclicProduct N → ℂ) :
    fieldOneFiniteCyclicProductDFT N
        (fieldOneFiniteCyclicProductDFT N f) =
      fun j => ((∏ i, N i : ℕ) : ℂ) * f (-j) := by
  funext l
  simp only [fieldOneFiniteCyclicProductDFT, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ k,
        fieldOneFiniteCyclicProductCharacter N k l *
          (fieldOneFiniteCyclicProductCharacter N j k * f j)) =
        ∑ j, f j * ∑ k,
          star (fieldOneFiniteCyclicProductCharacter N (-j) k) *
            fieldOneFiniteCyclicProductCharacter N l k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [fieldOneFiniteCyclicProductCharacter_star_neg_left N j k,
        fieldOneFiniteCyclicProductCharacter_comm N k l]
      ring
    _ = ∑ j, f j *
        (if -j = l then ((∏ i, N i : ℕ) : ℂ) else 0) := by
      simp_rw [fieldOneFiniteCyclicProductFourier_orthogonality N]
      simp only [Nat.cast_ite, Nat.cast_zero]
    _ = ((∏ i, N i : ℕ) : ℂ) * f (-l) := by
      rw [Finset.sum_eq_single (-l)]
      · simp
        ring
      · intro j _ hj
        have hneg : -j ≠ l := by
          intro h
          apply hj
          simpa using congrArg Neg.neg h
        simp [hneg]
      · simp

end

end GaloisForLFunctions.RHTower
