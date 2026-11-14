import GaloisForLFunctions.RHTower.QuadraticJacobiSum
import GaloisForLFunctions.HTGeometry.Arithmetic.QuadraticResidueParity
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerBorder

/-!
# Descent matrices of an actual odd-prime family

Legendre symbols supply the entries of the binary descent matrix.
Its diagonal gives zero row sums, and quadratic reciprocity proves its
rank-one symmetry defect. If the product modulus is `5` modulo `8`, the
two supplementary symbol sums are zero and one. These arithmetic facts
instantiate the kernel dictionary and exact bordered determinant test.
-/

namespace RHTower.OddPrimeFamily

open Matrix
open GaloisForLFunctions.HTGeometry.Arithmetic
open GaloisForLFunctions.HTGeometry.LinearAlgebra

variable {ι : Type*} [Fintype ι]

/-- Parities of the symbols of `-1` at the primes of the family. -/
def selmerY (P : OddPrimeFamily ι) (i : ι) : ZMod 2 :=
  quadraticResidueParity (P.prime i).1 (-1)

/-- Parities of the symbols of `2` at the primes of the family. -/
def selmerZ (P : OddPrimeFamily ι) (i : ι) : ZMod 2 :=
  quadraticResidueParity (P.prime i).1 2

variable [DecidableEq ι]

/-- The off-diagonal entries are the additive Legendre symbols `(q_j/q_i)`;
the diagonal is chosen to make every row sum zero. -/
def selmerMatrix (P : OddPrimeFamily ι) : Matrix ι ι (ZMod 2) := fun i j =>
  if i = j then ∑ k ∈ Finset.univ.erase i,
    quadraticResidueParity (P.prime i).1 (P.prime k).1
  else quadraticResidueParity (P.prime i).1 (P.prime j).1

theorem selmerMatrix_one (P : OddPrimeFamily ι) : P.selmerMatrix *ᵥ 1 = 0 := by
  funext i
  change (∑ j, P.selmerMatrix i j * 1) = 0
  simp only [mul_one]
  rw [← Finset.sum_erase_add Finset.univ (P.selmerMatrix i) (Finset.mem_univ i)]
  have hsum : (∑ j ∈ Finset.univ.erase i, P.selmerMatrix i j) =
      ∑ j ∈ Finset.univ.erase i,
        quadraticResidueParity (P.prime i).1 (P.prime j).1 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact if_neg (Ne.symm (Finset.mem_erase.mp hj).1)
  rw [hsum, selmerMatrix, if_pos rfl, CharTwo.add_self_eq_zero]

/-- Quadratic reciprocity gives the exact symmetry defect of the
actual residue-symbol matrix. -/
theorem selmerMatrix_reciprocity (P : OddPrimeFamily ι) :
    P.selmerMatrix + P.selmerMatrixᵀ = vecMulVec P.selmerY P.selmerY + diagonal P.selmerY := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hyi : P.selmerY i * P.selmerY i = P.selmerY i := by
      simpa only [pow_two] using ZMod.pow_card (P.selmerY i)
    change P.selmerMatrix i i + P.selmerMatrix i i =
      P.selmerY i * P.selmerY i + diagonal P.selmerY i i
    rw [diagonal_apply, if_pos rfl, hyi, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
  · have h := quadraticResidueParity_reciprocity_neg_one
      (P.prime i).2.2 (P.prime j).2.2 (P.pairwise_ne hij)
    change P.selmerMatrix i j + P.selmerMatrix j i =
      P.selmerY i * P.selmerY j + diagonal P.selmerY i j
    rw [diagonal_apply, if_neg hij, add_zero]
    simpa only [selmerMatrix, if_neg hij, if_neg (Ne.symm hij), selmerY, add_comm] using h

omit [DecidableEq ι] in
theorem selmerY_sum (P : OddPrimeFamily ι) (hl : P.modulus % 8 = 5) : P.selmerY ⬝ᵥ 1 = 0 := by
  have hodd : Odd P.modulus := Nat.odd_iff.mpr (by omega)
  have hfour : P.modulus % 4 = 1 := by omega
  have hsum := quadraticResidueParity_sum Finset.univ (fun i => (P.prime i).1) (-1)
    (fun i _ => by
      simpa only [Int.cast_neg, Int.cast_one] using
        (neg_ne_zero.mpr one_ne_zero : (-1 : ZMod (P.prime i).1) ≠ 0))
  change (∑ i, P.selmerY i * 1) = 0
  simp only [mul_one, selmerY]
  rw [hsum]
  change signParity (jacobiSym (-1) P.modulus) = 0
  rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four hfour, signParity_one]

omit [DecidableEq ι] in
theorem selmerZ_sum (P : OddPrimeFamily ι) (hl : P.modulus % 8 = 5) : P.selmerZ ⬝ᵥ 1 = 1 := by
  have hodd : Odd P.modulus := Nat.odd_iff.mpr (by omega)
  have htwo : P.modulus % 2 ≠ 0 := by omega
  have hres : ∀ i : ι, ((2 : ℤ) : ZMod (P.prime i).1) ≠ 0 := by
    intro i
    have h2 : ((2 : ℕ) : ZMod (P.prime i).1) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => (P.prime i).2.2
        ((Nat.prime_dvd_prime_iff_eq (P.prime i).2.1 Nat.prime_two).mp h)
    exact_mod_cast h2
  have hsum := quadraticResidueParity_sum Finset.univ (fun i => (P.prime i).1) 2
    (fun i _ => hres i)
  change (∑ i, P.selmerZ i * 1) = 1
  simp only [mul_one, selmerZ]
  rw [hsum]
  change signParity (jacobiSym 2 P.modulus) = 1
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight, if_neg htwo,
    if_neg (by omega : ¬ (P.modulus % 8 = 1 ∨ P.modulus % 8 = 7)), signParity_neg_one]

/-- Kernel isomorphism for the concrete residue-symbol matrices. All
matrix identities are proved from quadratic reciprocity. -/
def selmerKernelEquiv (P : OddPrimeFamily ι) (hl : P.modulus % 8 = 5) :
    LinearMap.ker (binarySelmerSource P.selmerMatrix P.selmerY P.selmerZ).mulVecLin ≃ₗ[ZMod 2]
      LinearMap.ker (binarySelmerSymmetric P.selmerMatrix P.selmerZ).mulVecLin :=
  binarySelmerKernelEquiv P.selmerMatrix P.selmerY P.selmerZ
    P.selmerMatrix_one P.selmerMatrix_reciprocity (P.selmerY_sum hl)

/-- Exact determinant criterion for the actual prime-family descent
matrix, with no separately assumed reciprocity or symbol-sum identities. -/
theorem selmer_border_det_ne_zero_iff (P : OddPrimeFamily ι) (hl : P.modulus % 8 = 5)
    {κ : ι ⊕ ι → ZMod 2} (hκne : κ ≠ 0)
    (hκ : binarySelmerSource P.selmerMatrix P.selmerY P.selmerZ *ᵥ κ = 0) :
    (symmetricBorder (binarySelmerSymmetric P.selmerMatrix P.selmerZ)
      (Sum.elim (P.selmerY + P.selmerZ) 0)).det ≠ 0 ↔
      (∀ v, binarySelmerSource P.selmerMatrix P.selmerY P.selmerZ *ᵥ v = 0 →
        ∃ a : ZMod 2, v = a • κ) ∧
      P.selmerY ⬝ᵥ (κ ∘ Sum.inl) + P.selmerZ ⬝ᵥ (κ ∘ Sum.inr) ≠ 0 :=
  binarySelmer_border_det_ne_zero_iff P.selmerMatrix P.selmerY P.selmerZ
    P.selmerMatrix_one P.selmerMatrix_reciprocity (P.selmerY_sum hl) (P.selmerZ_sum hl) hκne hκ

#print axioms selmerMatrix_reciprocity
#print axioms selmerKernelEquiv
#print axioms selmer_border_det_ne_zero_iff

end RHTower.OddPrimeFamily
