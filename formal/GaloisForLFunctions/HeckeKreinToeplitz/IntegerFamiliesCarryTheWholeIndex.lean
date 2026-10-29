import GaloisForLFunctions.HeckeKreinToeplitz.IndexIsEnergy

/-!
# Integer families carry the whole index

The atomic receivers place their atoms at `log n`, `n ≤ N`. In kernel language they are the Gram
matrices of a kernel on the integer windows `{1, …, N} ⊂ ℚ_{>0}` (`intWindow`).

**Principal submatrices** (`hermNegIndex_submatrix_le`). Reindexing a Gram matrix along any map
never raises its negative index: the form of `M.submatrix f f` is the form of `M` on the
coefficient sums over the fibres of `f`.

**Integer windows carry the whole index** (`negIndex_eq_iSup_intWindow`). For every kernel on
`ℚ_{>0}`, the negative index is the supremum over `N` of the negative squares of its Gram matrix on
`{1, …, N}`. A finite family of rationals, multiplied by a common denominator `b`, becomes a family
of positive integers, and Hecke covariance keeps its Gram matrix.

**The integer atomic receiver** (`negIndex_zetaKernel_eq_iSup_integerAtoms`). For `ζ`, the Weil Gram
matrices of the translates `B(· − log n)`, `n ≤ N`, of the cubic spline have at most `κ(K_ζ)`
negative squares and reach it as `N → ∞`: they count the zeros right of the line, and RH holds iff
they are all positive semidefinite (`riemannHypothesis_iff_integerAtoms`). Atomic families are
limits in the index topology, already at a fixed profile.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx weilGram rightZeros)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **Reindexing never raises the negative index.** -/
theorem hermNegIndex_submatrix_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix β β ℂ) (f : α → β) : hermNegIndex (M.submatrix f f) ≤ hermNegIndex M := by
  let L : (α → ℂ) →ₗ[ℂ] (β → ℂ) :=
    { toFun := fun c b => ∑ a ∈ univ.filter (fun a => f a = b), c a
      map_add' := fun c d => funext fun b => by simp only [Pi.add_apply, sum_add_distrib]
      map_smul' := fun t c => funext fun b => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum] }
  refine hermNegIndex_le_of_hermQuad_eq _ _ L fun c => ?_
  have inner : ∀ b, ∑ b', M b b' * L c b' = ∑ a', M b (f a') * c a' := fun b => by
    show ∑ b', M b b' * ∑ a' ∈ univ.filter (fun a' => f a' = b'), c a' = _
    simp only [mul_sum]
    rw [← sum_fiberwise univ f (fun a' => M b (f a') * c a')]
    refine sum_congr rfl fun b' _ => sum_congr rfl fun a' ha' => ?_
    rw [(mem_filter.mp ha').2]
  simp only [hermQuad, dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply, inner]
  congr 1
  show ∑ b, star (∑ a ∈ univ.filter (fun a => f a = b), c a) * ∑ a', M b (f a') * c a' = _
  simp only [star_sum, sum_mul]
  rw [← sum_fiberwise univ f (fun a => star (c a) * ∑ a', M (f a) (f a') * c a')]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a ha => ?_
  rw [(mem_filter.mp ha).2]

/-- The integers `1, …, N` in the Hecke lattice. -/
def intWindow (N : ℕ) : Fin N → HeckeLattice := fun i => ⟨(i : ℚ) + 1, by positivity⟩

/-- A positive rational times the product of all denominators is a positive integer. -/
theorem exists_nat_mul_eq {n : ℕ} (x : Fin n → HeckeLattice) (i : Fin n) :
    ∃ m : ℕ, 1 ≤ m ∧ ((∏ j, ((x j : ℚ)).den : ℕ) : ℚ) * (x i : ℚ) = m := by
  classical
  set c : ℕ := ∏ j ∈ univ.erase i, ((x j : ℚ)).den
  have hpos : 0 < ((x i : ℚ)).num := Rat.num_pos.mpr (x i).2
  have hc : 0 < c := prod_pos fun j _ => Rat.den_pos _
  refine ⟨c * ((x i : ℚ)).num.toNat, Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hc.ne' (by omega)), ?_⟩
  have h1 : (x i : ℚ) * ((x i : ℚ)).den = ((x i : ℚ)).num := Rat.mul_den_eq_num _
  have hnum : (((x i : ℚ)).num : ℚ) = ((((x i : ℚ)).num.toNat : ℕ) : ℚ) := by
    have h := Int.toNat_of_nonneg hpos.le
    exact_mod_cast h.symm
  rw [← mul_prod_erase univ (fun j => ((x j : ℚ)).den) (mem_univ i)]
  push_cast
  rw [show ((x i : ℚ)).den * (∏ j ∈ univ.erase i, (((x j : ℚ)).den : ℚ)) * (x i : ℚ) =
      (c : ℚ) * ((x i : ℚ) * ((x i : ℚ)).den) by simp only [c]; push_cast; ring, h1, hnum]

/-- **Integer windows carry the whole index of a kernel on `ℚ_{>0}`.** -/
theorem negIndex_eq_iSup_intWindow (k : HeckeLattice → ℂ) :
    negIndex k = ⨆ N : ℕ, (hermNegIndex (gram k (intWindow N)) : ℕ∞) := by
  classical
  refine le_antisymm ?_ (iSup_le fun N => hermNegIndex_gram_le_negIndex k _)
  rw [negIndex_le_iff]
  intro n x
  set b : ℕ := ∏ j, ((x j : ℚ)).den
  have hb : 0 < b := prod_pos fun j _ => Rat.den_pos _
  set B : HeckeLattice := ⟨b, by exact_mod_cast hb⟩
  choose m hm1 hm using exists_nat_mul_eq x
  set N : ℕ := ∑ i, m i
  have hmN : ∀ i, m i ≤ N := fun i => single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  let f : Fin n → Fin N := fun i => ⟨m i - 1, by have := hmN i; have := hm1 i; omega⟩
  have hBx : ∀ i, B * x i = intWindow N (f i) := fun i => by
    apply Subtype.ext
    show (b : ℚ) * (x i : ℚ) = ((m i - 1 : ℕ) : ℚ) + 1
    rw [hm i, Nat.cast_sub (hm1 i)]
    push_cast
    ring
  have hgram : gram k x = (gram k (intWindow N)).submatrix f f := by
    rw [← gram_mul_left k x B]
    ext i j
    simp only [gram, Matrix.submatrix_apply, hBx]
  rw [hgram]
  exact (Nat.cast_le.mpr (hermNegIndex_submatrix_le _ f)).trans
    (le_iSup (fun N => (hermNegIndex (gram k (intWindow N)) : ℕ∞)) N)

theorem scale_intWindow (N : ℕ) (i : Fin N) :
    scale heckeLogScale (intWindow N i) = Real.log ((i : ℝ) + 1) := by
  rw [scale_heckeLogScale]
  push_cast [intWindow]
  rfl

/-- **The integer atomic receiver counts the right zeros of `ζ`.** -/
theorem negIndex_zetaKernel_eq_iSup_integerAtoms :
    (rightZeros zetaZeroConfig).encard =
      ⨆ N : ℕ, (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        fun i : Fin N => shiftTest (Real.log ((i : ℝ) + 1)) (cx cubicSpline)) : ℕ∞) := by
  rw [← negIndex_zetaKernel, negIndex_eq_iSup_intWindow]
  refine iSup_congr fun N => ?_
  rw [gram_zetaKernel_eq_weilGram]
  simp only [scale_intWindow]

/-- **RH is positivity of the integer atomic receiver of the cubic spline.** -/
theorem riemannHypothesis_iff_integerAtoms :
    RiemannHypothesis ↔ ∀ N : ℕ, hermNegIndex (weilGram
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        fun i : Fin N => shiftTest (Real.log ((i : ℝ) + 1)) (cx cubicSpline)) = 0 := by
  rw [riemannHypothesis_iff_negIndex_zetaKernel_eq_zero, negIndex_zetaKernel,
    negIndex_zetaKernel_eq_iSup_integerAtoms, ENat.iSup_eq_zero]
  simp only [Nat.cast_eq_zero]

end GaloisForLFunctions.HeckeKreinToeplitz
