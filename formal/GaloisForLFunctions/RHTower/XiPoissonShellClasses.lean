import GaloisForLFunctions.RHTower.XiPoissonShellPolynomial
import GaloisForLFunctions.RHTower.XiPoissonBottomOnLine

/-!
# Displacement classes of the bottom shell

On the bottom shell every copy has the same height, so a copy is determined up to multiplicity by its
displacement: the class at displacement `l` consists of copies whose Poisson point is exactly
`g_1 + l i`.  Its coefficient sum in the `n`-th shell polynomial is therefore
`(class size) * (g_1 + l i) ^ n`, and line conjugation matches the class at `l` with the class at
`-l`, giving conjugate sums of equal size.

These are the Xi-side inputs of `HTGeometry.exists_ge_re_sum_exp_le_of_split`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The copies of the bottom shell at a given displacement. -/
def xiShellClass (l : ℝ) : Finset XiZeroCopy :=
  xiPoissonBottomShell.filter (fun q => (xiPoissonPoint q).im = l)

theorem mem_xiShellClass {l : ℝ} {q : XiZeroCopy} :
    q ∈ xiShellClass l ↔ q ∈ xiPoissonBottomShell ∧ (xiPoissonPoint q).im = l := by
  classical
  simp [xiShellClass]

/-- A copy of the bottom shell at displacement `l` has Poisson point exactly `g_1 + l i`. -/
theorem xiPoissonPoint_of_mem_xiShellClass {l : ℝ} {q : XiZeroCopy} (hq : q ∈ xiShellClass l) :
    xiPoissonPoint q = ((xiPoissonBottomHeight : ℝ) : ℂ) + (l : ℂ) * I := by
  obtain ⟨hs, hj⟩ := mem_xiShellClass.mp hq
  conv_lhs => rw [← Complex.re_add_im (xiPoissonPoint q)]
  rw [mem_xiPoissonBottomShell.mp hs, hj]

/-- The class coefficient sum. -/
theorem xiShellClass_sum (l : ℝ) (n : ℕ) :
    (∑ q ∈ xiShellClass l, xiPoissonPoint q ^ n)
      = (((xiShellClass l).card : ℝ) : ℂ) *
          (((xiPoissonBottomHeight : ℝ) : ℂ) + (l : ℂ) * I) ^ n := by
  classical
  have hcong : ∀ q ∈ xiShellClass l,
      xiPoissonPoint q ^ n = (((xiPoissonBottomHeight : ℝ) : ℂ) + (l : ℂ) * I) ^ n := by
    intro q hq
    rw [xiPoissonPoint_of_mem_xiShellClass hq]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- Line conjugation carries the class at `l` into the class at `-l`. -/
theorem lineConj_mem_xiShellClass {l : ℝ} {q : XiZeroCopy} (hq : q ∈ xiShellClass l) :
    xiZeroCopyLineConjEquiv q ∈ xiShellClass (-l) := by
  obtain ⟨hs, hj⟩ := mem_xiShellClass.mp hq
  refine mem_xiShellClass.mpr ⟨mem_xiPoissonBottomShell_lineConj hs, ?_⟩
  rw [xiPoissonPoint_lineConj, Complex.conj_im, hj]

/-- Conjugate classes have the same size. -/
theorem card_xiShellClass_neg (l : ℝ) :
    (xiShellClass (-l)).card = (xiShellClass l).card := by
  classical
  refine le_antisymm ?_ ?_
  · have hmap : ∀ q ∈ xiShellClass (-l), xiZeroCopyLineConjEquiv q ∈ xiShellClass l := by
      intro q hq
      have h := lineConj_mem_xiShellClass hq
      rwa [neg_neg] at h
    exact Finset.card_le_card_of_injOn _ hmap
      (fun a _ b _ hab => xiZeroCopyLineConjEquiv.injective hab)
  · exact Finset.card_le_card_of_injOn _ (fun q hq => lineConj_mem_xiShellClass hq)
      (fun a _ b _ hab => xiZeroCopyLineConjEquiv.injective hab)

/-- **The mirror class carries the conjugate coefficient sum.** -/
theorem xiShellClass_sum_neg (l : ℝ) (n : ℕ) :
    (∑ q ∈ xiShellClass (-l), xiPoissonPoint q ^ n)
      = (starRingEnd ℂ) (∑ q ∈ xiShellClass l, xiPoissonPoint q ^ n) := by
  rw [xiShellClass_sum, xiShellClass_sum, card_xiShellClass_neg, map_mul, map_pow,
    Complex.conj_ofReal]
  congr 2
  simp

/-- The class modulus. -/
theorem norm_xiShellClass_sum (l : ℝ) (n : ℕ) :
    ‖∑ q ∈ xiShellClass l, xiPoissonPoint q ^ n‖ =
      ((xiShellClass l).card : ℝ) *
        Real.sqrt (xiPoissonBottomHeight ^ 2 + l ^ 2) ^ n := by
  rw [xiShellClass_sum, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  congr 2
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, sub_zero, add_zero]
  congr 1
  ring

end

end RHTower
