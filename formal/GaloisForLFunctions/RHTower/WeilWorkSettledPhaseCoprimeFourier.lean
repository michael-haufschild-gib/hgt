import Mathlib.Analysis.Fourier.ZMod

/-!
# The coprime mask is a finite real cosine polynomial

This algebraic transfer applies the rational source estimates without requiring
positivity of the source after deletion of any primes.
-/

open Complex Finset ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

def coprimeMask (Q n : ℕ) : ℝ := if n.Coprime Q then 1 else 0

private def cyclicCoprimeMask (Q : ℕ) (j : ZMod Q) : ℂ := by
  classical
  exact if IsUnit j then 1 else 0

private theorem cyclicCoprimeMask_conj (Q : ℕ) (j : ZMod Q) :
    conj (cyclicCoprimeMask Q j) = cyclicCoprimeMask Q j := by
  unfold cyclicCoprimeMask
  split_ifs <;> simp

private theorem cyclicCoprimeMask_even (Q : ℕ) : Function.Even (cyclicCoprimeMask Q) := by
  intro j
  by_cases h : IsUnit j
  · simp only [cyclicCoprimeMask, if_pos h, if_pos h.neg]
  · have hn : ¬IsUnit (-j) := fun hn => h (by simpa only [neg_neg] using hn.neg)
    simp only [cyclicCoprimeMask, if_neg h, if_neg hn]

private theorem dft_cyclicCoprimeMask_real (Q : ℕ) [NeZero Q] (k : ZMod Q) :
    ((ZMod.dft (cyclicCoprimeMask Q) k).re : ℂ) = ZMod.dft (cyclicCoprimeMask Q) k := by
  apply Complex.conj_eq_iff_re.mp
  calc
    conj (ZMod.dft (cyclicCoprimeMask Q) k) = ZMod.dft (cyclicCoprimeMask Q) (-k) := by
      simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, cyclicCoprimeMask_conj]
      apply Finset.sum_congr rfl
      intro j _
      rw [← AddChar.map_neg_eq_conj]
      simp only [neg_neg, mul_neg]
    _ = _ := (ZMod.dft_even_iff.mpr (cyclicCoprimeMask_even Q)) k

private theorem re_stdAddChar_mul_nat (Q : ℕ) [NeZero Q] (j : ZMod Q) (n : ℕ) :
    (ZMod.stdAddChar (j * (n : ZMod Q))).re =
      Real.cos (2 * Real.pi * ((n : ℝ) * (j.val / Q))) := by
  have hc : (((j.val * n : ℕ) : ℤ) : ZMod Q) = j * (n : ZMod Q) := by simp
  rw [← hc, ZMod.stdAddChar_coe]
  have he : 2 * (Real.pi : ℂ) * I * ((j.val * n : ℕ) : ℤ) / (Q : ℂ) =
      ((2 * Real.pi * ((n : ℝ) * (j.val / Q)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]

/-- An exact finite real cosine expansion, valid for every integer input. -/
theorem exists_coprimeMask_cosine_expansion (Q : ℕ) [NeZero Q] :
    ∃ a : ZMod Q → ℝ, ∀ n : ℕ,
      coprimeMask Q n = ∑ j : ZMod Q, a j * Real.cos (2 * Real.pi * ((n : ℝ) * (j.val / Q))) := by
  let F := cyclicCoprimeMask Q
  refine ⟨fun j => (ZMod.dft F j).re / Q, fun n => ?_⟩
  have h := congrFun (ZMod.dft.symm_apply_apply F) (n : ZMod Q)
  rw [ZMod.invDFT_apply] at h
  have hf : F (n : ZMod Q) = (coprimeMask Q n : ℂ) := by
    by_cases hc : n.Coprime Q
    · have hu : IsUnit (n : ZMod Q) := (ZMod.isUnit_iff_coprime n Q).mpr hc
      simp only [F, cyclicCoprimeMask, coprimeMask, if_pos hc, if_pos hu, Complex.ofReal_one]
    · have hu : ¬IsUnit (n : ZMod Q) := fun hu => hc ((ZMod.isUnit_iff_coprime n Q).mp hu)
      simp only [F, cyclicCoprimeMask, coprimeMask, if_neg hc, if_neg hu, Complex.ofReal_zero]
  rw [hf] at h
  have hr := congrArg Complex.re h
  have hn : ((Q : ℂ)⁻¹) = (((Q : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  simp only [smul_eq_mul, hn, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.re_sum] at hr
  rw [← hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (ZMod.dft F j).im = 0 := by
    rw [← dft_cyclicCoprimeMask_real Q j]
    exact Complex.ofReal_im _
  rw [hj, mul_zero, sub_zero, re_stdAddChar_mul_nat Q j n]
  ring

end RHTower.WeilSingularArithmetic
