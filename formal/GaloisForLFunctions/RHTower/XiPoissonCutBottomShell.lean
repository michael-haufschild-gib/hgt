import GaloisForLFunctions.RHTower.XiPoissonCutHalfPlaneDecay

/-!
# The bottom shell of a cut divisor

The peeling wrapper needs, for each height cut, the same shell data the full divisor has: the copies
of the cut whose height equals the cut's least height, and the fact that on that shell the height
factors out of the trace exactly.

Everything mirrors `XiPoissonBottomShellRigidity`, with `xiPoissonCutHeight g` in place of the global
bottom height.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The bottom shell of the divisor above a height cut. -/
def xiPoissonCutBottomShell (g : ℝ) : Finset XiZeroCopy :=
  (finite_xiPoissonCut_shell g (xiPoissonCutHeight g)).toFinset

theorem mem_xiPoissonCutBottomShell {g : ℝ} {q : XiZeroCopy} :
    q ∈ xiPoissonCutBottomShell g ↔
      q ∈ xiPoissonCut g ∧ (xiPoissonPoint q).re = xiPoissonCutHeight g := by
  rw [xiPoissonCutBottomShell, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcut, hle⟩
    exact ⟨hcut, le_antisymm hle (xiPoissonCutHeight_le hcut)⟩
  · rintro ⟨hcut, heq⟩
    exact ⟨hcut, le_of_eq heq⟩

/-- The bottom-shell sum of a cut divisor on a vertical line. -/
def xiPoissonCutBottomShellSum (g σ u : ℝ) : ℂ :=
  ∑ q ∈ xiPoissonCutBottomShell g, xiPoissonTerm ((σ : ℂ) + (u : ℂ) * I) q

/-- On the cut's bottom shell the height factors out exactly. -/
theorem xiPoissonCutBottomShellSum_eq (g σ u : ℝ) :
    xiPoissonCutBottomShellSum g σ u =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (xiPoissonCutHeight g : ℂ)) *
        ∑ q ∈ xiPoissonCutBottomShell g,
          Complex.exp (-(σ : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
            ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ) := by
  rw [xiPoissonCutBottomShellSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hsplit : xiPoissonPoint q =
      ((xiPoissonCutHeight g : ℝ) : ℂ) + ((xiPoissonPoint q).im : ℂ) * I := by
    rw [← (mem_xiPoissonCutBottomShell.mp hq).2]
    exact (Complex.re_add_im _).symm
  rw [xiPoissonTerm]
  conv_lhs => rw [hsplit]
  exact xiPoisson_line_factor σ u (xiPoissonCutHeight g) (xiPoissonPoint q).im

/-- Line conjugation preserves the cut and its bottom shell. -/
theorem mem_xiPoissonCut_lineConj {g : ℝ} {q : XiZeroCopy} (hq : q ∈ xiPoissonCut g) :
    xiZeroCopyLineConjEquiv q ∈ xiPoissonCut g := by
  rw [mem_xiPoissonCut, xiPoissonPoint_lineConj, Complex.conj_re]
  exact hq

theorem mem_xiPoissonCutBottomShell_lineConj {g : ℝ} {q : XiZeroCopy}
    (hq : q ∈ xiPoissonCutBottomShell g) :
    xiZeroCopyLineConjEquiv q ∈ xiPoissonCutBottomShell g := by
  obtain ⟨hcut, heq⟩ := mem_xiPoissonCutBottomShell.mp hq
  refine mem_xiPoissonCutBottomShell.mpr ⟨mem_xiPoissonCut_lineConj hcut, ?_⟩
  rw [xiPoissonPoint_lineConj, Complex.conj_re]
  exact heq

end

end RHTower
