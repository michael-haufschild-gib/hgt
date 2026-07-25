import GaloisForLFunctions.RHTower.XiSpectralFamilyOnLine

/-!
# Lifting the low copies of an admissible family

The minimal-counterexample wrapper needs, for each height cut, a family whose least-height shell is
the cut's own.  Rather than reindex, replace each copy below the cut by a *real* point at a fixed
height `H` above the cut: the result is again admissible -- heights, summability, shells and
conjugation stability all survive, and the replaced points have zero displacement -- and its trace
differs from the original by two finite sums.

The construction is what lets the interface assembly be applied at every height without ever
changing the index type.
-/

open Complex
open scoped BigOperators

namespace RHTower

namespace SpectralFamily

noncomputable section

variable (F : SpectralFamily)

/-- The copies below a height cut. -/
def below (g : ℝ) : Set XiZeroCopy := {q : XiZeroCopy | (F.pt q).re < g}

theorem finite_below (g : ℝ) : (F.below g).Finite := by
  refine (F.shell_finite g).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq]
  exact le_of_lt hq

theorem below_lineConj {g : ℝ} {q : XiZeroCopy} (hq : q ∈ F.below g) :
    xiZeroCopyLineConjEquiv q ∈ F.below g := by
  show (F.pt (xiZeroCopyLineConjEquiv q)).re < g
  rw [F.conj_stable, Complex.conj_re]
  exact hq

/-- The family with every copy below `g` replaced by a real point of height `H`. -/
def lift (g H : ℝ) (hH : F.base ≤ H) : SpectralFamily where
  pt := fun q => if g ≤ (F.pt q).re then F.pt q else ((H : ℝ) : ℂ)
  base := F.base
  base_pos := F.base_pos
  base_le := by
    intro q
    by_cases h : g ≤ (F.pt q).re
    · simpa [h] using F.base_le q
    · simpa [h] using hH
  abs_im_lt := by
    intro q
    by_cases h : g ≤ (F.pt q).re
    · simpa [h] using F.abs_im_lt q
    · simp [h]
  summable_weight := by
    intro σ hσ
    classical
    simp only [apply_ite Complex.re, Complex.ofReal_re]
    have hfin : (F.below g).Finite := F.finite_below g
    have h1 : Summable (fun q : (F.below g) =>
        Real.exp (-(σ * (if g ≤ (F.pt (q : XiZeroCopy)).re then (F.pt (q : XiZeroCopy)).re
          else H)))) := by
      have : Finite (F.below g) := hfin.to_subtype
      exact Summable.of_finite
    have h2 : Summable (fun q : ((F.below g)ᶜ : Set XiZeroCopy) =>
        Real.exp (-(σ * (if g ≤ (F.pt (q : XiZeroCopy)).re then (F.pt (q : XiZeroCopy)).re
          else H)))) := by
      refine ((F.summable_weight hσ).subtype _).congr fun q => ?_
      have hq : ¬ ((F.pt (q : XiZeroCopy)).re < g) := q.2
      rw [if_pos (not_lt.mp hq)]
      rfl
    exact summable_subtype_and_compl.mp ⟨h1, h2⟩
  shell_finite := by
    intro R
    classical
    refine Set.Finite.subset ((F.shell_finite R).union (F.finite_below g)) ?_
    intro q hq
    by_cases h : g ≤ (F.pt q).re
    · left
      simpa [h] using hq
    · right
      exact not_le.mp h
  conj_stable := by
    intro q
    have hre : (F.pt (xiZeroCopyLineConjEquiv q)).re = (F.pt q).re := by
      rw [F.conj_stable, Complex.conj_re]
    by_cases h : g ≤ (F.pt q).re
    · rw [if_pos (hre ▸ h), if_pos h, F.conj_stable]
    · rw [if_neg (by rw [hre]; exact h), if_neg h, Complex.conj_ofReal]

end

end SpectralFamily

end RHTower
