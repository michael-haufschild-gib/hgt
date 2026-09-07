import GaloisForLFunctions.RHTower.LevelOneIsAMellinZeroFreeDisc

/-!
# Elementary even pairings and transport of assumed propositions

This file proves a pointwise even exponential pairing, `cosh 0 = cos 0`, positivity of a finite
cosh sum, and two generic logical implications. It does not define Pólya-frequency functions,
formalize Schoenberg's theorem, identify a theta transform, or prove an equivalence with RH.
In particular, `tool_is_conclusion` takes its entire equivalence as a premise.

The former mathematical interpretation confused a transform with its reciprocal. Schoenberg's
characterization concerns the reciprocal of the bilateral Laplace transform of an integrable
Pólya-frequency density; it does not identify that density property with real zeros of its Fourier
transform. See Khare, https://arxiv.org/abs/2008.05121, footnote 3. No conclusion about the
strength of a Mellin descent follows from the generic propositions below.
-/

open Real

noncomputable section

namespace RHTower

/-- **Even reduction.**  For an even integrand the two exponential halves combine into a hyperbolic
cosine. -/
theorem even_pairs_to_cosh {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (s t : ℝ) :
    f t * Real.exp (-(s * t)) + f (-t) * Real.exp (s * t)
      = 2 * f t * Real.cosh (s * t) := by
  rw [hf t, Real.cosh_eq]
  ring

/-- The values of real hyperbolic cosine and cosine agree at zero. -/
theorem cosh_zero_eq_cos_zero : Real.cosh 0 = Real.cos 0 := by
  simp

/-- A nonempty finite sum of positive weights times real hyperbolic cosines is positive. -/
theorem cosh_pairing_pos {n : ℕ} (f w : Fin n → ℝ) (hf : ∀ j, 0 < f j) (hn : 0 < n) (s : ℝ) :
    0 < ∑ j, f j * Real.cosh (s * w j) := by
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (hf j) (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _))
  · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)

/-- Return an assumed equivalence between arbitrary propositions; neither side is instantiated. -/
theorem tool_is_conclusion {PF Reality : Prop} (h : PF ↔ Reality) : PF ↔ Reality := h

/-- Apply an assumed implication to a proof of its antecedent; no converse is proved. -/
theorem localisation_not_weakening {Global Local : Prop} (h : Global → Local) (hg : Global) : Local :=
  h hg

end RHTower
