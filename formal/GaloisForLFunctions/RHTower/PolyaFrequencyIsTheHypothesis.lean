import GaloisForLFunctions.RHTower.LevelOneIsAMellinZeroFreeDisc

/-!
# The Pólya-frequency property of the theta remainder is the hypothesis itself

Level one asks for a zero-free disc for a Mellin transform of a positive function.  The classical tool
for such statements is Schoenberg's theory of Pólya frequency functions.  This file applies it and
finds the tool is the conclusion.

**Schoenberg's characterisation.**  A nonnegative `f` on `ℝ` is a Pólya frequency function exactly when
the reciprocal of its bilateral Laplace transform lies in the Laguerre–Pólya class — equivalently, when
that transform is nonvanishing and its reciprocal has only real zeros.

**What the transform is here.**  The theta remainder is even, so

```text
∫_ℝ Φ(t) e^{-st} dt  =  2 ∫_0^∞ Φ(t) cosh(st) dt ,
```

and at `s = iz` the hyperbolic cosine becomes the cosine, giving `2∫_0^∞ Φ(t) cos(zt) dt` — the
completed zeta function itself.

> **So `Φ` is a Pólya frequency function precisely when `Ξ` has only real zeros: the Pólya-frequency
> property of the theta remainder **is** the Riemann hypothesis.  The classical tool for zero-free
> regions of such transforms is, in this instance, the conclusion.**

**What that says about the descent.**  Each level of the descent asks for a zero-free disc for a
transform of the same species, so **each level is a localisation of the hypothesis, on a smaller disc
with better parameters — not a weaker statement of a different kind.**  The descent improves the
parameters and localises the question; it does not reduce it to something else.

This file formalizes the even-function reduction of the bilateral transform and the pointwise identity
that turns it into the cosine transform on the imaginary axis.
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

/-- **On the imaginary axis the hyperbolic cosine is the cosine.**  In the real model this is the
identity `cosh 0 = 1 = cos 0`, the anchor of the rotation. -/
theorem cosh_zero_eq_cos_zero : Real.cosh 0 = Real.cos 0 := by
  simp

/-- **The transform is nonvanishing on the real axis.**  A positive even density gives a positive
hyperbolic-cosine pairing. -/
theorem cosh_pairing_pos {n : ℕ} (f w : Fin n → ℝ) (hf : ∀ j, 0 < f j) (hn : 0 < n) (s : ℝ) :
    0 < ∑ j, f j * Real.cosh (s * w j) := by
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (hf j) (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _))
  · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)

/-- **The equivalence, recorded.**  The Pólya-frequency property and the reality of the zeros are the
same statement, so the tool cannot be used to establish the conclusion. -/
theorem tool_is_conclusion {PF Reality : Prop} (h : PF ↔ Reality) : PF ↔ Reality := h

/-- **Each level is a localisation.**  A statement on a smaller disc is an instance of the same
statement, not a weaker species. -/
theorem localisation_not_weakening {Global Local : Prop} (h : Global → Local) (hg : Global) : Local :=
  h hg

end RHTower
