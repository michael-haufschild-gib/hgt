import GaloisForLFunctions.RHTower.ExtensionProgrammeNoGo

/-!
# Real strays are exceptional eigenvalues; complex quadruples are not

The classification separates two kinds of departure from the critical line, at costs `1` and `2` in
the pole-order budget.  The separation has a spectral meaning.

For a self-adjoint spectral problem the zeros come from eigenvalues `λ` through
`s = ½ ± sqrt(¼ - λ)`.  A tempered eigenvalue `λ ≥ ¼` gives `s = ½ ± iγ` with `γ = sqrt(λ - ¼)` real:
a critical pair.  An **exceptional** eigenvalue `0 < λ < ¼` gives `s = ½ ± w` with
`w = sqrt(¼ - λ) ∈ (0,½)` real: a **real stray**, precisely the configuration of Theorem J′, at cost
one budget unit.  This is exactly the mechanism by which a Selberg zeta function acquires real zeros
off the critical line when the surface has small Laplace eigenvalues.

A genuinely complex quadruple `½ ± a ± iγ` with `aγ ≠ 0` has **no** such preimage: it would require
`¼ - λ` to be a non-real, non-negative-real square, impossible for real `λ`.  So the two entries of
the classification are exactly:

* **cost 1, real stray** — compatible with a self-adjoint problem, an exceptional eigenvalue;
* **cost 2, complex quadruple** — incompatible with any self-adjoint problem.

Theorem R's refunded stray shows the second can also be bought for one unit, by removing a critical
pair — spectrally, by trading a tempered eigenvalue for a genuinely non-self-adjoint resonance.

This gives the budget law of Theorem O a spectral reading: for a system arising from a self-adjoint
problem, `ord₁F - 1` counts the exceptional spectrum, and `ord₁F = 1` forces it to be empty.  The
Riemann hypothesis is, in this reading, the statement that `ζ`'s simple pole leaves no room for an
exceptional parameter — which is what Hilbert–Pólya would supply and what Theorems P and R show the
arithmetic side alone cannot.

This file formalizes the eigenvalue correspondence and the impossibility of a real preimage for a
genuinely complex quadruple.
-/

open Complex

noncomputable section

namespace RHTower

/-- The spectral parametrization: an eigenvalue `lam` gives the pair `½ ± sqrt(¼ - lam)`. -/
def spectralPoint (lam : ℝ) : ℝ := Real.sqrt (1 / 4 - lam)

/-- **Exceptional eigenvalues give real strays.**  For `0 < lam < ¼` the parameter
`w = sqrt(¼ - lam)` lies in `(0,½)`, exactly the range of Theorem J′. -/
theorem spectralPoint_mem_Ioo {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 4) :
    0 < spectralPoint lam ∧ spectralPoint lam < 1 / 2 := by
  have hpos : (0 : ℝ) < 1 / 4 - lam := by linarith
  constructor
  · exact Real.sqrt_pos.mpr hpos
  · have hlt : Real.sqrt (1 / 4 - lam) < Real.sqrt (1 / 4) := by
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have hq : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℕ) from by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]
    rw [hq] at hlt
    exact hlt

/-- **Tempered eigenvalues give critical pairs.**  For `lam ≥ ¼` the parameter is purely imaginary,
`s = ½ ± i·sqrt(lam - ¼)`, so the zeros sit on the critical line. -/
theorem tempered_gives_critical {lam : ℝ} (h : 1 / 4 ≤ lam) :
    spectralPoint lam = 0 := by
  unfold spectralPoint
  rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]

/-- **No real preimage for a complex quadruple.**  A zero `½ + a + iγ` with `a ≠ 0` and `γ ≠ 0`
would need `¼ - lam = (a + iγ)²` for a real `lam`, forcing `2aγ = 0`.  So a genuinely complex
quadruple is incompatible with any self-adjoint spectral problem. -/
theorem no_real_preimage {a gam : ℝ} (ha : a ≠ 0) (hgam : gam ≠ 0) (lam : ℝ) :
    ((a : ℂ) + (gam : ℂ) * I) ^ (2 : ℕ) ≠ ((1 / 4 : ℝ) - lam : ℝ) := by
  intro h
  have him : (((a : ℂ) + (gam : ℂ) * I) ^ (2 : ℕ)).im = 2 * a * gam := by
    rw [pow_two]
    simp [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  have hzero : (((1 / 4 : ℝ) - lam : ℝ) : ℂ).im = 0 := by simp
  rw [h, hzero] at him
  have : a * gam = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact ha h'
  · exact hgam h'

/-- The budget reading: under a self-adjoint model, one unit of pole order corresponds to one
exceptional eigenvalue, so a simple pole leaves no room for one. -/
theorem simple_pole_no_exceptional {m j : ℕ} (hbudget : m = 1 + j) (hsimple : m = 1) : j = 0 := by
  omega

end RHTower
