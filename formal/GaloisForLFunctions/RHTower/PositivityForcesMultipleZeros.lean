import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.NoObstructionOnlyAConstruction

/-!
# De Branges positivity forces every off-line zero to be multiple

The Hedenmalm seam builds the candidate `E = XiC + i XiC'` and leaves its Bezoutian positivity as
the RH-bearing condition, separately isolating a multiplicity obstruction.  This file shows the two
are not independent: positivity alone already collapses the off-line case to the degenerate one.

**The kernel at a zero.**  Writing `A = XiC` and `B = -XiC'`, the de Branges numerator is

```text
N(w, z)  =  B z · conj (A w)  -  A z · conj (B w) .
```

At a zero `ρ` of `XiC` both terms carry a factor `A ρ = 0` or `conj (A ρ) = 0`, so `N(ρ, ρ) = 0`.

**A vanishing diagonal kills its row.**  For a positive semidefinite two-by-two block with a zero
diagonal entry, the determinant condition forces the off-diagonal entry to vanish.  So `N(w, ρ) = 0`
for every `w`.

**And that is a multiple zero.**  With `A ρ = 0` the surviving term is `B ρ · conj (A w)`, so
`N(w, ρ) = 0` for some `w` with `A w ≠ 0` forces `B ρ = 0`, i.e. `XiC' ρ = 0`.

> **If the Hedenmalm–de Branges kernel is positive semidefinite, every zero at which the kernel's
> diagonal vanishes is a multiple zero of `XiC`.  Positivity therefore disposes of the location
> question outright and leaves only the degenerate case that the seam had already isolated: the two
> obstructions are complementary, not independent.**

Combined with the seam's criterion that the Bezoutian diagonal is nonzero exactly at simple zeros,
this says: **de Branges positivity together with simplicity of the zeros gives the hypothesis.**

This file formalizes the two-by-two positivity step, the vanishing of the numerator at a zero, and the
resulting derivative vanishing.
-/

open Complex

noncomputable section

namespace RHTower

/-- The de Branges numerator attached to a real-entire pair. -/
def dbKernelNum (A B : ℂ → ℂ) (w z : ℂ) : ℂ :=
  B z * (starRingEnd ℂ) (A w) - A z * (starRingEnd ℂ) (B w)

/-- **The numerator vanishes at a common zero.**  If `A ρ = 0` then `N(ρ, ρ) = 0`. -/
theorem dbKernelNum_self_eq_zero {A B : ℂ → ℂ} {ρ : ℂ} (hA : A ρ = 0) :
    dbKernelNum A B ρ ρ = 0 := by
  simp [dbKernelNum, hA]

/-- **A positive semidefinite two-by-two block with a vanishing diagonal entry has a vanishing
off-diagonal entry.**  Testing the form at `(1, -s·conj b)` gives `2 s ‖b‖² ≤ a.re` for every `s ≥ 0`,
which is impossible unless `b = 0`. -/
theorem offDiag_eq_zero_of_psd_diag_zero {a b : ℂ}
    (hpsd : ∀ x y : ℂ, 0 ≤ (a * x * (starRingEnd ℂ) x
      + b * y * (starRingEnd ℂ) x + (starRingEnd ℂ) b * x * (starRingEnd ℂ) y).re) :
    b = 0 := by
  by_contra hb
  have hns : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
  have key : ∀ s : ℝ, 2 * s * Complex.normSq b ≤ a.re := by
    intro s
    have h := hpsd 1 (-(s : ℂ) * (starRingEnd ℂ) b)
    have hval : (a * 1 * (starRingEnd ℂ) 1
        + b * (-(s : ℂ) * (starRingEnd ℂ) b) * (starRingEnd ℂ) 1
        + (starRingEnd ℂ) b * 1 * (starRingEnd ℂ) (-(s : ℂ) * (starRingEnd ℂ) b)).re
        = a.re - 2 * s * Complex.normSq b := by
      simp [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hval] at h
    linarith
  have hbig := key ((|a.re| + 1) / (2 * Complex.normSq b))
  have hsimp : 2 * ((|a.re| + 1) / (2 * Complex.normSq b)) * Complex.normSq b = |a.re| + 1 := by
    field_simp
  rw [hsimp] at hbig
  linarith [le_abs_self a.re]

/-- **The surviving term at a zero.**  The numerator always splits this way; at a zero of `A` the
first summand drops. -/
theorem dbKernelNum_at_zero (A B : ℂ → ℂ) (ρ w : ℂ) :
    dbKernelNum A B w ρ = -(A ρ * (starRingEnd ℂ) (B w)) + B ρ * (starRingEnd ℂ) (A w) := by
  simp [dbKernelNum]
  ring

/-- **Hence a vanishing kernel row forces a multiple zero.**  If the numerator vanishes at some `w`
with `A w ≠ 0`, and `A ρ = 0`, then `B ρ = 0`. -/
theorem multiple_zero_of_row_vanishes {A B : ℂ → ℂ} {ρ w : ℂ}
    (hA : A ρ = 0) (hAw : A w ≠ 0) (hrow : dbKernelNum A B w ρ = 0) :
    B ρ = 0 := by
  rw [dbKernelNum, hA, zero_mul, sub_zero] at hrow
  have hconj : (starRingEnd ℂ) (A w) ≠ 0 := by
    simpa using hAw
  exact (mul_eq_zero.mp hrow).resolve_right hconj

/-- **The statement for the Hedenmalm pair.**  With `A = XiC` and `B = -XiC'`, a vanishing kernel row
at a zero of `XiC` says the zero is multiple. -/
theorem xi_multiple_zero_of_row_vanishes {ρ w : ℂ}
    (hA : XiC ρ = 0) (hAw : XiC w ≠ 0)
    (hrow : dbKernelNum XiC (fun z => -deriv XiC z) w ρ = 0) :
    deriv XiC ρ = 0 := by
  have h := multiple_zero_of_row_vanishes (A := XiC) (B := fun z => -deriv XiC z) hA hAw hrow
  simpa using h

/-- **And the seam's diagonal degenerates there.**  At a zero with vanishing derivative the Bezoutian
diagonal is zero, which the seam identifies with multiplicity above one. -/
theorem bezoutian_diag_zero_of_multiple {ρ : ℂ} (hA : XiC ρ = 0) (hd : deriv XiC ρ = 0) :
    xiHedenmalmBezoutian ρ ρ = 0 := by
  rw [xiHedenmalmBezoutian_self_of_zero hA, hd]
  ring

end RHTower
