import GaloisForLFunctions.RHTower.EstermannGrowth
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# The entire completion of Estermann's zeta function

`D(·, a/q)` is holomorphic off `s = 1` with a double pole there, so `(s-1)² D(s, a/q)` is entire.
Writing it out through the polar decomposition replaces the two `ζ` factors by `zetaEntire`, and the
remaining `(s-1)` factors are absorbed by the two entire parts:

```text
(s-1)² D(s, a/q) = q^{-s} ( ζ₀(s)² + ζ₀(s)·(s-1)G_a(s) + (s-1)² R_a(s) ),   ζ₀(s) = (s-1)ζ(s).
```

This is the function a contour shift moves across the critical strip.
-/

open Complex

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The entire completion `(s-1)² D(s, a/q)`. -/
def estermannEntire (q : ℕ) [NeZero q] (a : ZMod q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) *
    (zetaEntire s ^ (2 : ℕ) + zetaEntire s * ((s - 1) * estermannCharSum q a s)
      + (s - 1) ^ (2 : ℕ) * estermannRegularPart q a s)

/-- **The completion is entire.** -/
theorem differentiable_estermannEntire (a : (ZMod q)ˣ) :
    Differentiable ℂ (estermannEntire q ((a : ZMod q))) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  unfold estermannEntire
  refine (differentiable_const_cpow_neg hq0).mul ?_
  refine Differentiable.add (Differentiable.add ?_ ?_) ?_
  · exact (differentiable_zetaEntire.pow 2)
  · exact differentiable_zetaEntire.mul
      ((differentiable_id.sub (differentiable_const 1)).mul (differentiable_estermannCharSum a))
  · exact ((differentiable_id.sub (differentiable_const 1)).pow 2).mul
      (differentiable_estermannRegularPart a)

/-- **The completion computes `(s-1)² D`.** -/
theorem estermannEntire_eq (a : ZMod q) {s : ℂ} (hs : s ≠ 1) :
    estermannEntire q a s = (s - 1) ^ (2 : ℕ) * estermannZeta q a s := by
  rw [estermannZeta_eq_polar_add_regular, estermannEntire, zetaEntire_eq hs]
  ring

end

end RHTower
