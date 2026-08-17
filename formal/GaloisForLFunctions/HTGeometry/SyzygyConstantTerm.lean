import Mathlib

/-!
# The constant term of the second entry of a syzygy

A syzygy `U Y + X V ≡ 0 mod t^L` with `L ≥ 1` forces its degree-zero part to vanish,

```text
U(0) Y(0) + X(0) V(0) = 0 ,
```

so over a domain the constant term of `V` cannot vanish once those of `U` and `Y` are nonzero: if it
did, the second product would drop out and the first would have to vanish as well.  Note that no
hypothesis on `X` is needed — the argument runs entirely on the first product.

This is how a nonvanishing leading coordinate on one side of a tangent pair propagates to the other
side.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [CommRing K]

/-- The degree-zero part of a syzygy modulo `t^L`. -/
theorem syzygy_coeff_zero {U V X Y : K[X]} {L : ℕ} (hL : 0 < L)
    (hsyz : (Polynomial.X ^ L : K[X]) ∣ (U * Y + X * V)) :
    U.coeff 0 * Y.coeff 0 + X.coeff 0 * V.coeff 0 = 0 := by
  have h := (Polynomial.X_pow_dvd_iff.1 hsyz) 0 hL
  rwa [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero] at h

/-- **The constant term of `V` is nonzero.** -/
theorem syzygy_coeff_zero_ne_zero [IsDomain K] {U V X Y : K[X]} {L : ℕ} (hL : 0 < L)
    (hsyz : (Polynomial.X ^ L : K[X]) ∣ (U * Y + X * V))
    (hU : U.coeff 0 ≠ 0) (hY : Y.coeff 0 ≠ 0) :
    V.coeff 0 ≠ 0 := by
  intro hV
  have h := syzygy_coeff_zero hL hsyz
  rw [hV, mul_zero, add_zero] at h
  exact (mul_ne_zero hU hY) h

end GaloisForLFunctions.HTGeometry

end
