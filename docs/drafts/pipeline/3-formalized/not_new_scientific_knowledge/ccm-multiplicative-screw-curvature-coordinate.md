# The rectangular screw detector is a multiplicative midpoint curvature

- **ID:** `ccm-multiplicative-screw-curvature-coordinate`
- **Stage:** 3-formalized
- **Type:** THEOREM / COORDINATE GLUE
- **Scientific status:** `[PROVED IN LEAN] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMMultiplicativeScrewCurvature.lean`

Fix positive integers `m,n`.  For width `L=log m`, the fixed screw
curvature at `x=log(m^2 n)` is

```text
2[Psi(log(m^2 n))+Psi(log n)-2Psi(log(mn))+2Psi(log m)],
```

where `Psi=xiScrewDivisor`.  The same expression is exactly the
rectangular Xi-Weil value at aperture `log(m^2 n)/2`.

The result is an algebraic specialization of the formal screw-curvature
identity and the laws `log(mn)=log m+log n`.  Its value is architectural:
it exposes the source theorem as a multiplicative covariance or
conditional-negative-type problem on the integer triple `n,mn,m^2n`.
It does not prove a lower bound for that curvature and therefore does not
prove RH.

Lean declarations:

- `xiScrewWindowCurvature_log_mul_sq`
- `xiWeilPolarization_rectangular_log_mul_sq_eq_screwCurvature`

The focused module build passes.

