# Exact nonlinear-boundary quotient through the seam

- **ID:** tt-exact-nonlinear-boundary-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/tt-third-slope-nonlinear-cone.md · Route TT
- **Statement:** The complete nonlinear-boundary core has its forced drift factor as a polynomial. Its quotient equals the full reduced source slope times `h^16`, including on `V=0`.

## Paper proof [PROVED HERE]

Use the established exact boundary parametrization
`b=1/12-7h/72`, `R=s*(1-h^2*b*s)`, `T=b*s`,
`V=9-h^2*R`, `Z=(1-h*T)/3`.
The complete boundary core `C` obeys `Q(h,R,T)=h^3*C` and
`h^16*S(V,h⁻¹,Z)=C` for nonzero `h`.

Represent every substitution in `MvPolynomial Coord ℂ`. Pulling back the
proved factorization `Q=(9-r*h^2)*reducedScaledSlope` shows `V ∣ h^3*C`.
The Bezout identity

`(1/9)*V + ((1/9)*R*h)*h = 1`

makes `V` coprime to `h`. Hence `V ∣ C`, giving a polynomial `D` with
`C=V*D`. No pointwise division by `V` is performed.

To identify `D` on the seam, regularize the full source `reducedSlope`:
for some natural `n` and polynomial `Q₀`,
`h^n*reducedSlope(sourcePoint(h,r,t))=Q₀(h,r,t)` when `h≠0`.
Pull back `Q₀` to the exact boundary. The full source identities imply
the polynomial equality

`V*h^n*D = V*h^16*Q₀(h,R,T)`.

Polynomial extensionality away from `h=0` suffices for this equality.
Since `V` is a nonzero polynomial (its clock-zero value is `9`), cancel
`V` in the polynomial ring. Evaluate and cancel `h^n` for `h≠0`:

`D(h,s)=h^16*reducedSlope(V,h⁻¹,Z)`.

This identity includes `V=0`. Finally, evaluation of `C=V*D` at `h=0`
gives `D(0,s)=216*axisMinorMass-7*principalMass*s^2`.
All derivatives remain those of the original complete source slope.

## Lean and audit

- `ThetaCuspRatioNonlinearBoundaryPolynomial.lean`: polynomial pullback,
  Bezout identity, exact drift divisibility and factorization.
- `ThetaCuspRatioNonlinearBoundaryQuotient.lean`: full reduced source
  incidence including the seam and exact clock-zero value.
- Both leaves passed direct `lake --old env lean` audits and are wired
  into `GaloisForLFunctions/RHTower.lean`; no full or umbrella build.
- Six imported capstones passed `/tmp/tt_c76_production_axioms.lean`:
  only `propext`, `Classical.choice`, `Quot.sound`.

## Open hard problem

Prove positivity of the complete quotient on the physical boundary
domain, then prove the interior/transverse third-slope sign. Positivity
on the enclosing bounded `(h,s)` rectangle is a stronger live conjecture,
not an established fact. The full source quadratic, fourth Schur gap,
join, all-rank closure and RH remain open.

## Log

- 2026-10-04 — Exact factor and seam-inclusive source quotient formalized.
