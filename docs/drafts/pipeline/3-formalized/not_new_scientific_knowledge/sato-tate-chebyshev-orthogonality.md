# Sato-Tate Chebyshev orthogonality

- **ID:** sato-tate-chebyshev-orthogonality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/g4-over-fq-deligne-katz.md` §1 and the `function-field-native-reproof` G4/Sato-Tate angle face; Lean file `formal/GaloisForLFunctions/SatoTateMoment.lean`
- **Statement:** The Chebyshev symmetric-power characters are orthonormal for the Sato-Tate measure `(2/pi) sin^2(theta) dtheta` on `[0,pi]`; in particular every nonzero Chebyshev moment vanishes.

## Goal
This banks the exact measure-side target behind the G4 angle/Katz-Sarnak statement: the Sato-Tate distribution has vanishing higher symmetric-power moments. It does not formalize Katz-Sarnak equidistribution, Deligne-Katz monodromy, analytic continuation/nonvanishing of symmetric-power `L`-functions, prime averages, or the Tannakian weight/angle exact sequence.

## Paper Proof
For integer frequencies,
```
int_0^pi cos(j theta) dtheta = pi   if j = 0,
                                  0 if j > 0.
```
Using the product-to-sum identity,
```
sin(m theta) sin(n theta)
  = (cos((m-n) theta) - cos((m+n) theta)) / 2,
```
this gives
```
int_0^pi sin(m theta) sin(n theta) dtheta
  = pi/2   if m = n,
    0      otherwise
```
for `m,n >= 1`.

The Chebyshev identity
```
U_k(cos theta) sin theta = sin((k+1) theta)
```
then converts the Sato-Tate inner product to the sine orthogonality integral:
```
int_0^pi U_j(cos theta) U_k(cos theta) (2/pi) sin^2(theta) dtheta
  = delta_{j,k}.
```
Taking `j=0` gives the moment formula
```
int_0^pi U_k(cos theta) (2/pi) sin^2(theta) dtheta
  = delta_{k,0}.
```

## Gates
- [x] 0 -> 1  in-progress: exact Sato-Tate measure-side orthogonality extracted from the G4 angle face.
- [x] 1 -> 2  fully-proven: paper proof above, by elementary trigonometric orthogonality and the Chebyshev `U_k(cos theta)` identity.
- [x] 2 -> 3  formalized: Lean theorems `integral_cos_nat_mul`, `integral_sin_succ_mul_sin`, `satoTate_moment`, `integral_sin_mul_sin`, and `satoTate_orthonormal`; names checked by scratch file; `#print axioms` reports only standard mathlib axioms.
- [ ] 3 -> 4  publication-ready: cite as the formal measure-side certificate for the function-field G4/Sato-Tate angle target.

## Log
- 2026-06-19 — Leaner split this exact Sato-Tate measure orthogonality lemma from the broader G4-over-`F_q` angle/Katz-Sarnak card. The parent card remains in `2-fully-proven` because Deligne-Katz monodromy, prime equidistribution, and the Tannakian weight/angle exact sequence are not fully Lean-formalized.
