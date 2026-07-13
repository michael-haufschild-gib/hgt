# Morita gamma finite recurrence

- **ID:** morita-gamma-finite-recurrence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/per-place-source-a-gamma-carriers.md` section 1
- **Statement:** For a prime `p`, the finite positive-integer Morita product
  `Gamma_p(n)=(-1)^n product_{j<n, p not dividing j} j` satisfies
  `Gamma_p(n+1)=-Gamma_p(n)` if `p | n`, and `Gamma_p(n+1)=-n*Gamma_p(n)` otherwise.

## Goal
This banks the exact finite integer recurrence used by the per-place Source-A gamma-carrier card. It does
not formalize p-adic analytic continuation, the Source-A grade, the multiplier dichotomy, the uniform
per-place `Gamma_v` family, or any complex/p-adic comparison.

## Paper Proof
Fix a prime `p` and define

`P_p(n) = product_{j<n, p not dividing j} j`

and

`Gamma_p(n) = (-1)^n P_p(n)`.

Since every prime divides `0`, the condition `j<n` with `p` not dividing `j` is the same finite index set as
`0<j<n` with `p` not dividing `j`.

Passing from `n` to `n+1` adds only the possible new index `j=n`. If `p | n`, that index is excluded, so

`P_p(n+1)=P_p(n)`.

If `p` does not divide `n`, that index is included and contributes the factor `n`, so

`P_p(n+1)=n P_p(n)`.

In both cases the sign changes by `(-1)^(n+1)=-(-1)^n`. Therefore

`Gamma_p(n+1)=-Gamma_p(n)` when `p | n`,

and

`Gamma_p(n+1)=-n Gamma_p(n)` when `p` does not divide `n`.

## Gates
- [x] 0 -> 1  in-progress: finite Morita recurrence split from the per-place Source-A gamma-carrier card.
- [x] 1 -> 2  fully-proven: paper proof above by splitting the new endpoint of a filtered finite product.
- [x] 2 -> 3  formalized: Lean definitions/theorems `moritaGammaProduct`, `moritaGammaFinite`,
  `moritaGammaProduct_succ_of_dvd`, `moritaGammaProduct_succ_of_not_dvd`,
  `moritaGammaFinite_succ_of_dvd`, `moritaGammaFinite_succ_of_not_dvd`, and
  `moritaGammaFinite_succ` in `formal/GaloisForLFunctions/HTGeometry/MoritaGamma.lean`; scratch `#check` /
  `#print axioms`, `lake build`, and `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the finite Morita recurrence inside the
  per-place gamma-carrier exposition.

## Log
- 2026-06-19 - Leaner split this exact finite recurrence from
  `per-place-source-a-gamma-carriers` section 1. The parent card remains in `2-fully-proven` because the
  p-adic analytic continuation, Source-A grade, multiplier-dichotomy application, uniform per-place family,
  and complex/p-adic comparison are not fully Lean-formalized.
