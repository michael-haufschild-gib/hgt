# Archimedean Gamma shift and connection compatibility

- **ID:** archimedean-gamma-shift-connection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/gamma-module-construction.md` Result (1)-(2) and
  `../0-backlog-lean/completed-base-archimedean-coordinate.md`
- **Statement:** Deligne's real archimedean Gamma factor satisfies
  `Gamma_R(s+2) = (s/(2*pi)) Gamma_R(s)`, the half-argument digamma recurrence
  `psi(s/2+1)=psi(s/2)+2/s` away from poles, and the resulting logarithmic-connection coefficient is
  compatible with the `s -> s+2` multiplier.

## Goal
This banks the exact scalar archimedean Gamma identities used by the gamma-module construction and completed
base coordinate. It does not formalize the full rank-one `(sigma_infty, d/ds)` module, Lerch's
zeta-regularized determinant import, the completed object `M_Lambda`, or any RH claim.

## Paper Proof
Let `Gamma_R(s) = pi^(-s/2) Gamma(s/2)`. Then
`Gamma_R(s+2) = pi^(-(s+2)/2) Gamma(s/2+1)`.
Using `Gamma(z+1)=z Gamma(z)`, this equals
`pi^(-s/2) pi^(-1) (s/2) Gamma(s/2) = (s/(2*pi)) Gamma_R(s)`.

For the logarithmic derivative, define
`A(s) = -1/2 log pi + 1/2 psi(s/2)`. The digamma recurrence
`psi(z+1)=psi(z)+1/z`, applied to `z=s/2`, gives
`psi(s/2+1)=psi(s/2)+2/s`.

Substituting this identity into `A(s+2)` gives
`A(s+2)=A(s)+1/s`. Multiplying by the Gamma multiplier `s/(2*pi)` yields
`(1/(2*pi)) + (s/(2*pi)) A(s) = (s/(2*pi)) A(s+2)`, the scalar compatibility identity.

## Gates
- [x] 0 -> 1 in-progress: scalar Gamma recurrence and connection identities extracted from the gamma-module
  construction.
- [x] 1 -> 2 fully-proven: paper proof above, using the standard Gamma and digamma recurrences.
- [x] 2 -> 3 formalized: Lean definitions/theorems `gammaRealLogConnection`, `gammaReal_shift_two`,
  `digamma_half_add_one`, and `gammaRealLogConnection_shift_compat` in
  `formal/GaloisForLFunctions/RHTower/ArchimedeanGamma.lean`; names checked by scratch file; `lake build` green;
  `check_axioms.sh` PASS.
- [ ] 3 -> 4 publication-ready: cite as the scalar Gamma recurrence/connection lemma in the gamma-module note.

## Log
- 2026-06-19 — Leaner split this exact scalar theorem from `gamma-module-construction`. The parent card
  remains in `2-fully-proven` because the full rank-one module construction, Lerch inverse determinant import,
  and completed-object wiring are not fully Lean-formalized.
