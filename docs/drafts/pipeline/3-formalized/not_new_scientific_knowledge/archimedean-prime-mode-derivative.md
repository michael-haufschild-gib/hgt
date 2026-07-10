# Archimedean prime-mode derivative

- **ID:** archimedean-prime-mode-derivative
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), split from `../2-fully-proven/archimedean-generator-axis-mode.md`
- **Priority:** FOUNDATIONAL
- **Source:** finite-support prime-side part of the `∂_s e_m = -(m·ell)e_m` formula
- **Statement:** For a finite integer prime Fourier mode `m`, define `m·ell = sum_p m_p log p` and `e_m(s)=exp(-s(m·ell))`. Then `d/ds e_m(s) = -(m·ell)e_m(s)`.

## Paper Proof

The mode is the exponential function
`e_m(s)=exp(-sL)` with `L=m·ell=sum_p m_p log p`, a finite sum because `m` has finite support.
The derivative of the affine map `s |-> -sL` is `-L`. By the chain rule for the complex exponential,

`d/ds exp(-sL) = exp(-sL) * (-L) = -L * exp(-sL)`.

Substituting `L=m·ell` gives the claimed diagonal archimedean-generator action
`∂_s e_m = -(m·ell)e_m`.

## Lean Certificate

- Lean definitions: `primeLogFrequencyComplex`, `archimedeanPrimeMode`
- Lean theorem: `GaloisForLFunctions.deriv_archimedeanPrimeMode`
- File: `formal/GaloisForLFunctions/ArchimedeanAxisMode.lean`
- Scope: finite-support integer prime modes only. This does not formalize the infinite torus, the completed `(sigma, partial_s)` connection, the Gamma/digamma residue, or the C5-localization synthesis in the parent card.

Verification:

```bash
cd formal && lake env lean GaloisForLFunctions/ArchimedeanAxisMode.lean
cd formal && lake build GaloisForLFunctions
bash scripts/check_axioms.sh
```

## Gates

- [x] 0 -> 1 in-progress: finite-support prime-mode derivative isolated from the archimedean generator card.
- [x] 1 -> 2 fully-proven: paper proof above by the exponential chain rule.
- [x] 2 -> 3 formalized: Lean theorem `deriv_archimedeanPrimeMode`, imported by `GaloisForLFunctions`, included in the axiom audit.
- [ ] 3 -> 4 publication-ready: include as the formal finite-mode derivative anchor for the archimedean generator note.

## Log

- 2026-06-19 — Leaner added the finite-support integer-mode derivative theorem in `ArchimedeanAxisMode.lean` and created this synced split ticket. Parent `archimedean-generator-axis-mode.md` remains in `2-fully-proven` until the full infinite-torus/generator/digamma/C5-localization theorem is formalized.
