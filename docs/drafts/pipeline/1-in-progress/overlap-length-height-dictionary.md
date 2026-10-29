# Overlap, polynomial length, height, and the complete Weil form

- **ID:** overlap-length-height-dictionary
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; walls, route-obstacles, and route-unification ledgers.
- **Statement:** Identify atomic overlap with length divided by spectral height, with exact normalization, and transport the corpus's actual threshold and completeness theorems through this dictionary.

## Goal

Formalize the dictionary and its consequences without importing any unproved positivity,
prime-correlation estimate, or completeness assumption. Audit each inference against the current
Lean source. Retain the full prime, Gamma, and polar terms. Continue the conjecture loop from
each success or obstruction.

## Gates

- [x] 0 → 1: well-posed source comparison; existing transform factorization located.
- [ ] 1 → 2: dependency-closed paper arguments for each proposed extension.
- [ ] 2 → 3: individual `lake --old env lean` audits, transitive `#print axioms`, umbrella imports.

## Current evidence

`SpacingScaleHarmonicAnalysis/TheAtomicFamilyIsADirichletPolynomial.lean` already proves
`paperFT_atomicTest` and the complete zero-side summand factorization. Its convention is
`h_f(z) = ∫ f(u) exp(i z u) du`, `D_x(z) = Σ x_n exp(i z log n)`.

The literal formula in §1.3 omits the dilation Jacobian for unnormalized bumps. Calling the
Fourier window a cutoff must mean a scale of decay, not compact frequency support. A conventional
Dirichlet polynomial needs a coefficient reweighting and a sign change in the frequency.
The identity `N = T c_N` is exact; replacing the argument `N` in `c_N` by `T` needs an asymptotic
proof. Equal scale coordinates do not identify distinct quadratic forms or their quantifiers.

## Conjecture loop

1. Exact Fourier normalization and reciprocal height dictionary.
2. Exact bandwidth/aperture/overlap threshold identities using the existing definitions.
3. Transport actual complete-form positivity and the RH-complete receiver into height coordinates.
4. Audit successor-shell support and sign claims; extract stronger exact laws if the prose fails.
5. Derive schedule and census consequences; separate coordinate identities from new analytic inputs.

## No-go closure

No route retired. Possible inaccuracies in the report are under source audit; any refuted
statement will be paired with its strongest proved replacement.

## Log

- 2026-10-29 — Read requested report and supporting ledgers; first corpus searches located existing
  transform factorization and dilation law. Existing unrelated working-tree changes preserved.
