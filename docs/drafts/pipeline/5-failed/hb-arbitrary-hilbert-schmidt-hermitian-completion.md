# HB arbitrary Hilbert--Schmidt Hermitian completion

- **ID:** HB-HS-HERMITIAN-COMPLETION
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** Forced tilted reduced Teukolsky angular leakage can be absorbed into an arbitrary self-adjoint Hilbert--Schmidt carrier while preserving both exact source coefficient and holomorphic source determinant.

## Exact killing theorem

`d4HBReducedTeukolskyArbitraryHermitianCompletionFidelityRouteKilled` proves the route impossible for every carrier type, every self-adjoint Hilbert--Schmidt kernel, arbitrary finite- or infinite-rank auxiliary sectors, and arbitrary extra counterterms. One exact off-diagonal source entry already forces energy at least `2|c|²`, while determinant fidelity forces energy exactly `|c|²`; tilted source incidence gives `c != 0`.

## RH proof chain closed by this no-go

Exact reduced Einstein quadratic source -> doubled-grade chiral Teukolsky coefficient -> proposed conservative angular completion -> proposed determinant fidelity -> HB source darkness -> exact nonzero-factor transmutation to FZZ-P information equilibrium, every PW-B recoil balance, and RBH multiplicity-leading balance -> shared Ward endpoint -> RH.

The no-go kills completion-to-fidelity producer before RH endpoint: no Xi conclusion is assumed.

## Strongest positive survivor

Sharp representation boundary:

`source-faithful + self-adjoint + Hilbert--Schmidt + determinant-faithful => source=0`.

Thus viable survivor must abandon at least one of self-adjointness, Hilbert--Schmidt/Fredholm regularity, coefficient fidelity, or determinant fidelity. Locality, dimension, canonical block form, and counterterm choice are no longer loopholes.

## Status

- Paper proof: dependency-closed
- Lean: `ThetaCuspHawkingHBArbitraryHilbertSchmidtHermitianCompletionFidelityNoGo.lean`
- Closed capstone: premise-free and contains no forbidden declarations
- Targeted build: PASS
- Frontier map: intentionally unchanged/read-only
