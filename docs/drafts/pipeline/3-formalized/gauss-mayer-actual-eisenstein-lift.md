# Actual Eisenstein lift of the canonical Mayer period

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–3.

## Exact result

The independently defined Eisenstein Fourier model and rectangular
Epstein completion have the exact normalization:

```text
E*((w−1)/2, ia) = a^(w/2) Λ_a(w/2)/2,
```

for `a>0`, `Re w>0`, `Im w>0`. Consequently its height restriction
`a^(−w/2) E*((w−1)/2,ia)/Γ_R(w)` is the actual `epsteinField w a`,
whose absolutely convergent Cauchy transform is the actual Mayer period.

## Proof

In `Re w>2`, split nonzero lattice pairs by their positive gcd. Homogeneity
extracts `ζ(w)` and leaves the primitive Poincaré sum. The independently
proved Poincaré-to-Fourier identity supplies the completed Eisenstein model.
Continue both sides through `Re w>0`, `Im w>0`, using their proved
holomorphy. Then apply the certified continued Epstein-to-Mayer integral.
No division by `ζ(w)` occurs, so the identification must hold at its zeros.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerEisensteinLift.lean`, namespace
`MayerEisensteinLift`: `eisenstein_eq_epstein_source` proves the actual
source equality; `eisenstein_eq_epstein` continues it;
`eisensteinField_eq_epsteinField` identifies the normalized fields.
`cauchyKernel_eisenstein_integrable` and `cauchyKernel_eisenstein_period`
certify absolute convergence and the actual Mayer image. All five passed
the direct production check with only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms.

## Existing input and boundary

The actual truncated Maass–Selberg pairing and resonant partner-angle law
already exist in the corpus. The source connection to the actual Mayer period is now certified. It does not by itself classify every Mayer
eigenfunction, construct a form on the full eigenspace, or force partner
saturation.
