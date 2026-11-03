# The global source Hecke eigenvalue of the Lewis period

- **ID:** f2-global-lewis-hecke-eigenvalue
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** F2; `MayerScattering/LewisHeckeEisensteinEigenvalue.lean`.
- **Statement:** The actual completed Eisenstein Lewis period is an eigenfunction of the four source Hecke branches throughout `0<Re s<1/2`, on every `a>0`.

## Theorem

Let `E_s` denote `eisensteinLewisPeriod s`. Then

`E_s(2a)+2^(−2s)E_s(a/2)+2^(−2s)E_s((a+1)/2)`
`+(a+1)^(−2s)E_s(2a/(a+1))=(1+2·2^(−2s))E_s(a)`.

Moreover `E_s(1)=2ζ(2s−1)≠0`. At every Mayer resonance, `E_s` equals the actual resonant Lewis period, giving the same eigen-equation. The spectral scalar is derived from the source, not supplied as a premise.

## Proof

For `a∈[1,3/2]`, all four branch arguments lie in the original period segment `[1/2,7/2]`. In `Re w>2`, the disc period equals the convergent Barnes boundary period. The [Barnes cone identity](f2-barnes-hecke-source-identity.md) gives eigenvalue `1+2·2^(−w)`.

The pole-cleared state `(w−2)state(w)` is holomorphic on `Re w>0`. Continuous evaluation at each of the five fixed disc points gives a holomorphic pole-cleared Hecke defect. This defect vanishes in the absolute chamber, hence throughout the connected half-plane. Dividing by `w−2` continues the original period identity to every regular parameter.

For `a∈(1,3/2)`, the branch arguments lie strictly inside the period segment; the global extension agrees there with the disc representative. The global Eisenstein period is holomorphic on the positive complex half-plane. Its real restriction, each positive rational branch, and the Hecke weight are real analytic on `(0,∞)`. The resulting Hecke defect vanishes on `(1,3/2)`, so the real-analytic identity theorem extends it to all positive arguments.

The state value at zero gives `E_s(1)=2ζ(2s−1)`. The shifted zeta factor is nonzero when `0<Re(2s)<1`. At resonance, the forcing term `−ζ(2s)` vanishes, identifying the Eisenstein and resonant global extensions.

## Lean

- `periodValue_hecke_absolute`
- `periodValue_hecke`
- `eisensteinLewisPeriod_hecke`
- `resonantLewisPeriod_hecke`
- `eisensteinLewisPeriod_one_eq`, `eisensteinLewisPeriod_one_ne_zero`

Final check: `lake --old env lean GaloisForLFunctions/RenormalizedIntersectionTheory/MayerScattering/LewisHeckeEisensteinEigenvalue.lean`.
All audited endpoints use only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.

## Scope

The theorem concerns completed periods. PM's finite-energy core subtracts scattering boundary terms, whose Hecke defect must be retained. The eigen-equation alone supplies no positivity.
