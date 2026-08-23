# Theta-cusp Hawking Bogoliubov Born endpoint (2026-08-23)

## New exact endpoint

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovBornEndpoint.lean`

Use standard 1+1 moving-mirror coefficient
[
β_{ωω'}[f]=-(4π√{ωω'})^{-1}int e^{-iω'v-iωf(v)}(ωf'(v)-ω'),dv.
]
Perturb inertial ray by literal source `f_λ(v)=v+λ thetaCuspFullSource(v)`. First variation numerator is the unsquared complex Born response
[
int e^{-i(ω+ω')v}{ωk'(v)-iω(ω-ω')k(v)},dv.
]
Fourier integration by parts plus existing theta transform yields, unconditionally,
[
BornRaw(ω,ω')=2iωω'XiC(ω+ω').
]
For balanced modes, including standard prefactor, entire continuation is
[
B_θ(z)=-izXiC(z)/(4π).
]
The kinematic zero z=0 is real. Therefore:
[
RH \iff \forall z, B_θ(z)=0 \Rightarrow Im(z)=0.
]
Lean theorem:
`riemannHypothesis_iff_thetaCuspHawkingBornDarkFrequenciesPhysical`.

## Why Hawking is structural

This endpoint derives from actual moving-mirror Bogoliubov first variation, derivative term, Fourier integration by parts, and balanced mode prefactor. It retains complex β before norm-square, so avoids KMS/intensity phase blindness. It is not the previous theta line-bound criterion under a Hawking name.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovBornEndpoint.lean`: pass.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint reaches unrelated pre-existing umbrella error: `GaussianHermitianPencilSpectralActionLaw` unreachable from `GaloisForLFunctions.RHTower`.

## Honest frontier

Endpoint is exact but not an RH proof. Next source-specific theorem must show `B_θ` is minimum-phase / has no upper-half-plane dark frequencies from a genuine causal symplectic realization. Generic moving-mirror causality or passivity does not imply this; theta structure must do the work.