# PM actual boundary kernel

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusBoundaryKernel.lean`.
- **Frontier effect:** proves the negative boundary-jet limit of the actual moving kernel. Full prime-convolution identification, rough inversion and complete signed energy compensation remain separate obligations.

## Results

For every `0<epsilon<1/2`, some `C>=0` satisfies, eventually in real `H`,
uniformly for `L>=2*log(H)`,

`|L^2*integral_1^H Re(w_epsilon(x))/(L-log(x)) dx+Re(D_epsilon)|`
` <= C*(L/log(H)^3+1/log(H)+1/L)`.

Consequently, as real `s` tends to infinity,

`s^10*integral_1^exp(s^2) Re(w_epsilon(x))/(s^5-log(x)) dx`
` -> -Re(D_epsilon)`.

Here `w_epsilon` and `D_epsilon` are the literal PM boundary weight and jet.
No square-integrability, RH, source-sign or prime-sum premise is used.

## Proof

Write `z=log(x)`. The exact identity
`L^2/(L-z)=L+z+z^2/(L-z)` decomposes the integral. The zero total mass and
the audited quantitative mass tail bound its zeroth-moment term by
`C*L/log(H)^3`. The full first moment is `-Re(D_epsilon)`; its omitted
tail is bounded by `M2/log(H)`, where `M2` is the finite second absolute
logarithmic moment. On `1<x<=H` the denominator is at least `L/2`, so the
remainder is at most `2*M2/L`. These three bounds prove the estimate.
For `L=s^5,H=exp(s^2)`, the errors tend to zero as `1/s,1/s^2,1/s^5`.

## Audit

- Scratch proof and limit passed.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusBoundaryKernel:olean` passed; only this leaf was newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusBoundaryKernel.lean` passed with empty output.
- `/tmp` audit of both exports reports only `propext`, `Classical.choice`, `Quot.sound`.
- Wired once into RHTower; no umbrella build.
- Index passed and both exports appear in `formal/LEAN_API.md`.
- Global lint reports twelve unrelated unreachable modules, no PM failure; not a global lint pass.
- No numerical experiments, added axioms, placeholders, heartbeat increases, commits or pushes.

## Remaining hard problem

The exact signed prime-head transfer and density-preserving prime tail must
now be combined with this kernel theorem to identify the complete prime
convolution uniformly at square-root lower cutoffs. That term must then be
combined with the finite rough inverse and its semiprime sector, including
prime squares. Complete signed prime-update compensation remains open.
