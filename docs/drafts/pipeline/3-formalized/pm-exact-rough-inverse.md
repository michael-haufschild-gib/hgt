# PM exact rough-factor inverse

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRoughInverse.lean`.
- **Frontier effect:** connects the actual finite-prime core to the actual full source through every positive rough dilation, including prime powers. Square-scale decomposition and signed energy compensation remain open.

## Exact theorem

For every finite set `S` of primes, every real `epsilon`, and every `t>0`,

`F_S,epsilon(t) = sum_(1<=m<=floor(1/t)) r_S(m)*m^(-epsilon)*A_epsilon(m*t)`.

Here `r_S(m)` is the existing `smoothAF(complement(S))` indicator: `m` is
positive and all its prime factors lie outside `S`. The theorem uses the
literal finite-prime Fermi source and literal full PM source, with no
convergence, RH or L2-admission premise.

## Proof

The existing divisor identity is `mobiusAF(E)*zeta=smoothAF(E)`.
Multiplication by Möbius gives `smoothAF(E)*mu=mobiusAF(E)`. At
`E=complement(S)`, the right-hand coefficient is exactly the finite-prime
aperture coefficient. Expand each source in its finite Fermi sum. The
generator identity `G_d(m*t)=G_(m*d)(t)` and complete multiplicativity of
`n^(-epsilon)` combine its weights. Finite divisor-antidiagonal interchange
then yields precisely the integer convolution. No infinite rearrangement
or squarefree restriction of the rough indicator occurs.

## Audit

- Scratch proof and targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusRoughInverse:olean` passed; only this leaf was newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusRoughInverse.lean` passed with empty output.
- `/tmp` axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.
- Wired once into RHTower; no umbrella build.
- Index passed; the export appears in `formal/LEAN_API.md`.
- Global lint reports twelve unrelated unreachable modules, no PM failure; not a global lint pass.
- No numerical experiment, added axiom, placeholder, heartbeat increase, commit or push.

## Next hard step

At `P^2<=X<2*P^2`, specialize the rough sum to `1`, primes at least `P`,
and products of two primes at least `P`, including equal factors. The
audited first-band source equals one on the semiprime terms. A sharp
unordered-pair bound and the audited negative prime-convolution asymptotic
must then be combined uniformly in `X/P^2` to establish the core sign.
