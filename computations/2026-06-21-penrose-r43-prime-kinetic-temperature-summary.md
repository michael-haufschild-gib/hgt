# R43 - prime kinetic temperature failure

Status: dead end / reduces to existing phase-carrier and completion-equalization results.

Random source chain:
- seed RandomNode: volume contraction is given by the sum of Lyapunov exponents over the relevant tangent subspace
- broad topic RNG: 15, thermostatted dynamical systems
- NODE RNG: 13, temperature definitions based only on kinetic energy can fail for constrained, driven, or small systems
- target-file RNG: 3, `docs/consolidated/01-landscape-and-weld-geometry.md`
- target-topic RNG: 11, `universal-prime-side-orthogonality`
- scientific-method RNG: 19, fake proof
- perturbation-method RNG: 9, small cases

## Transfer

The natural transfer is:

```text
prime-only scalar amplitude = kinetic temperature
archimedean completion = hidden thermostat / constraint variable
completed transport = true constrained temperature
```

With

```text
P = zeta'/zeta
A = d/ds log(0.5*s*(s-1)*pi^{-s/2} Gamma(s/2))
H = A + P = xi'/xi
```

the exact identity is

```text
|H|^2 - |P|^2 = |A|^2 + 2 Re(A conj(P)).
```

So a prime-only kinetic temperature cannot determine completed transport
unless the hidden archimedean phase/work term is supplied.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r43-prime-kinetic-temperature.py
```

Main-window lane medians:

```text
sigma=0.3: kin=2.675133, completed=1.831201, median_hidden=-8.734642
sigma=0.5: kin=2.153640, completed=1.702111, median_hidden=-2.474810
sigma=0.7: kin=1.493187, completed=1.831201, median_hidden= 2.137271
sigma=1.2: kin=0.279554, completed=1.730969, median_hidden= 4.214241
```

Kinetic-matched cross-lane pairs can have large completed-energy spread:

```text
sigma=0.3,t=507.179: kin=2.350366, comp=0.469055, cos(A,P)=-0.997
sigma=0.7,t=512.564: kin=2.353338, comp=3.413957, cos(A,P)= 1.000
completed spread=2.944902
```

Small cases show the same mechanism:

```text
sigma=0.7,t=52.647: kin=1.662987, comp=2.383797, cos(A,P)= 0.721
sigma=0.3,t=50.441: kin=1.663532, comp=0.495314, cos(A,P)=-0.995
completed spread=1.888484
```

## Verdict

The fake proof "prime-side kinetic energy is enough" fails, but the failure is
not a new non-reducing result. It is the already-known weld phase-carrier
identity in energy language:

```text
completed energy = prime energy + archimedean work + phase interference.
```

The mirror-lane median equalization also overlaps the earlier Berry
completion/equalization result. This is a useful instrument warning:
Source-B-only scalar amplitude is a bad temperature for the completed object,
but the mathematical content reduces to existing phase-cancellation and
universal prime-side orthogonality.
