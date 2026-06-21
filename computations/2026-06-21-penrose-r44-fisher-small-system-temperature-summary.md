# R44 - finite-system temperature ambiguity at the Fisher wall

Status: dead end / reducible finite-regularization warning.

Random source chain:
- seed RandomNode: temperature definitions based only on kinetic energy can fail for constrained, driven, or small systems
- broad topic RNG: 8, thermodynamics of small systems
- NODE RNG: 2, temperature is not always a sharply defined state variable for a small nonequilibrium system
- target-file RNG: 2, `docs/consolidated/01-landscape-and-geometry.md`
- target-topic RNG: 17, Fisher signature wall
- scientific-method RNG: 11, experiments
- perturbation-method RNG: 12, invariant

## Transfer

The small-system transfer reads the Fisher signature wall as a finite-reservoir
problem. The analytic norm `zeta(2 sigma)` changes sign at `sigma=1/2`, but
any raw finite positive cutoff

```text
Z_X(a) = sum_{n <= X} n^{-a},  a = 2 sigma
```

is positive on both sides. The negative-signature side only appears after a
reservoir subtraction, for example

```text
R0_X(a) = Z_X(a) - X^{1-a}/(1-a)
R1_X(a) = R0_X(a) - 0.5 X^{-a}.
```

## Evidence

Script:

```text
computations/2026-06-21-penrose-r44-fisher-small-system-temperature.py
```

Raw cutoffs stay positive while the subtracted norms match analytic
continuation:

```text
X=100, sigma=0.490: raw= 5.405141(+), R1=-49.424252(-), zeta=-49.424243(-)
X=100, sigma=0.510: raw= 4.982680(+), R1= 50.578662(+), zeta= 50.578670(+)

X=10000, sigma=0.490: raw=10.689039(+), R1=-49.424243(-), zeta=-49.424243(-)
X=10000, sigma=0.510: raw= 8.990523(+), R1= 50.578670(+), zeta= 50.578670(+)
```

The invariant check is decisive:

```text
raw finite sign: always positive
renormalized sign: sign of analytic continuation around sigma=1/2
```

## Verdict

This is not a non-reducing finding. It is a useful experimental warning:
finite positive reservoirs cannot display the Fisher negative signature until
a renormalization/environment subtraction is chosen. But that is exactly the
standard analytic-continuation regularization issue, and it overlaps the R32
finite-cutoff Fisher warning. No chat post; count unchanged.
