# Shift-one seam power-64 Cassini--Jensen source law

- **ID:** `shift-one-seam-power64-cassini-jensen`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / new right-to-left source coordinate
- **Scientific status:** `[PROVED HERE] [NEW SOURCE WELD] [NOT AN RH PROOF]`
- **Lean consumers:**
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamPowerSixtyFourMassCriterion.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamPowerSixtyFourJensenKernel.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniSource.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniPairQuotient.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniJensenSourceLaw.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniGlobalJensenLaw.lean`

## Setup

Write

```text
X(w) = xi(1/2+w).
```

The functional equation makes `X` even.  Hence there is a unique entire function `Phi` such that

```text
Phi(w^2) = X(w).
```

Translate its squared coordinate by the shift-one Euler point:

```text
Psi(u) = Phi(1-u).
```

Since `Psi(0)=Phi(1)=xi(3/2) != 0`, its centered Jensen excess is defined for every `r>0` by

```text
E64(r)
  = circleAverage_(|u|=r) log|Psi(u)| - log|Psi(0)|.
```

For a nontrivial Xi zero `rho`, put `w_rho=rho-1/2`.  Its shift-one squared-seam coordinate is

```text
z_rho = 1/(1-w_rho^2).
```

The zeros of `Psi` are exactly

```text
u_rho = 1-w_rho^2 = z_rho^(-1),
```

with one copy for each functional-equation pair `w_rho,-w_rho` and with analytic multiplicity
retained.

## Theorem

Let

```text
H64 = sum_(rho, with multiplicity) |z_rho|^64.
```

Then

```text
H64 = 8192 * integral_0^infinity E64(r) / r^65 dr.          (1)
```

Consequently, with

```text
S64 = Re(primeArchShiftedReciprocalMoment 1 63),
C32 = sum_(rho, with multiplicity) Im(z_rho^32)^2,
```

one has

```text
C32 = 4096 * integral_0^infinity E64(r) / r^65 dr
        - S64/2,                                           (2)

8192 * integral_0^infinity E64(r) / r^65 dr <= S64
  <-> C32 = 0
<-> RiemannHypothesis.                                   (3)
```

Lean now proves `(2)` exactly as
`xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual`, proves its right-hand
side nonnegative unconditionally, and proves that equality to zero is equivalent to RH.  Thus
ordinary Jensen nonnegativity does not discharge `(3)`: it supplies only nonnegativity of the
residual already identified with `C32`; the missing statement is its exact vanishing.

The reverse inequality in `(3)` is the new most-right source obligation.  It contains no zero
enumeration: `Psi` is the canonical completed entire source in the translated squared coordinate,
and `S64` is the explicit prime--Gamma negative-binomial moment already formalized in Lean.

## Proof

Jensen's formula gives, for `r>0`,

```text
E64(r)
  = sum_(u in Z(Psi), |u|<=r) mult(u) log(r/|u|).          (4)
```

Every summand is nonnegative.  Tonelli therefore permits integration before summation.  For every
`a>0`, direct antidifferentiation gives

```text
integral_a^infinity log(r/a) / r^65 dr
  = 1/(64^2 a^64)
  = 1/(4096 a^64).                                        (5)
```

Combining `(4)` and `(5)` yields

```text
4096 * integral_0^infinity E64(r) / r^65 dr
  = sum_(u in Z(Psi)) mult(u) |u|^(-64).                  (6)
```

The map `w -> w^2` identifies the two zeros `w` and `-w` forced by the functional equation.
Because `X(0)=xi(1/2) != 0`, there is no fixed zero at `w=0`.  Thus the multiplicity-exact Xi
divisor sum has exactly twice the mass in `(6)`.  Since `u=z_rho^(-1)`, equation `(1)` follows.

Lean already proves

```text
H64 - S64 = 2*C32,
H64 <= S64 <-> C32=0 <-> RH.
```

Substitution of `(1)` gives `(2)` and `(3)`.

## Why this changes the backward chain

The older centered radial-Jensen law uses inverse-square mass around `s=1/2`.  Equation `(1)` is
not that law at a higher exponent.  Its squared-coordinate translation centers the entire source
at

```text
Psi(0)=xi(3/2),
```

inside absolute Euler convergence.  In the original `s`-plane, the level sets

```text
|1-(s-1/2)^2| = r
```

are Cassini ovals with foci `-1/2` and `3/2`.  The remaining RH-bearing comparison is therefore a
weighted circular log-modulus inequality based at an Euler-safe point, not another all-degree
Hankel cone and not a central-line estimate.

The exact backward chain is

```text
[OPEN] Euler--Gamma control of the Cassini--Jensen integral in (3)
  -> C32=0
  -> dyadic tail from power 64
  -> RH.
```

## Lean status

- [x] shift-one atom equals squared-seam coordinate
- [x] source moment `S64` equals the holomorphic power-64 trace
- [x] `H64-S64=2*C32`
- [x] `C32=0 <-> RH`
- [x] formalize the even entire quotient `Phi`
- [x] formalize `Psi(u)=Phi(1-u)` and its zero-divisor multiplicity pairing
- [x] formalize the exponent-64 atom integral and Tonelli divisor sum
- [x] identify the Tonelli divisor profile with `E64` and finish identity `(1)`
- [ ] prove the source inequality `(3)` from Euler--Gamma data
- [ ] RH
