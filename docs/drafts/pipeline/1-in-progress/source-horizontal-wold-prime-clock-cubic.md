# Source-horizontal Wold prime-clock cubic

- **ID:** source-horizontal-wold-prime-clock-cubic
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / CROSS-ROUTE PRODUCER
- **Source:** source-horizontal/Wold neutral-jet bridge, Routes R and T
- **Statement:** Prime-clock normalization kills the residual primitive's linear jet but leaves a
  universal negative cubic response.  The normalized cubic coefficient tends `-2/3`.

## Goal

Attack full-grade cofinal control of the source-horizontal deformation without assuming Route T's
critical Abel norm.  Preserve ordered prime labels and the source reflection-odd grade.

## Gates

- [x] 0 -> 1: exact finite deformation and asymptotic invariant identified
- [ ] 1 -> 2: dependency-closed paper proof
- [ ] 2 -> 3: unconditional Lean formalization and audit
- [ ] RH handoff

## Heavy conjecture loop

### C4 -- fixed-grade residual primitive collapses because `R_N -> 0` -- FAILED

Let `A_p(t)` be the gauged source Gamma-Bockstein deformation with `A_p'(0)=c_p`, and let

```text
P_N(t) = sum_(n<=N) A_(p_n)(t) - sinh(t log p_N) - C t,
```

where `C` is the Wold logarithmic holonomy.  Then `P_N'(0)=R_N`.  For fixed positive `t`, however,
the endpoint term has size `p_N^t`, whereas the Wold sum has only prime-harmonic density.  The
linear residual convergence cannot control the full deformation.  Fixed-grade cofinal collapse is
the wrong conjecture.

### C5 -- normalize grade by the terminal prime clock -- SURVIVES

Put `H_N=log p_N`.  The third neutral jet is

```text
P_N'''(0) = sum_(n<=N) c_(p_n) H_n^2 - H_N^3.
```

The exact residual recurrence

```text
c_(p_(n+1)) = (H_(n+1)-H_n) + (R_(n+1)-R_n)
```

turns the first sum into a right-endpoint quadrature for `integral_0^H x^2 dx`, plus a bounded
Stieltjes residual.  Since every prime-log gap is at most `1` and `R_n` is bounded,

```text
sum_(n<=N) c_(p_n) H_n^2 = H_N^3/3 + O(H_N^2).
```

Therefore

```text
P_N'''(0) / H_N^3 -> -2/3.
```

Equivalently, for the prime-clock-normalized path `theta |-> P_N(theta/H_N)`, the first derivative
is `R_N/H_N -> 0`, while the third derivative tends `-2/3`.  Cofinal normalization is
moment-neutral at first order but not source-trivial: it exposes a universal odd cubic remnant.

## Paper proof outline

For one cell `x=H_n`, `y=H_(n+1)`, `delta=y-x`:

```text
delta*y^2 - (y^3-x^3)/3 = x*delta^2 + (2/3)*delta^3.
```

Because `0<=delta<=1` and `y<=H_N`, summing cell errors is `O(H_N^2)`.  Discrete Abel summation gives

```text
sum_(n<N) (R_(n+1)-R_n) H_(n+1)^2
 = R_N H_N^2 - R_0 H_1^2
   + sum_(1<=n<N) R_n (H_n^2-H_(n+1)^2).
```

Uniform boundedness of `R_n` bounds this by `O(H_N^2)`.  Initial-prime terms are constant.
Since `H_N -> infinity`, division by `H_N^3` proves the limit.

## Hostile boundary

The cubic remnant orients a nonzero horizontal grade but does not annihilate the reflected pair:
reflection negates it.  A valid next producer must make the prime-clock horizon response
reflection-even or source-null while retaining its odd cubic coefficient.  If achieved, the
`-2/3` limit would force the Xi centered rate to vanish.  Mere source equivariance only exchanges
the two signs.

## Lean target

`formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldPrimeClockCubic.lean`

## Log

- 2026-08-11 -- C4 failed; C5 isolated.  Paper proof reduced to exact cubic cell quadrature and
  bounded-residual Abel summation.
