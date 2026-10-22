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
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean formalization and targeted audit
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

### C6 -- the cubic is the Taylor shadow of a universal full-grade profile -- PROVED

The exact source deformation is not merely jet-equivalent to the Wold coefficient.  Primewise,

```text
A_p(t) = c_p sinh(t log p) / log p.
```

Hence, with `H_N=log p_N`, the literal centered primitive satisfies

```text
P_N(u/H_N)
 = sum_(n<=N) c_(p_n) sinh(u H_n/H_N)/H_n
   - sinh(u) - C u/H_N.
```

The bounded Wold logarithmic discrepancy predicts the full cofinal law

```text
P_N(u/H_N) -> F(u) := integral_0^1 sinh(u x)/x dx - sinh(u).
```

This is compatible with C5 because `F'(0)=0` and `F'''(0)=-2/3`.  More strongly,

```text
F(u) = -sum_(k>=1) [2k/(2k+1)] u^(2k+1)/(2k+1)!,
```

so `F` is odd and has sign opposite `u`; its only real zero is `0`.  The source-horizontal
prime-clock limit would therefore be a global, not infinitesimal, critical-line classifier.  Its
reflection product `-F(u)F(-u)=F(u)^2` is a canonical nonnegative profile with exact critical
radical, aligning the R/T handoff with the Gauss--Hodge/global-index target.

Lean now proves the complete statement unconditionally.  Every normalized Wold moment, including
mass, converges to `1/(r+1)`; all orders are uniformly dominated by normalized mass.  Dominated
summation gives the full profile limit, exact Taylor resummation identifies it with the literal
finite source deformation, and the terminal holonomy vanishes.  The resulting `F` is odd, has
sign opposite `u`, and vanishes only at `u=0`.

### C7 -- codiagonal/zero-mass conservation annihilates the nonlinear profile -- FAILED

Pair the reflection-odd complete-resolution tail with the reflection-odd profile.  Their product

```text
W_q = -(log 2/2) t_q F(t_q)
```

is reflection-even, nonnegative, and zero exactly on the critical line.  But ordinary codiagonal
conservation controls bounded linear label-blind readers.  `W_q` is a cofinal nonlinear reading.
The existing Gauss--Hodge firewall already admits reflection-closed abstract off-line
configurations with positive analogous mass.  Therefore source symmetry and zero total signed mass
do not force `W_q=0`.

### C8 -- polar work is quantitatively proper -- PROVED

For `u>=0`, every profile deficit mode is nonnegative and the first surviving mode is

```text
u^3/3! * (1-1/3) = u^3/9.
```

Hence `F(u)<=-u^3/9`.  Reflection extends this to the unconditional quartic lower bound

```text
(log 2/18) u^4 <= -(log 2/2) u F(u).
```

Thus every nonzero grade has polar work tending to infinity along every expanding source-scale
orbit.  Uniform boundedness of that orbit is equivalent to `u=0`.

### C9 -- global bounded source-polar orbit work is RH -- PROVED AS RECEIVER; PRODUCER OPEN

Specialize `u` to every multiplicity-labelled Xi centered rate.  For any fixed `d>1`, Lean proves

```text
(forall q, exists B, forall n,
  PolarWork (d^n * centeredRate q) <= B) <-> RiemannHypothesis.
```

This is not an RH proof: no existing normalized carrier bounds this cofinal nonlinear observer.
Route L's source-forced critical-edge Köthe wall is the reciprocal-domain version of the same
properness principle: forward and reciprocal orientations are simultaneously admitted exactly at
zero grade.  The shared missing producer is therefore source-derived simultaneous landing, or an
equivalent pre-zero uniform bound on the polar orbit.  Reflection, bounded scalarization, and
ambient `l1/l2` admission do not supply it.

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
