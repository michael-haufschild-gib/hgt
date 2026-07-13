# Finite-prime logarithmic boundary transfer

- **ID:** `finite-prime-logarithmic-boundary-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM / COFINAL BOUNDARY-TRANSFER PRINCIPLE
- **Scientific status:** `[FORMALIZED BRIDGE]`; the analytic zero-transfer corollary is proved on
  paper, while its Rouché step is standard parent complex analysis and is not duplicated in Lean
- **Source:** the canonical reflected prime-clock metric, interpreted as an inner superspace metric
  for finite-prime approximants; separate from RHTower Routes A--D
- **Statement:** A finite-prime cutoff cannot localize a parameter to the critical line. Cofinal
  reflected energy that is `o((log N)^2)` does: it forces the horizontal displacement to zero.
  If holomorphic finite-prime approximants also converge locally uniformly and zero-preservingly to
  `Xi`, every limiting zero lies on the critical line.

## Scope correction

The phrase "every finite-prime RH architecture has a universal `1/log N` boundary layer" requires
a hypothesis. It is proved for architectures whose reflected finite-size geometry dominates the
canonical prime-clock displacement energy, or an equivalent susceptibility with quadratic growth
in `log N`. An arbitrary finite model can be rescaled to have any nominal width, so no unconditional
statement about every imaginable finite-prime construction is mathematically meaningful.

Within the canonical prime-reflection geometry, the logarithmic layer is exact and sharp.

## Reflected finite-prime metric

For

```text
s = 1/2 + epsilon + i t,
tau(s) = 1-conj(s) = 1/2 - epsilon + i t,
```

define the squared distance between the two finite-prime clock perspectives by

```text
E_N(epsilon)
  = sum_(p<=N) |p^(-s)-p^(-tau(s))|^2
  = 4 sum_(p<=N) sinh(epsilon log p)^2/p.                (1)
```

Its susceptibility is

```text
chi_N = sum_(p<=N) (log p)^2/p.                          (2)
```

The already formalized Mertens scaling theorem gives

```text
chi_N/(log N)^2 -> 1/2.                                  (3)
```

Since `|sinh x|>=|x|`,

```text
E_N(epsilon) >= 4 epsilon^2 chi_N.                       (4)
```

Thus the radial scale factor `epsilon` is measured with a stiffness of order `(log N)^2`.

## Cofinal boundary theorem

`[PROVED ON PAPER; PROVED IN LEAN]` Let `epsilon_N` be any real sequence. If

```text
E_N(epsilon_N)/(log N)^2 -> 0,                           (5)
```

then

```text
epsilon_N -> 0.                                         (6)
```

### Proof

By `(3)`, for all sufficiently large `N`,

```text
chi_N/(log N)^2 >= 1/4.                                 (7)
```

Divide `(4)` by `(log N)^2` and use `(7)`:

```text
epsilon_N^2
  <= 4 epsilon_N^2 chi_N/(log N)^2
  <= E_N(epsilon_N)/(log N)^2.                          (8)
```

The right side tends to zero by `(5)`. The left side is nonnegative, so
`epsilon_N^2 -> 0`, hence `epsilon_N -> 0`. QED.

The pointwise formal theorem is slightly stronger operationally. Whenever `(7)` holds,

```text
epsilon^2 <= E_N(epsilon)/(log N)^2.                    (9)
```

This gives a certified horizontal error bar at each sufficiently large cutoff.

## Exact logarithmic boundary layer

For `epsilon_N=c/log N`, the previously formalized critical profile is

```text
E_N(epsilon_N)
  -> Phi(c)
   = 4 integral_0^1 sinh(cu)^2/u du.                    (10)
```

Consequently:

- `epsilon_N log N -> 0` implies `E_N -> 0`;
- `epsilon_N log N -> c!=0` gives a finite nonzero limiting separation;
- `|epsilon_N| log N -> infinity` implies `E_N -> infinity`.

This is the rigorous content of the `1/log N` boundary layer. A single finite cutoff has no wall.
The wall is the cofinal statement that bounded-energy defect fibers are squeezed into a shrinking
window.

Condition `(5)` is weaker than bounded energy. Even energy tending to infinity is allowed, provided
it is `o((log N)^2)`. Conversely, a fixed off-line displacement `epsilon!=0` necessarily costs

```text
E_N(epsilon) >= (2+o(1)) epsilon^2 (log N)^2.            (11)
```

Thus log-square growth is the first scale at which the quadratic coercivity estimate alone no
longer excludes a fixed off-line defect. The exact nonlinear energy of a fixed displacement is
typically much larger; the transfer theorem deliberately uses only the universal lower bound.

## Analytic zero-transfer theorem

`[PROVED ON PAPER]` Let `U={s:0<Re(s)<1}` and let `F_N` be holomorphic on `U`. Assume:

1. `F_N -> Xi` locally uniformly on `U`;
2. for every compact `K subset U`, the zero-fiber energy obeys

   ```text
   sup {E_N(Re(z)-1/2)/(log N)^2 : z in K, F_N(z)=0} -> 0.   (12)
   ```

Then every zero of `Xi` in `U` has real part `1/2`.

### Proof

Let `rho` be a zero of `Xi`. Choose shrinking closed discs `D_j` around `rho`, contained in `U`,
whose boundaries contain no zero of `Xi`. Local uniform convergence and Rouché's theorem imply that
for all sufficiently large cutoffs, `F_N` has the same positive number of zeros as `Xi` in `D_j`.
Choose increasing cutoffs `N_j` and zeros `rho_j` of `F_(N_j)` with `rho_j in D_j`. Then

```text
rho_j -> rho.                                           (13)
```

Put `epsilon_j=Re(rho_j)-1/2`. Condition `(12)` and the pointwise estimate `(9)`, applied along the
cofinal subsequence `N_j`, give `epsilon_j -> 0`. Taking real parts in `(13)` yields

```text
Re(rho)=1/2.                                            (14)
```

Since `rho` was arbitrary, RH follows. QED.

This theorem identifies two logically independent gates:

```text
analytic gate: locally uniform convergence that lifts every Xi zero,
metric gate:   sub-log-square reflected energy on approximant zero fibers.
```

Neither gate can replace the other.

## Quantum-gravity and superspace reading

The horizontal variable `epsilon` is the radial scale factor of the prime superspace; height `t`
is its external clock. Equation `(1)` is the inner metric distance between the two
functional-equation-related clock gauges at finite prime volume.

The theorem does not demand that the two gauges agree at any finite cutoff. It demands that their
metric mismatch on the defect fibers grow more slowly than the log-square stiffness of the
superspace. The thermodynamic limit then removes the radial component and leaves pure clock motion:

```text
sub-log-square on-shell mismatch
  + cofinal zero preservation
  => radial scale factor vanishes
  => Re(rho)=1/2.                                       (15)
```

This is stronger and less circular than postulating exact finite-prime unitarity. It converts the
physics metaphor into a quantitative source target.

## What this kills

The theorem excludes the following as complete RH arguments:

- one finite cutoff, regardless of how cleanly it separates its finite spectrum;
- a fixed-width strip estimate that does not shrink cofinally;
- finite positivity or finite self-adjointness without locally uniform zero transfer;
- finite spectral agreement at selected heights;
- hypertranscendence of every approximant without control of its zero fibers;
- convergence of scalar values that is not locally uniform near zeros.

All of these can hold while zeros wander inside the `1/log N` layer or while the approximants fail
to carry the zeros of `Xi` at all.

## What remains viable

A finite-prime architecture remains viable if it supplies at least one genuine boundary-crossing
mechanism:

- locally uniform convergence to `Xi` plus `(12)`;
- cofinal Weil positivity strong enough to imply the metric gate;
- an exact global self-adjoint realization whose finite compressions converge in a
  zero-preserving topology; or
- a new quantized invariant stable under passage through the logarithmic layer.

For the prime-clock/superspace reformulation, the exact open core is now:

```text
construct source-defined holomorphic F_N
  -> prove F_N -> Xi locally uniformly
  -> prove E_N(Re(z)-1/2)=o((log N)^2) at every F_N zero.      (16)
```

The first two arrows carry the divisor. The third forces the internal scale factor to vanish. No
finite theorem alone can substitute for their conjunction.

## Robust contraction companion

`[PROVED IN LEAN]` If `T` is a contraction on a complex normed space and a nonzero vector `x`
satisfies

```text
||T x-lambda x|| <= delta ||x||,
```

then

```text
|lambda| <= 1+delta.                                    (17)
```

If reciprocal radial powers `q^a` and `q^(-a)` remain uniformly bounded on arbitrarily large
scales, then `a=0`. This is the channel-theoretic form of the same cofinal principle: approximate
physicality of both reflected modes is enough; exact inverse channels are unnecessary.

## Lean surface

The new module
`formal/GaloisForLFunctions/RHTower/FinitePrimeBoundaryTransfer.lean` proves:

- `FinitePrimeBoundaryTransfer.norm_le_one_add_of_approx_eigenmode`;
- `FinitePrimeBoundaryTransfer.exponent_eq_zero_of_uniform_reflected_bounds`;
- `RHTower.horizontalDisplacement_sq_le_energy_div_log_sq`;
- `RHTower.tendsto_horizontalDisplacement_zero_of_energy_div_log_sq_tendsto_zero`.

It imports the already formalized exact energy identity, Mertens susceptibility asymptotic, and
quadratic lower bound from `RHTower.PrimeClockFiniteScaling`. No axiom or conjectural analytic input
is introduced.

## Gates

- [x] exact finite metric and logarithmic susceptibility available
- [x] cofinal sub-log-square transfer proved on paper
- [x] quantitative pointwise bound formalized in Lean
- [x] robust approximate-contraction companion formalized in Lean
- [x] locally uniform zero-transfer corollary proved on paper
- [ ] construct a source-defined approximant family satisfying both transfer gates
- [ ] formalize the analytic Rouché transfer only if it becomes a reusable non-wrapper dependency
