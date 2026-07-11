# Prime-clock critical-window scaling law

- **ID:** `prime-clock-critical-window-scaling`
- **Stage:** 2-fully-proven (paper), Lean completion pending
- **Type:** THEOREM (paper) / `[NOVELTY UNVERIFIED]`
- **Source:** finite-cutoff form of the reflected infinite prime-clock superspace, separate from the
  live routes in `docs/reports/rhtower_status_1107.md`
- **Statement:** The reflected coherent-sector transition has the sharp finite-size window
  `Re(s)-1/2 = Theta(1/log N)`. If `epsilon_N log N -> c`, the prime-cutoff displacement energy
  converges to the universal profile

  ```text
  Phi(c) = 4 integral_0^1 sinh(c u)^2 / u du.
  ```

## Goal

Turn the infinite Shale seam into a quantitative phase-transition theorem. The result determines
how the line emerges from finite prime universes and supplies a falsifiable renormalization law for
the proposed quantum phase space.

## Gates

- [x] 0 → 1 in-progress: finite energy, scaling variable, candidate profile, and Mertens input fixed.
- [x] 1 → 2 fully-proven: complete paper proof below.
- [ ] 2 → 3 formalized: the exact hyperbolic identity, two-sided finite-window bounds,
  susceptibility asymptotic (8), sharp subcritical convergence, supercritical divergence, and a
  nondegenerate critical-scale sandwich are in `PrimeClockFiniteScaling.lean`; only the exact
  nonlinear profile (7) remains.
- [ ] 3 → 4 publication-ready: requires full Lean proof and a broader parent-literature/rediscovery
  audit. The preliminary exact-formula search found no instance of this crossover law.

## Finite prime universe

Put

```text
s = 1/2 + epsilon + i t,
tau(s) = 1-conj(s) = 1/2 - epsilon + i t.
```

At prime cutoff `N`, the squared coherent displacement is

```text
E_N(epsilon)
  = sum_{p <= N} |p^(-s) - p^(-tau(s))|^2
  = sum_{p <= N} (p^(-1/2-epsilon) - p^(-1/2+epsilon))^2.
```

The clock phase `exp(-it log p)` cancels exactly. Thus `E_N` measures only the distance between the
two reflected clock perspectives.

## Exact hyperbolic form `[PROVED HERE; PROVED IN LEAN]`

For every real `epsilon`,

```text
E_N(epsilon) = 4 sum_{p <= N} sinh(epsilon log p)^2 / p.        (1)
```

Indeed,

```text
p^(-1/2-epsilon) - p^(-1/2+epsilon)
  = -2 p^(-1/2) sinh(epsilon log p).
```

In particular `E_N` is nonnegative and even, and `E_N(0)=0`.

Define the quadratic susceptibility

```text
chi_N = sum_{p <= N} (log p)^2 / p.
```

Since `|sinh x| >= |x|`, equation (1) gives the exact lower bound

```text
E_N(epsilon) >= 4 epsilon^2 chi_N.                              (2)
```

## Mertens measure

Let `L=log N` and define a finite measure on `[0,1]` by

```text
nu_N = (1/L) sum_{p <= N} ((log p)/p) delta_(log p/L).
```

Mertens' first theorem in prime form says

```text
A(x) := sum_{p <= x} (log p)/p = log x + O(1).                  (3)
```

The error in (3) is uniformly bounded. Therefore, uniformly for `0 <= u <= 1`,

```text
nu_N([0,u]) = A(N^u)/L = u + O(1/L).                            (4)
```

Replacing `N^u` by its integer part changes the numerator by a bounded amount, including the
bounded region near `u=0`. Hence (4) is uniform. It follows that

```text
nu_N  ->  Lebesgue measure on [0,1]                             (5)
```

weakly. This is an elementary bounded-discrepancy form of the Helly--Bray theorem; equivalently,
step functions follow directly from (4), and continuous functions follow by uniform approximation.

## Universal crossover theorem `[PROVED HERE]`

Let `epsilon_N` be any real sequence such that

```text
c_N := epsilon_N log N -> c in R.
```

Define

```text
g_c(u) = 4 sinh(c u)^2 / u  for u>0,
g_c(0) = 0.
```

The extension at zero is continuous because `sinh(cu)^2/u = c^2 u + O(u^3)`. From (1),

```text
E_N(epsilon_N)
  = integral_[0,1] g_(c_N)(u) d nu_N(u).                        (6)
```

On every bounded `c`-interval the map `(c,u) -> g_c(u)` is continuous on the compact set
`[-C,C] x [0,1]`. Thus `g_(c_N) -> g_c` uniformly. Combining this with (5) and (6) gives

```text
lim_N E_N(epsilon_N)
  = Phi(c)
  := 4 integral_0^1 sinh(c u)^2 / u du.                         (7)
```

This proves the claimed profile. ∎

## Sharpness of the window `[PROVED HERE]`

Taking the test function `u` in (5) yields

```text
chi_N / (log N)^2
  = integral_[0,1] u d nu_N(u)
  -> 1/2.                                                       (8)
```

Consequently:

- if `epsilon_N log N -> 0`, then `E_N(epsilon_N) -> Phi(0)=0`;
- if `epsilon_N log N -> c` with `0<|c|<infinity`, then
  `E_N(epsilon_N) -> Phi(c)` with `0<Phi(c)<infinity`;
- if `|epsilon_N| log N -> infinity`, then (2) and (8) give
  `E_N(epsilon_N) -> infinity`.

Therefore `1/log N` is the sharp crossover width, not merely an upper or lower estimate.

For normalized bosonic coherent vectors, the overlap magnitude is

```text
O_N(epsilon) = exp(-E_N(epsilon)/2).
```

In the critical window,

```text
O_N(epsilon_N) -> exp(-Phi(c)/2).
```

Near the center, `Phi(c)=2c^2+O(c^4)`, so the first crossover profile is Gaussian:
`O_N -> exp(-c^2+O(c^4))`.

## Interpretation

`[PROVED]` A finite prime universe has no superselection boundary: all reflected coherent vectors
have nonzero overlap. The boundary forms only in the thermodynamic limit.

`[PROVED]` The scale that resolves the boundary is logarithmic. A cutoff at `N` cannot distinguish
horizontal displacements much smaller than `1/log N`; displacements much larger than that become
orthogonal.

`[BRIDGE]` The result is RH-blind by itself. It explains the geometry of the selector but does not
show that `Xi` zeros inhabit its critical window.

`[NOVELTY UNVERIFIED]` The proof uses classical Mertens theory and weak convergence, but the exact
prime coherent-sector crossover profile was not found in preliminary searches across coherent-state,
orthogonality-catastrophe, prime-zeta, and finite-size-scaling literature. Scientific novelty remains
provisional until the formal proof and a specialist literature audit are complete.

## Lean status

`formal/GaloisForLFunctions/RHTower/PrimeClockFiniteScaling.lean` proves:

- `reflected_rpow_diff_sq_eq_sinh`;
- `primeClockCutoffEnergy_eq_sinh`;
- `sq_le_sinh_sq`;
- `primeClockCutoffEnergy_quadratic_lower`;
- `primeClockCutoffEnergy_zero`;
- `primeClockCutoffEnergy_neg`;
- `primeClockSusceptibility_nonneg`;
- `tendsto_primeClockSusceptibility_div_log_sq`;
- `primeClockCutoffEnergy_quadratic_upper`;
- `tendsto_primeClockCutoffEnergy_zero_of_scaled_tendsto_zero`;
- `tendsto_primeClockCutoffEnergy_atTop_of_scaled_tendsto_atTop`;
- `primeClockCutoffEnergy_critical_scaled_sandwich`.

The repository already contains the required explicit Mertens bound in
`RHTower.Mertens.mertens_first_prime`. Lean now derives (8), the sharp `1/log N` trichotomy, and the
critical-scale two-sided bounds from it. The remaining Lean task is the bounded-discrepancy measure
limit for the exact nonlinear test family in (4)--(7), not any unproved number-theoretic input.

## Log

- 2026-07-11 — exact energy identity and lower bound formalized; complete Mertens-measure proof of the
  universal `1/log N` crossover profile written on paper; novelty retained as unverified.
