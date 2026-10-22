# Quantitative finite prime-log phase recurrence

- **ID:** `quantitative-finite-prime-log-phase-recurrence`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / QUANTITATIVE KRONECKER--DIRICHLET BRIDGE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every `d`-tuple of real frequencies has a common recurrence clock
  `1<=n<=(Q+1)^d` with coordinate error at most `1/(Q+1)`.  Consequently every finite weighted
  phase source, and in particular every finite prime-log source, returns within
  `(2pi/(Q+1))` times its total variation of its fully coherent value on the same clock budget.

## Theorem

Let `d,Q` be natural numbers and let

```text
alpha : Fin d -> R.                                         (1)
```

Then there are `n` and integer coordinates `r_i` such that

```text
1<=n<=(Q+1)^d,
|n alpha_i-r_i|<=1/(Q+1)       for every i.                 (2)
```

Equivalently, for angular frequencies `omega_i`,

```text
|n omega_i-2pi r_i|<=2pi/(Q+1).                             (3)
```

For a finite prime list `p_i`, equation `(3)` specializes to

```text
|n log(p_i)-2pi r_i|<=2pi/(Q+1).                            (4)
```

The clock bound depends only on the number `d` of phase coordinates and the requested resolution,
not on the sizes of the primes.

For arbitrary complex weights `w_i`, the same clock satisfies

```text
|sum_i w_i exp(i n omega_i)-sum_i w_i|
 <=(2pi/(Q+1))sum_i|w_i|.                                  (4a)
```

Hence its norm obeys the deterministic capacity floor

```text
|sum_i w_i exp(i n omega_i)|
 >=|sum_i w_i|-(2pi/(Q+1))sum_i|w_i|.                       (4b)
```

Equations `(4a)`--`(4b)` apply verbatim to `omega_i=log p_i`.  Thus the pigeonhole cost controls
the actual weighted Fourier source, not merely its coordinate phases.

### Delay--resolution separation

For every resolution parameter `Q` and every clock multiplier `L`, one can separate the two
resources exactly:

```text
L<=n<=L(Q+1)^d,                                            (4c)
|n omega_i-2pi r_i|<=2pi/(Q+1).                            (4d)
```

Indeed, apply simultaneous approximation to the rescaled frequencies `L omega_i`, obtaining
`m<=(Q+1)^d`, then take `n=Lm`.  Consequently

```text
|sum_i w_i exp(i n omega_i)-sum_i w_i|
 <=(2pi/(Q+1))sum_i|w_i|.                                  (4e)
```

For the critical polar mode

```text
P(n)=(1/2-in)^(-1),                                        (4f)
```

when `L>=1`, one has `|P(n)|<=1/n<=1/L`.  Hence every finite weighted prime-log source satisfies
the exact
prime--polar capacity floor

```text
|sum_i w_i exp(i n log p_i)-P(n)|
 >=|sum_i w_i|-(2pi/(Q+1))sum_i|w_i|-1/L                   (4g)
```

at some clock in the window `(4c)`.  The delay `L` kills the polar mode at only a multiplicative
cost; the exponential dimension cost pays solely for phase resolution.  The earlier annular law
`Q<=n<=Q(Q^2+1)^d` is therefore a valid but strictly weaker specialization.

When the weights are nonnegative, the phase loss is quadratic rather than linear.  The elementary
bound

```text
cos(delta)>=1-delta^2/2                                   (4h)
```

gives the sharper positive-source law

```text
|sum_i w_i exp(i n log p_i)-P(n)|
 >=(1-2pi^2/(Q+1)^2)sum_i w_i-1/L,                         (4i)
```

again at a clock `L<=n<=L(Q+1)^d`.  Thus reaching relative coherence `1-eta` costs resolution
`Q+1` of order `eta^(-1/2)`, not `eta^(-1)`.  This square-root law is the correct deterministic
positive-source baseline near full coherence.

## Proof

Put `M=Q+1`.  For every integer `j` with

```text
0<=j<=M^d,                                                   (5)
```

place the fractional-part vector

```text
({j alpha_1},...,{j alpha_d})                               (6)
```

in the product cell indexed by

```text
(floor(M{j alpha_1}),...,floor(M{j alpha_d})).               (7)
```

There are `M^d+1` vectors and exactly `M^d` cells.  Two distinct indices `x<y` therefore occupy
the same cell.  Put `n=y-x`.  Then

```text
1<=n<=M^d.                                                   (8)
```

Equality of the `i`th cell coordinates gives

```text
|{y alpha_i}-{x alpha_i}|<=1/M.                              (9)
```

Taking

```text
r_i=floor(y alpha_i)-floor(x alpha_i)                        (10)
```

turns `(9)` into `(2)`.  Multiplication by `2pi` proves `(3)`, and `omega_i=log p_i` proves `(4)`.
The elementary chord estimate

```text
|exp(i x)-1|<=|x-2pi r|                                    (10a)
```

followed by the triangle inequality proves `(4a)`.  The reverse triangle inequality proves
`(4b)`.

## Role in the prime-log capacity programme

For a prime cutoff `X`, take `d=pi(X)`.  The theorem gives the explicit recurrence budget

```text
log n<=pi(X)log(Q+1).                                       (11)
```

Thus full finite-prime coherence is always available once the logarithmic observation time is of
order `pi(X)`.  This supplies the unconditional supercritical mechanism in
`prime-log-kronecker-coherence-capacity-conjecture.md`.

It does not prove the new subcritical assertion

```text
log T=o(pi(X))
  => sup_(1<=|t|<=T)|D_X(t)|->0.                            (12)
```

The difference between `(11)` and `(12)` is exactly the new growing-dimensional hitting-time
problem.  Fixed-dimensional Kronecker recurrence cannot decide it.

## Lean formalization

The file

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMPrimePoleFiniteCoherence.lean
```

contains the unconditional declarations

```text
exists_fin_simultaneous_integer_approximation_quantitative
exists_fin_simultaneous_two_pi_phase_approximation_quantitative
exists_fin_primeLog_phase_recurrence_quantitative
norm_exp_I_mul_real_sub_one_le_mod_two_pi
exists_fin_weighted_phaseSum_recurrence_quantitative
exists_fin_weighted_phaseSum_norm_floor_quantitative
exists_fin_primeLog_weighted_phaseSum_recurrence_quantitative
exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
exists_fin_weighted_phaseSum_recurrence_delayed_quantitative
exists_fin_primeLog_weighted_phaseSum_recurrence_delayed_quantitative
exists_fin_primeLog_weighted_phaseSum_polar_floor_delayed_quantitative
one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
nonnegative_weighted_phaseSum_norm_floor_of_phase_approximation
exists_fin_primeLog_nonnegative_phaseSum_polar_floor_delayed_quantitative
exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
weighted_phaseSum_sub_coherent_le_of_phase_approximation
exists_fin_weighted_phaseSum_recurrence_annular_quantitative
exists_fin_primeLog_weighted_phaseSum_recurrence_annular_quantitative
norm_criticalPrimePolarClock_le_inv_nat
exists_fin_primeLog_weighted_phaseSum_polar_floor_annular_quantitative. (13)
```

The proof uses a literal finite pigeonhole argument over product cells.  Narrow verification by

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMPrimePoleFiniteCoherence.lean
```

passes.  The declarations use only Lean's standard logical axioms `propext`, `Classical.choice`,
and `Quot.sound`; there is no project axiom or unproved analytic input.

## Classification

The simultaneous approximation theorem is classical Dirichlet pigeonhole theory.  Its exact
prime-log specialization and formal connector are route-useful infrastructure, not claimed as new
scientific knowledge.  Novelty begins only at the rate-optimal deterministic capacity law for
dimension `pi(X)`.

## Gates

- [x] quantitative denominator bound proved
- [x] coordinate error proved
- [x] angular `2pi` recurrence proved
- [x] prime-log specialization proved
- [x] arbitrary weighted-source recurrence proved
- [x] deterministic norm-capacity floor proved
- [x] cofinal annular clock bound proved
- [x] critical polar decay on the same clock proved
- [x] prime--polar capacity floor proved
- [x] stronger delay--resolution separation proved
- [x] quadratic positive-weight coherence floor proved
- [x] narrow Lean verification passed
- [x] theorem-level axiom audit passed
- [ ] prove the subcritical growing-dimensional converse

## Log

- 2026-07-19 -- Added the quantitative pigeonhole theorem to the existing CCM finite-coherence
  module and formalized its angular and prime-log specializations.
- 2026-07-19 -- Strengthened the result from coordinate recurrence to weighted Fourier-source
  recurrence and the associated norm-capacity floor; re-ran the narrow source and theorem-level
  axiom audits.
- 2026-07-19 -- Proved the cofinal annular recurrence and the finite prime--polar capacity floor.
  This removes the polar term from the supercritical branch rather than treating it as an informal
  asymptotic afterthought.
- 2026-07-19 -- Strengthened the annular estimate to the delay--resolution law
  `L<=n<=L(Q+1)^d`.  The polar-decay budget is now independent of the phase-resolution budget.
- 2026-07-19 -- Proved the quadratic positive-source capacity floor `(4i)`, replacing the linear
  chord loss by the sharp second-order cosine loss.
