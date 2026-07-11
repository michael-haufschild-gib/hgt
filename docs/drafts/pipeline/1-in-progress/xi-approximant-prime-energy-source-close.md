# Xi approximant prime-energy source close

- **ID:** `xi-approximant-prime-energy-source-close`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[OPEN RH CORE]`
- **Scientific status:** `[CONJECTURE] [RH-SUFFICIENT]`
- **Statement:** Construct a source-defined cofinal finite-prime entire family whose transforms
  converge locally uniformly to `XiC` and whose compact zero fibres have sub-log-square reflected
  prime energy. Combined with the formal Hurwitz transfer, this proves `RiemannHypothesis`.

## Exact target

Construct entire functions `F_j`, prime cutoffs `N_j -> infinity`, and, for every `R>0`, envelopes
`E_R(j)->0` such that

```text
F_j -> XiC locally uniformly,

F_j(z)=0 and |z|<=R
  => primeClockCutoffEnergy(N_j, Im z)/(log N_j)^2 <= E_R(j).       (1)
```

The family must be defined from a completed Euler--theta or finite-Weil source before evaluating
the `XiC` divisor. The paper-proved finite-prime theta-cusp screens already supply the first line;
their missing theorem is `(1)`.

## Why the target cannot be weakened formally

If `XiC` has a zero `z` with `Im z != 0`, the formal Hurwitz theorem supplies zeros `z_j` of every
sufficiently advanced locally uniform approximant in an arbitrarily small fixed ball around `z`.
The formal finite-prime susceptibility lower bound then prevents `(1)` for any cofinal cutoff.
Thus cutoff slowing, compact localization, and replacement of uniform by averaged language cannot
make an off-line limit zero disappear. A proof of `(1)` must use a genuine source constraint.

## Selected source mechanism

The concrete operator sufficient condition is an asymptotically Hermitian determinant
linearization. Seek finite matrices or compact-resolvent Galerkin operators

```text
A_j=H_j+K_j,
H_j*=H_j,
||K_j|| log N_j -> 0,                                      (2)
```

and nowhere-zero normalizations `u_j` satisfying

```text
u_j(z) det(z I-A_j) -> XiC(z) locally uniformly.            (3)
```

For every eigenvalue `z` of `A_j` and normalized right eigenvector `v`,

```text
Im z=Im <v,K_j v>,
|Im z|<=||K_j||.                                           (4)
```

The finite-prime critical-window upper estimate then turns `(2)` into `(1)`. Exact Hermitian CCM
determinants are the zero-defect specialization; for them only `(3)` remains.

## Competing mechanisms and attacks

1. **Theta-correlation positivity.** Pointwise positivity and FE--Schwarz symmetry fail on explicit
   positive even kernels with off-axis transform zeros. This mechanism survives only if the exact
   Euler--theta incidence yields a source Gram factorization.
2. **Total zero-energy trace.** A nonnegative trace controlling every compact zero would imply
   `(1)`, but its source evaluation is a Weil/Li positivity theorem and cannot be assumed.
3. **Prime-character Hilbertization.** The analytic defect sees off-real zeros, while the unitary
   `L2` quotient does not. Faithful positive comparison is RH-equivalent in the audited category.
4. **Slow cutoff diagonalization.** This works under RH after compact zero heights are already known
   to vanish; it cannot prove their vanishing and is rejected as target-fed.

## Lean composition already available

The downstream declarations are

```text
RHTower.eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
RHTower.tendsto_horizontalDisplacement_zero_of_cofinal_energy_div_log_sq_tendsto_zero
RHTower.riemannHypothesis_of_XiC_locally_uniform_cofinalLocalPrimeEnergy_approximants.
```

No new Lean wrapper is justified until `(2)`--`(3)` or another source proof of `(1)` is present.

## Gates

- [x] locally uniform Hurwitz transfer formalized
- [x] cofinal compact-local prime-energy transfer formalized
- [x] finite-prime theta-cusp divisor approximants proved on paper
- [x] cutoff-slowing and generic-positive-kernel fake closes rejected
- [ ] construct an asymptotically Hermitian source linearization or an equivalent source Gram
- [ ] prove the compact-local energy estimate `(1)`
- [ ] formalize the source family and estimate
- [ ] compose an unconditional Lean proof of `RiemannHypothesis`
