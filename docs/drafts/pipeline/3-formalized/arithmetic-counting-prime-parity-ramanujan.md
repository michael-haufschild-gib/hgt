# Prime parity has no coprime Ramanujan coordinates

- **ID:** ACP-PARITY-RAMANUJAN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Source:** ../1-in-progress/arithmetic-counting-positivity.md

## Statement

Let `p` be prime, `omega(n)=(-1)^v_p(n)`, `c=(p-1)/(p+1)`, and
`H_N=sum_{1<=n<=N}1/n`. For every positive conductor `m`,

`lim_N H_N^-1 sum_{n<=N} omega(n)c_m(n)/n
 = c sum_{d|m} mu(m/d)omega(d)`.

In particular the limit is zero for every `m>1` with `p` not dividing `m`.
This is an arithmetic correlation theorem. It does not yet prove convergence
of constrained eigenvalues or the maximal hyperplane gap.

## Dependency-closed proof

Multiplicativity and the bijection `k -> d*k` give the exact incidence count

`sum_{n<=N,d|n} omega(n)/n = omega(d) S_floor(N/d)/d`,

where `S_M=sum_{n<=M}omega(n)/n`. Expand the Ramanujan coefficient by its
defining finite Mobius sum `c_m(n)=sum_{d|m,d|n}d*mu(m/d)`, exchange the two
finite sums, and apply that incidence count. The result is exactly

`sum_{n<=N}omega(n)c_m(n)/n
 = sum_{d|m}mu(m/d)omega(d) S_floor(N/d)`.

The parity boundary theorem gives `0<=S_M-c H_M<=K_p`, with
`K_p=2(1+log p)/(p+1)`. The harmonic interval bound gives
`0<=H_N-H_floor(N/d)<=1+log d`. Consequently

`|S_floor(N/d)-c H_N| <= K_p+c(1+log d)`.

Since `H_N>=log N` diverges, division by `H_N` proves
`S_floor(N/d)/H_N -> c`. Taking the limit of the finite divisor sum proves
the claimed formula. If `p` does not divide `m`, it divides no divisor of
`m`, so each `omega(d)=1`. The remaining Mobius divisor sum is zero when
`m>1` and one when `m=1`.

## Novelty and scope

Corpus searches found finite gcd-profile expansions, untwisted Ramanujan
Gram limits and finite-flip polar matching. These do not provide the mixed
nonperiodic prime-parity coordinate limit. Mobius inversion itself is
classical and imported. The new bridge is from the finite parity boundary
count to actual harmonic Ramanujan coordinates, with an explicit uniform
error before passing to a limit.

## Gates

- [x] Exact finite count and closed paper proof.
- [x] Corpus search before mathlib lookup.
- [x] Lean leaf check and transitive axiom audit.
- [x] Umbrella and foundational README updated.

## Lean verification

`ArithmeticCountingPositivity/PrimeParityRamanujanCoordinates.lean` proves:

- `gaugeHarmonicSum_multiples` and `gaugeHarmonicSum_divisibility`;
- `primeParityRamanujanSum_eq`;
- `primeParity_decimation_error` and `primeParity_decimation_tendsto`;
- `primeParityRamanujanSum_tendsto` and `primeParityRamanujanSum_tendsto_zero`.

The exact divisor identity and general limit also include conductor zero,
where both sides vanish by the empty divisor sum. The nontrivial vanishing
theorem uses `m>=2` and `not p|m` exactly as in the paper statement.

The final canonical command
`lake --old env lean GaloisForLFunctions/ArithmeticCountingPositivity/PrimeParityRamanujanCoordinates.lean`
exited zero without diagnostics. All seven declarations have transitive axioms
only `propext`, `Classical.choice`, `Quot.sound`. Its olean was written solely
for the subsequent harmonic spectral-coordinate module. The programme umbrella
imports the leaf; no umbrella was compiled. Audit output and source hash are in
`arithmetic-counting-prime-parity-ramanujan-audit.txt`.

## Subsequent conjecture

The absent coprime coordinates suggest that a flip at a sufficiently large
prime can preserve the exact gap `2 log 2`. Actual spectral projections and
a uniform constrained Rayleigh estimate remain obligations on the parent
card; they are not premises of the theorem above.
