# Rank-uniform logarithmic Cauchy approximation: exact obstruction and survivor

- **ID:** RH-LOG-CAUCHY-RANK-ROOT-20260926
- **Stage:** 5-failed — this coefficient-model mechanism only
- **Type:** [BRIDGE] FALSIFIED; positive survivor formalized
- **Parent:** `../1-in-progress/rh-nonlocal-tail-root-2026-09-26.md`
- **Owner:** root
- **RH status:** unresolved; no literal-theta negative form is asserted.

## Frozen test

The common-shift theta-tail formula suggests a positive Cauchy leading kernel
with a logarithmic correction. Can a sufficiently large fixed diagonal level
make that displayed correction positive in every rank?

This was a derived mechanism test. The actual theta-to-model two-term transfer
was not assumed proved. The subsequent `ThetaTailCauchyAsymptotic` leaf now proves
it at fixed nodes. Transfer of coefficient forms at growing rank remains open.

## Exact paper model

For `u=u0*(1+z)/(1-z)`, `v=u0*(1+w)/(1-w)`, `u0>0`, and `|z|,|w|<1`,

```
(2R+(log u+log v)/2)/(u+v)
 = (1-z)(1-w)/(2u0) * (L+A(z)+A(w))/(1-z*w),
L=2R+log u0,  A(z)=(log(1+z)-log(1-z))/2.
```

The identity is algebraic after the real logarithm product/quotient laws.
The power series of A is `sum_(j>=0) z^(2j+1)/(2j+1)`: differentiate the
convergent geometric series and integrate from zero. Consequently the bivariate
coefficient array has diagonal L, odd off-diagonals `1/|i-j|`, and all other
entries zero. The Lean file independently proves the exact formal-series
equation `(1-zw)K=L+A(z)+A(w)`, and the real Cayley identity.

For an arbitrary real vector on 2m coordinates, define

```
E(a)=sum_(i<2m) a_i^2,
Q(L,m,a)=L E(a)+2 sum_(j<m) [sum_(i<2m-(2j+1)) a_i a_(i+2j+1)]/(2j+1),
h_m=sum_(j<m) 1/(2j+1).
```

## Killing theorem [PROVED IN LEAN]

At the alternating vector `a_i=(-1)^i`, each odd-lag product is -1, hence

`Q(L,m,a)=2m*(L+1-2h_m)`.

Since `h_m >= (1/2) sum_(j<m) 1/(j+1) -> infinity`, every fixed L has a
negative finite-rank test. More strongly, no corrections `r_m` satisfying
`r_m(a)<=C E(a)` for one finite constant C can make `Q+r_m` nonnegative in
every rank. The necessary correction on the alternating vector is
`r_m(a)>=2m*(2h_m-1-L)`.

## Strongest positive survivor [PROVED IN LEAN]

1. **Threshold window:** `|Q-L E|<=2h_m E`. Thus `L>=2h_m` suffices for
   positivity; positivity at m>0 forces `L>=2h_m-1`. The proof applies
   `2|ab|<=a^2+b^2` to each lag and bounds both partial energies by E.
2. **Exact adverse sign pattern:** replacing any a by `(-1)^i |a_i|` can only
   decrease Q. Positivity is equivalent to positivity on these tests with
   arbitrary nonnegative amplitudes. Parity conjugation reverses exactly the
   off-diagonal part.
3. **Joint rank law:** `2h_m-log m -> 2log 2+gamma`. This follows from
   `h_m=H_(2m)-H_m/2` and the existing harmonic asymptotics. Therefore
   `Q(log m+c,m,alternating)/(2m) -> c+1-2log 2-gamma`.
4. **Fixed rank survives:** every fixed m is positive for all sufficiently
   large L. This coexists with failure at every fixed L when rank is unbounded.

## What this means for the whole route

The positive fixed-rank Cauchy approximation cannot be promoted to an all-rank
producer by a uniformly bounded correction in coefficient energy. Its missing
joint boundary has logarithmic rank scale and an explicit negative direction.
The full theta correction may have unbounded coefficient energy despite small
pointwise size; nothing here excludes that possibility or the nonlocal route.
The actual two-term kernel asymptotic is now proved at fixed nodes in
`ThetaTailCauchyAsymptotic`. The next obligation is control of its coefficient
form at growing rank, retaining complete theta assembly.

## Formal scope and verification

Leaf: `formal/GaloisForLFunctions/RHTower/LogarithmicCauchyRankBoundary.lean`,
namespace `RHTower.LogCauchyRank`; wired into `RHTower.lean`.

- Scratch check passes with no diagnostics.
- Named leaf build passes: 3132 jobs, cached dependency reuse.
- All 36 public theorem axiom reports contain only `propext`, `Classical.choice`,
  `Quot.sound`; none missing. Index refreshed; global `lint --check-generated`
  passes with existing large-file warnings.
- No numerical experiment or git command. No global novelty claim.
- The analytic positive-kernel-to-jet transfer and the literal-theta asymptotic
  are not claimed as Lean theorems in this leaf.
