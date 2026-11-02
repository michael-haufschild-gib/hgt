# Positive atomic cancellation on a two-clock cone

- **Stage:** 3-formalized.
- **Parent:** SC2 in `../1-in-progress/route-sc-complete-family-and-coupling.md`.
- **Result:** Weight lower bounds, linear height counts, and exact two-prime
  phases do not exclude cone cancellation. Actual zeta spline weights remain
  outside this countermodel.

## Exact theorem

For every `a,b>0` and `0<d<D`, there are countably many distinct
`z_j=delta_j+i gamma_j` and positive weights `w_j` satisfying

1. `d<=delta_j<D`, with unattained supremum `D`.
2. `sum_j w_j=2` and `w_j>=(1+|gamma_j|)^(-1)`.
3. Atoms with `|gamma_j|<=T` embed into `Fin floor(T)` for every real `T`.
4. For every nonzero natural cone time `t=ma+nb`, the absolutely convergent
   sum `L(t)=sum_j w_j exp(t z_j)` is zero.

In particular this applies to `a=log p,b=log q` for distinct primes, retaining
actual joint clock separation. The reciprocal lower bound is stronger than
an eighth-power lower bound.

The quartet kernel `K(t)=L(t)+conj L(t)+L(-t)+conj L(-t)` is even and Hermitian,
`K(0)=8`, and `|K(t)|<=4` at every positive cone time. Consequently

`|K(ma+nb)-K(ma)-K(nb)+K(0)|<=20` for every `m,n>=0`.

## Proof

For finite positive frequencies `S`, convolve equal two-point measures at
`{0,pi/u}` over `u` in `(S union (S-S) union (S+S))\{0}`. The resulting
uniform `n`-atom measure has zero Fourier transform at all these frequencies.
Translation preserves the zeros and permits arbitrary heights. If
`sum_s |r_s|<=A/4`, weights

`w_j=(A-2 Re sum_s r_s exp(-i s gamma_j))/n`

lie in `[A/(2n),3A/(2n)]`, sum to `A`, and correct all moments to `-r_s`.

Use levels `delta_k=D-(D-d)2^(-k)` and block masses `2^(-k)`. Exponential
summability on the two-generator cone supplies nested exhaustive finite
cutoffs whose next uncancelled tail is small enough for positive correction.
Every prefix has mass `2-2^(-k)` and cancels its cutoff. Each fixed moment
therefore vanishes in the absolutely convergent limit. Place each block
above its cumulative atom count and reciprocal minimum weight. Merge
repeated nodes by summing their positive weights; moments, counting, and
weight bounds survive. Increasing real levels give the unattained width.

For quartets, positive-time cancellation leaves only the reflected sum,
whose norm is at most the mass two, and its conjugate. Three such bounds
and `K(0)=8` give twenty; coupling vanishes on the axes.

## Lean audit

Namespace `GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments`, files
under `formal/GaloisForLFunctions/ArithmeticCouplingTheory/ConeMoments/`:

- `PositiveFiniteCorrection.lean`: `exists_positive_correction`.
- `PositiveMomentExtension.lean`: `exists_positive_level_extension`.
- `PositiveConeCutoffs.lean`: `exists_nested_cone_cutoffs`.
- `PositiveCloudExtension.lean`: `exists_initial_stage`, `exists_stage_extension`.
- `PositiveAtomicConeNullseries.lean`: `exists_two_clock_positive_atomic_nullseries`.
- `PositiveQuartetsWithBoundedConeCoupling.lean`: `exists_positive_quartet_cone_model`.

Final direct `lake --old env lean` audits pass. Transitive axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.

## Remaining constraint

The model does not impose an eighth-power upper weight bound, prescribed
complex spline phases, or integer zero multiplicities. The quantitative
upper/lower-weight conjecture is tracked in
`../1-in-progress/two-prime-cone-spline-sized-weights.md`.
