# Logarithmic conductor moments sharpen defect confinement

- **ID:** logarithmic-conductor-defect-confinement
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For each `η>0`, a constant `Cη>0` gives squared approximation error at most `η` by conductors `m≤exp(Cη(K+1))` for every vector of squared mass at most one and prime defect at most `K≥0`, uniformly in the integer horizon.

## Purpose

The exponential cutoff matches the known defect-only obstruction. Combined with a logarithmic defect bound for actual negative complete-Weil eigenvectors, it would give a polynomial conductor range. That signed bound remains unproved.

## Formalized inputs

1. Condition on the primes below `P`, with `log P` proportional to `(K+1)/η`. The existing rough-fibre estimate pays the conditioning error.
2. Truncate the smooth part at `A`. The existing summed valuation moment bounds its discarded mass by `2(K+ladderConstant(P))/log A`.
3. The actual finite-sieve eigenbasis satisfies
   `Σ log(m) |⟨e_m,x⟩|² ≤ 2(log A+L_Q) ‖x‖²`
   on class vectors supported at `a≤A`; [Lean proof](../3-formalized/finite-sieve-profiles-have-logarithmic-conductor-tails.md). Positivity of the sieve operator on absolute coefficients bounds the signed prime term. The identification `e_m(a)=sqrt(sieveDensity(Q)/a)·normalizedRamanujanMode(m,a)` and total class-density mass one are also [formalized](../3-formalized/sieve-eigenbasis-is-density-weighted-ramanujan.md).
4. The geometric class density `μ_Q(a)=sieveDensity(Q)/a` has logarithmic moment at most `L_Q` and tail at most `L_Q/log T`; [Lean proof](../3-formalized/sieve-ground-mass-has-a-logarithmic-moment.md). Positive supported/coprime factorization now proves `μ_Q(a)(log(N+1)-log a)≤w_N(a)≤2μ_Q(a)(log(N+1)+2L_Q+4)`; [Lean proof](../3-formalized/harmonic-sieve-mass-is-controlled-by-its-euler-correction.md). When `A²≤N+1` and `log(N+1)≥2L_Q+4`, these compare the weights by universal factors on `a≤A`.
5. Discarding conductor coefficients above `R` gives relative squared error `16(log A+L_Q)/log R` in the actual harmonic class weights; [Lean proof](../3-formalized/finite-sieve-profiles-have-effective-ramanujan-approximations.md).

## Paper assembly

Put `δ=η/8`. Let `C₀` be the proved rough-conditioning constant. Choose an integer `P>1` with

`C₀(K+1)/δ ≤ log P ≤ C₀(K+1)/δ+3`.

For the sieve of primes below `P`, its Euler correction is the ladder constant `L`. Since `1/(p-1)≤2/p`, the proved Mertens row bound gives `L≤2(log P+log 4+4)`. Thus `L=O_η(K+1)` and the conditioning error is at most `δ`.

The collective valuation estimate, applied to `y_n=sqrt(n)x_n`, gives

`Σ_(n≤N) log(smoothPart_(P-1)(n)) x_n² ≤ 2D_N(x)+2L Σ_(n≤N)x_n²`.

Choose `A>1` with `2(K+L)/δ≤log A≤2(K+L)/δ+3`. The mass on smooth parts above `A` is at most `δ`. Truncating the conditional mean there therefore leaves squared error at most `2δ`. Weighted Jensen bounds the truncated mean's squared mass by one.

Choose `R>1` with

`2log A+2L+4+16(log A+L)/δ ≤ log R ≤ 2log A+2L+7+16(log A+L)/δ`.

For `N≥R`, the harmonic comparison conditions hold. The formalized finite-sieve approximation gives a Ramanujan packet of squared error at most `δ` from the truncated mean. A supported conductor has the same Ramanujan value on `a·b` as on `a` when `b` is coprime to the sieve. Supported/coprime factorization therefore identifies the class-weight error with the physical horizon error. Squared triangle inequality gives total error at most `2(2δ)+2δ=6δ≤η`.

For `N<R`, Möbius inversion and `Σ_(m|d)c_m(n)=d·1_(d|n)` express every function on `1,…,N` using conductors `m≤N`. The approximation is exact and still uses only `m≤R`.

The choices above have `log P`, `L`, `log A`, and `log R` bounded by constants depending only on `η`, times `K+1`. Hence `R≤exp(Cη(K+1))`. Integer cutoffs exist by taking ceilings of exponentials; their logarithmic rounding cost is at most three.

## Remaining scope

The logarithmic defect bound for actual negative complete-Weil vectors remains unproved and is not an input assumed by this theorem.

## Lean

`GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/BoundedPrimeDefectHasAnExponentialConductorCutoff.lean`:

- `exists_exponential_conductor_cutoff_of_poleDefect_le`: the stated horizon-uniform theorem.
- `sum_log_smoothPart_mul_sq_le`: collective smooth-part moment.
- `sum_smoothRoughMean_classMass_le`: contraction of the conditional mean.
- `smoothProfile_ramanujan_error_eq_classMass`: exact transfer to physical horizon error.
- `exists_horizon_ramanujanPole_expansion`: exact finite-horizon span.

Direct Lean check passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
