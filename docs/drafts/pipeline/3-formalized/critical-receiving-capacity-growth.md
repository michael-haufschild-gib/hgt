# Receiving capacity versus the critical overlap

- **ID:** critical-receiving-capacity-growth
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

## Exact question

The corpus gives an exact dilation capacity

    C_N = Σ_(p≤N) (log p/p)/H_(floor(N/p)),
    min_(charge=t) J_N = t²/C_N.

The kernel-checked quantitative law gives a constant C such that

    |C_N−log log N|≤C  for every integer N≥3.

Consequently C_N/c_N→0 at every positive critical ratio
c_N⁸/log N→R. Nonzero fixed charge therefore has dilation cost much
larger than 1/c_N, even though its minimum cost tends to zero.
The exact finite capacity and its unique minimizer are already proved in
`ArithmeticCouplingTheory/ReceivingCharges/PrimeIncidenceReceivingCapacity.lean`.
The new bounded-error law is
`primeIncidenceReceivingCapacity_log_log_bounded` in
`ArithmeticCouplingTheory/ReceivingCharges/PrimeIncidenceCapacityGrowth.lean`.
Its final actual-path check uses exactly
`[propext, Classical.choice, Quot.sound]`. The critical-scale consequence
and the divergence `c_N t²/C_N→∞` for t≠0 also pass their final
actual-path check in
`CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeCapacityAtCriticalScale.lean`
with exactly those axioms. Both modules are wired into their umbrellas.

This is a dilation statement. A comparable lower bound for the **complete**
energy is a separate open problem; no such comparison is assumed here.

## Why the distinction matters

`PrimeChargeRawObstruction.lean` proves arbitrarily small complete raw cost
at prescribed exact charge. Its dyadic construction fixes M before taking
N=X^(2^(M+1))→∞, with limiting cost 3t²/(2M). That qualitative existence
theorem gives no cost at a prescribed critical rate.

For a fixed window with energy of order c_N, an O(1) mixed pairing and a
positive source cost e_N permit an optimized energy reduction of order
1/e_N. A nonvanishing reduction after division by c_N therefore requires
e_N=O(1/c_N), or a correspondingly larger mixed pairing. This is an
algebraic scale requirement, not an assertion that those mixed limits hold.

## Exact decomposition and proof

Let B(n)=Σ_(p≤n)log p/p. `primePoleScale_logarithmic` in
`CriticalScaleArithmeticRigidity/PrimePoleNorm.lean` gives
|B(n)−log n|≤C₀ for n≥1. For N≥2, put
`d_k=1/H_k−1/H_(k+1)≥0`. Telescoping each inverse harmonic denominator
and interchanging finite sums gives the exact identity

    C_N=B(N)/H_N
        +Σ_(k=1)^(N−1) d_k[B(N)−B(floor(N/(k+1)))].

The arithmetic condition is exact:
`floor(N/p)≤k` iff `p>floor(N/(k+1))`. All cofactor cutoffs in this sum
are positive. If M=floor(N/(k+1)), then
`1≤N/((k+1)M)<2`, so

    |B(N)−B(M)−log(k+1)|≤2C₀+log 2.

Since `Σd_k=1−1/H_N≤1`, this costs a uniform constant. Another finite
summation by parts identifies the comparison sum as

    K_N=Σ_(k=1)^(N−1) log((k+1)/k)/H_k.

In particular `|C_N−K_N|≤3C₀+log 2`. The harmonic increment
`H_(k+1)−H_k=1/(k+1)` and `u/(1+u)≤log(1+u)≤u` give

    0≤log((k+1)/k)/H_k−log(H_(k+1)/H_k)≤2/[k(k+1)].

Both comparison sums telescope, yielding `0≤K_N−log H_N≤2`.
Finally `log N≤H_N≤1+log N` makes `log H_N−log log N` uniformly bounded
for N≥3. Hence the claimed law follows entirely from finite sums.

For the critical corollary, write
`log log N=log(log N/c_N⁸)+8 log c_N`. The first term tends to
log(1/R), while log(c_N)/c_N→0. The bounded capacity error divided
by c_N also vanishes. Since C_N>0 for N≥2, this implies
`c_N t²/C_N→∞` for every fixed nonzero t. The corresponding source is
`ReceivingCharges/PrimeCapacityAtCriticalScale.lean`.

The three finite-sum steps pass their final actual-path Lean audits:
`PrimeIncidenceCapacityCofactors.lean`, `InverseHarmonicLogSum.lean` and
`PrimeIncidenceCapacityGrowth.lean`. Each endpoint uses only the standard
three axioms. Together with the checked critical-scale corollary, this
closes the stated dilation theorem. The complete-energy comparison
remains a separate research question.

## Attack and positive survivor

Verdict: **BRIDGE**. This is weighted prime Mertens theory applied to the
corpus's exact receiving capacity, not a new arithmetic cancellation law.
It is compatible with arbitrarily small raw costs and every fixed finite
positive scale form. Its useful boundary is quantitative: qualitative
charge survival does not determine whether a critical window can be corrected.

The subsequent hard questions are source-specific:

1. Evaluate the complete energy of the actual capacity minimizer uniformly
   in N, including its harmonic centering and all overlap terms.
2. Evaluate its mixed pairing with each fixed terminal window on the same
   schedule. Retain both rates before optimizing coefficients.
3. If complete energy differs substantially from dilation energy, identify
   the signed channel producing that difference and its receiving cost.

The existing complete moment bound can lose powers of c_N on coefficients
concentrated near the largest primes. Replacing complete energy by dilation
energy there would assume the missing comparison. The capacity law alone
neither extends the positive critical band nor removes compensation.
