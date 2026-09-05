# Coprime chronological completion

Stage: in progress. Type: paper proof; Lean implementation pending.

## Exact target

For coprime positive moduli `p,q`, the literal chronological sum
`sum_{1 <= m < n <= N} a_p(m)m^(-s) a_q(n)n^(-conj t)`,
`a_p(n)=1-p[p|n]`, converges whenever `Re s>0` and `Re t>0`.
No zero, reflection, continuation, rearrangement, or fitted counterterm is an input.

## Proof mechanism

The outer coefficient prefix is `A_q(N)=N mod q`. Abel summation expresses the
ordered sum as a vanishing boundary minus two sums. The term containing the
increment of `n^(-conj t)` is absolutely summable, since the inner weighted
prefix is bounded. The other term has coefficient `a_p(n) A_q(n)` and weight
`n^(-s-conj t)`. Coprimality makes this coefficient periodic with zero period
sum: multiplication by `p` permutes the residues modulo `q`. A second Abel
summation therefore converges throughout the positive half-plane.

## Research scope

This sharpens the existing domain `Re s+Re t>1` by retaining arithmetic
cancellation discarded by its norm estimate. It supplies joint, coefficient-exact
second-level completion; it does not supply replication–dilation coherence or
an RH proof. The diagonal case is deliberately not included.

Parent mathematics: Abel summation, residue permutations, periodic multiple
Dirichlet series. Kelliher–Masri, section 9.2,
[Analytic continuation of multiple Dirichlet series](https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf).
No beyond-literature priority claim. The target concerns ordinary chronological
convergence, not merely meromorphic continuation.

Own write scope: `EulerDeletionCoprimeCrossCompletion.lean`, its umbrella import,
and this card. Other tasks own the noncommutative and cylinder modules.
