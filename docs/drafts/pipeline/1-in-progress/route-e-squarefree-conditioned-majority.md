# Route E: squarefree majority sign after conditioning

- **ID:** E-SQUAREFREE-CONDITIONED-MAJORITY-001
- **Stage:** 1-in-progress
- **Target:** turn the proved within-history support bound into a signed source bound for the literal window-conditioned cell.
- **Status:** new paper conjecture/proof to audit; no Lean code yet.
- **Parent:** [conditioned-slot divisor theorem](../3-formalized/route-e-conditioned-slot-divisors.md).

## Scope correction that creates this target

The proved four-value theorem bounds receiver values inside each history.
It does not bound their union across different histories. No cell-wide
sign or load conclusion follows without an additional source law.
Squarefreeness of every physical receiver may supply that law.

## Conjecture and paper argument

Fix positive integer factor arrays `a_c,b_c`, a singleton histogram with
`M>=30` slots, and a nonempty family of histories whose every receiver is
squarefree and lies in `[L,L+W]`. Keep `A=prod_c a_c`. Assume the proved
source inequalities give `W<A` and at most four distinct receiver values
inside every history. The intended family is the literal full histogram
restricted by these physical conditions; it is invariant under common
slot permutations. Arbitrary further conditioning need not have that
invariance and is outside the parity claim below.

1. Distinct inactive factors are pairwise coprime. Given components `c,d`,
   at most two slots activate one of them. Since `M>=3`, another slot
   contains both `a_c,a_d`. Their product divides its squarefree receiver,
   so `a_c` and `a_d` are coprime.
2. If two different slots have the same receiver `n`, then `A` divides
   `n`. For each component, at least one of the two slots is inactive,
   hence `a_c` divides `n`. Pairwise coprimality combines these divisibilities.
3. Distinct multiples of positive `A` differ by at least `A`, so at most
   one multiple of `A` fits the common interval because `W<A`. This is a
   statement about the fixed interval and factor arrays, independent of
   history.
4. Every history has a repeated value since `M>4`. By steps 2–3 it is the
   same integer `n_star` throughout the nonempty family. Every other value
   occurs at most once; the four-value bound leaves at most three such
   slots. Thus at least `M-3` slots equal `n_star` in every history.
5. Since `n_star` is squarefree, `mu(n_star)` is `+1` or `-1`. The signed
   slot sum therefore obeys
   `mu(n_star) * sum_r mu(n_r) >= M-6` in every history.
6. For the uniform law on a family invariant under common slot
   permutations, every anchor has the same distribution. Double-counting
   first gives the stronger positive statement
   `P(n_anchor=n_star)>=1-3/M`. It also gives anchored signed mean of magnitude at least
   `1-6/M`, with orientation `mu(n_star)`. The same argument should hold
   for any nonnegative weight invariant under those permutations.

This would obstruct small anchored Möbius bias for the literal conditioned
squarefree singleton source with fixed activation powers. It would not
bound the Gamma--Hankel covariance of arbitrary prefixes, and it would not
exclude different occupancy laws or source families failing the power bound.

## Deriving the remaining geometric inequality

The closed bounded-activation theorem gives `L^10<=A^11` and the actual
window gives `W^55<L^30`. Hence `W^55<A^33<=A^55` because `A>=1`, so
`W<A`. No logarithmic baseline hypothesis needs to be added.

## Next audit

Search the entire corpus for squarefree-product coprimality, finite
pairwise-coprime divisibility, repeated receiver rigidity, and invariant
slot counting. Verify the source support and sign conventions before
formalizing the exact majority statement. Do not infer invariance under
independent component permutations; only common slot permutations preserve
the window restriction automatically.

The first deep search is complete but partial; it returned no checked
ingredient sets. Source inspection found
`RHTower.finset_prod_dvd_iff_of_pairwise_coprime` in
`EulerDeletionQuasiShuffleCylinderClosure.lean`,
`Nat.coprime_of_squarefree_mul`, `Squarefree.squarefree_of_dvd`, and
`routeEComponentHistoryAnchorSwap_mem_cell_iff`. These are candidate
ingredients, not a verified proof of the new majority statement.
