# Cancellation on repeated prime factors

**Route** PVC. **Stage** 3-formalized.

Let $D,R\ge1$, let $g_D$ be the [inner coefficient](pvc-the-inner-weight-on-large-prime-multiples.md), and let $w_R$ be the centered quotient weight. In the signed sum $\sum_{Y<uv\le X}\Lambda(u)g_D(v)w_R(\lfloor X/(uv)\rfloor)$ with $u>2(D+1)$, all proper prime powers $u$ and all ordinary primes $u=p$ dividing $v$ together cost
$$
O\big((D+1)R\sqrt X(1+\log X)\big)
$$
uniformly in the lower endpoint $Y$. Each complementary factor cutoff $v>D$ is automatic.

**Quotient intervals.** If all positive prefixes of $a$ through $M$ have absolute value at most $A$ and $|w|\le B$, the sum of $a(t)w(\lfloor M/t\rfloor)$ over $L<t\le M$ is at most $4AB\lfloor\sqrt M\rfloor$ in absolute value. At most $\lfloor\sqrt M\rfloor$ arguments lie below the split, each costing $2AB$. Above the split, at most $\lfloor\sqrt M\rfloor$ nonempty quotient intervals occur. Each interval sum costs $2AB$, including its truncation at $L$.

**Common prime.** For $p>2(D+1)$ the prefixes of $g_D(pt)$ are $O(D+1)$ independent of $p$. Put $v=pt$ and apply the quotient bound at $M=\lfloor X/p^2\rfloor$, $L=\lfloor Y/p^2\rfloor$. The cost summed over the primes is at most a constant times $(D+1)R\sqrt X\sum_{p\le X}(\log p)/p$. The last sum is at most $\log X+\log 4+4$ by [Mertens’ first theorem](../../../../formal/GaloisForLFunctions/RHTower/MertensFirst.lean), since it is bounded by the full positive Mangoldt harmonic sum.

**Proper powers.** For a proper prime power $u$ apply the quotient bound at $M=\lfloor X/u\rfloor$, $L=\lfloor Y/u\rfloor$, using the ordinary prefixes of $g_D$. The positive cumulative proper-power mass $P(t)=\psi(t)-\theta(t)$ is $O(\sqrt t)$. Abel summation gives $\sum_{u\le X,\,u\;\mathrm{nonprime}}\Lambda(u)/\sqrt u=O(1+\log X)$, since $\sqrt n(1/\sqrt n-1/\sqrt{n+1})\le1/n$. This controls every proper prime power, including products with further distinct prime divisors.

**Lean.** [Truncated quotient pairing](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnTruncatedQuotientIntervals.lean), `abs_truncated_quotient_pair`. [Half-weighted proper powers](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheHalfWeightedMassOfProperPrimePowers.lean), `proper_power_half_weight`. [Repeated-prime estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean), `factor_slice_bounds` and `repeated_prime_factors_bound`. The latter depends only on `propext`, `Classical.choice`, and `Quot.sound`.
