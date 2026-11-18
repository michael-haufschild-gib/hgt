# The prime error at every complementary cutoff

**PVC · Paper theorem.** Write $E(t)=\psi(t)-t$, $g_D$ for the inner jumps, and $w_R$ for the centered factorial weight. For arbitrary $a$, the complete Mangoldt tail
$$
\sum_{a<v\le X}g_D(v)\sum_{u\le X/v}\Lambda(u)w_R(\lfloor X/(uv)\rfloor)
$$
differs from $\sum_{a<v\le X}g_D(v)E(\lfloor X/v\rfloor)$ by $O((1+M_{D+1})(1+M_R)(1+\log(RX+2))\sqrt X)$. The [factorial estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringTheFactorialPrimeWeight.lean) bounds the difference at each quotient. The [truncated quotient lemma](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnTruncatedQuotientIntervals.lean) then uses bounded prefixes of $g_D$ on every quotient fibre. The cost is uniform even when $X/a$ exceeds the reciprocal prime window.

For $F\ge 2(D+1)$ let $P_a$ be the discarded ordinary coprime row above $v=a$ and $pv>Y$, where $\lfloor Y/(F+1)\rfloor\le a$. Writing $J=1+\log X$, its difference from the complete Mangoldt tail costs
$$
O\big((D+1)R J\sqrt X+F(D+1)^2 R^3 J X^{49/100}\big)
$$
uniformly in $a,Y$. Transposing the two finite sums gives a full slice at every $u$, with lower endpoint $a$. The [slice saving](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationAcrossComplementaryFactorSlices.lean) bounds each short first factor's slice by $O((D+1)^2R^3 JX^{49/100})$, and its Mangoldt mass through $F$ is at most $7F$. At large proper powers the square-root slice estimate and the [half-weight estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheHalfWeightedMassOfProperPrimePowers.lean) give the first term. On ordinary primes removing repeated factors costs the same by the [prime-multiple estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean). The bound on $Y$ makes its lower product edge inactive throughout this tail. With logarithmic $D,R$ and $F=\max(2(D+1),\lfloor X^{1/200}\rfloor)$ the estimate is square-root up to logarithms, since $49/100+1/200<1/2$.
