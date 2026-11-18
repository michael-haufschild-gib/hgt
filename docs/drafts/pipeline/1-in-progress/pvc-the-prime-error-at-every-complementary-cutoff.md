# The prime error at every complementary cutoff

**PVC.** Write $E(t)=\psi(t)-t$, $g_D$ for the inner jumps, and $w_R$ for the centered factorial weight. For arbitrary $a$, the complete Mangoldt tail
$$
\sum_{a<v\le X}g_D(v)\sum_{u\le X/v}\Lambda(u)w_R(\lfloor X/(uv)\rfloor)
$$
differs from $\sum_{a<v\le X}g_D(v)E(\lfloor X/v\rfloor)$ by $O((1+M_{D+1})(1+M_R)(1+\log(RX+2))\sqrt X)$. The [factorial estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringTheFactorialPrimeWeight.lean) bounds the difference at each quotient. The [truncated quotient lemma](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnTruncatedQuotientIntervals.lean) then uses bounded prefixes of $g_D$ on every quotient fibre. The cost is uniform even when $X/a$ exceeds the reciprocal prime window.

For the ordinary coprime tail, large repeated first factors cost square-root error by the [prime-multiple bounds](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean). Proper powers have bounded half-weight up to logarithms. The [uniform slice saving](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationAcrossComplementaryFactorSlices.lean) handles the short first primes at the moving lower limit $pv>pa$. If $a\ge\lfloor Y/(F+1)\rfloor$, the original product cutoff $Y$ is inactive on the tail with $p>F$.

The [complete scalar identity](../2-fully-proven/pvc-a-power-descent-for-the-actual-cofactor-count.md) normalizes the full dilation by the actual prime error. The pointwise transfer to the ordinary coprime row at an arbitrary complementary cutoff remains to be formalized.
