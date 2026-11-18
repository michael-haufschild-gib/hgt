# Large complementary factors above the square-root product window

**PVC · Formalized.** The residual coprime product at both widths can be restricted to $v\le\lfloor\sqrt X\rfloor$, uniformly in the product lower endpoint and all first-prime cutoffs above $2(D+1)$.

**Proof.** For $p>2(D+1)$ both $g_D(t)$ and $g_D(pt)$ have prefixes bounded by $2+\mathrm{mass}(D+1)$. Subtracting the multiples of $p$ bounds all prefixes of $g_D(v)\mathbf1_{p\nmid v}$. On $v>\max(M,\lfloor Y/p\rfloor)$ the [quotient tail](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnTruncatedQuotientIntervals.lean) has at most $X/(p(M+1))$ fibres. Summation against $\log p$ by Mertens costs $O((D+1)R(1+\log X)X/(M+1))$. At $M=\lfloor\sqrt X\rfloor$ this is square-root precision. The remaining region still contains large ordinary primes paired with complementary factors between the logarithmic cutoff and $\sqrt X$.

**Lean.** [`large_complement_bound`, `bounded_complement_cofactors`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/LargeComplementsInTheCoprimeProduct.lean). Both axiom audits returned `propext`, `Classical.choice`, and `Quot.sound`.
