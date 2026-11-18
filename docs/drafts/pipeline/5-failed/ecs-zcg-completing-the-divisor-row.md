# Completing the divisor row preserves the prime wave

**Stage** 5-failed. **Scope** Replacing the restricted cofactor row by its completed row to gain cancellation.

**Obstruction.** Write $E(N)=\psi(N)-N$, $M_V(N)=\sum_{d\le\min(V,N)}\mu(d)\lfloor N/d\rfloor$, and $C_{V,W}(N)=\sum_{d\le\min(W,N)}b_V(d)E(\lfloor N/d\rfloor)$. For every $V,W,N$,
$$\left|C_{V,W}(N)+\sum_{W<d\le N}b_V(d)E(\lfloor N/d\rfloor)-E(N)-2\gamma M_V(N)\right|\le 50\sqrt N\sqrt V.$$
Thus for a wave of order $N^\beta$ the mean-corrected completed row retains its amplitude whenever $V=o(N^{2\beta-1})$. The omitted tail is part of the arithmetic question for a fixed cutoff.

**Positive theorem and proof.** The complete unweighted sum $S(N)=\sum_{d\le N}E(\lfloor N/d\rfloor)$ equals $\log(N!)-\sum_{d\le N}\lfloor N/d\rfloor$. Stirling's estimate and the Dirichlet hyperbola bound give $|S(N)+2\gamma N|\le25\sqrt N$. The unit term of $b_V$ contributes $E(N)$, and its divisor term contributes $-\sum_{d\le\min(V,N)}\mu(d)S(\lfloor N/d\rfloor)$. Sum the preceding square-root error using $\sum_{d\le V}d^{-1/2}\le2\sqrt V$, then split the completed count at $W$.

**Lean** `abs_completeDivisorError_add_le` and `abs_cofactorCount_add_tail_sub_prime_sub_mean_le` are kernel-checked with the standard axioms. [Formal proof](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheCompletedCofactorRowRetainsThePrimeError.lean)
