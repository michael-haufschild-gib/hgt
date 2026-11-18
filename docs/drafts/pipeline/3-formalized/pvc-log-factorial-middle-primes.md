# A fixed power interval for both Vaughan counts

**Stage** 3-formalized. **Type** Theorem (Lean). **Route** PVC.

There is an absolute $K$ with the following property. For $N\ge1$, put $R=\lfloor N^{1/4}\rfloor$. In the paired Vaughan count, replace each divided Chebyshev error $\psi(X)-X$, $X=\lfloor N/d\rfloor$, by
$$
 T_R(X)=\sum_{R<m\le X/R}\Lambda(m)\,[1-B_R(\lfloor X/m\rfloor)].
$$
The total replacement error is at most $K\sqrt N\sum_{d\le W}|b_V(d)|$ for every $V,W$. The window is independent of the desired exponent $b>1/2$. Its signed weights are explicit and its long variable runs only over prime powers.

**Construction.** Write $H=\sum_{j\le R}\mu(j)/j$, $S=\sum_{j\le R}(\mu(j)/j)\log(R/j)$, and $c=R(1-S)/\log2$. Take
$$
 B_R(t)=\sum_{j\le R}\mu(j)\lfloor t/j\rfloor-RH\lfloor t/R\rfloor+
 c\big(\lfloor t/R\rfloor-2\lfloor t/(2R)\rfloor\big).
$$
For $1\le t<R$, Möbius inversion gives $B_R(t)=1$. The harmonic moment of the full coefficient list $a_j$ is zero and its logarithmic moment $-\sum a_j\log j/j$ is one. Also $\sum |a_j|\le R+R|H|+3|c|=O(R)$ by $|H|\le1$ and $S\to1$. Consequently $|B_R(t)|=O(R)$ for every $t$, by subtracting $t\sum a_j/j=0$ before rounding.

**Proof.** The total pairing $\sum_{m\le X}\Lambda(m)B_R(\lfloor X/m\rfloor)$ is $\sum_j a_j\log(\lfloor X/j\rfloor!)$. Replacing each log factorial by $(X/j)(\log X-\log j-1)$ costs at most $3+\log j+2\log X$. The two moments make the sum of the main terms exactly $X$. Hence the complete pairing differs from the integer density by $O(R(1+\log(2R)+\log X))$. The complementary weight $1-B_R$ vanishes when $X/R<m\le X$. Removing $m\le R$ costs $O((1+R)\psi(R))=O(R^2)$. Both errors are $O(\sqrt N)$ when $X\le N$ and $R=\lfloor N^{1/4}\rfloor$. Sum against the actual short coefficients at either width.

**Open.** Bound the signed sum $\sum_d b_V(d)T_R(\lfloor N/d\rfloor)$ at both widths. The square-root estimate controls the entire error of the replacement.

**Lean.** `abs_mangoldt_prefix_sub_count_le` evaluates the complete prime pairing. `quarter_power_middle_interval` gives the uniform square-root estimate. [Log-factorial weights for the middle prime interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/LogFactorialWeightsForTheMiddlePrimeInterval.lean)
