# Small complementary factors through the square-root product window

**PVC · Formalized.** Put $q=\lfloor X^{10^{-6}}\rfloor$. For all sufficiently large $X$, $1\le R\le X^{1/400000}$, $\lfloor\sqrt X\rfloor\le L$, and $U\le X^{1/2+10^{-9}}$, the ordinary prime sum over $1\le v\le q$, $L<pv\le U$, $p>F$, with coefficient $g_D(v)\log(p)w_R(\lfloor X/(pv)\rfloor)$, costs $O((D+1)X^{0.499701})$ uniformly in $F$.

**Proof.** Put $T=\lfloor X/v\rfloor$. Then $X\le 2Tv$ and $2vX^{0.99999}\le X$ for large $X$, so $T\ge X^{0.99999}$. The upper prime endpoint $\lfloor U/v\rfloor+1$ is at most $2T^{0.50001}$. At the lower endpoint, $vT^{0.49999}\le X^{0.499991}\le\sqrt X\le L+1\le v(\lfloor L/v\rfloor+1)$. Also $R\le T^{1/100000}$. Thus the [sharp prime interval estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/OrdinaryPrimeCancellationInTheSquareRootBand.lean) gives $O(X^{0.4997})$ for each slice. There are at most $X^{10^{-6}}$ slices and $|g_D(v)|\ll D+1$.

**Lean.** [`short_complement_window_bound`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ShortComplementsInTheSquareRootProductWindow.lean).
