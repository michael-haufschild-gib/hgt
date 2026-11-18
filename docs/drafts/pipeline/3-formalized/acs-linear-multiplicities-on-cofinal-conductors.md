# Sections at linear multiplicities on arbitrarily late conductors

There exist fixed positive constants $c,\gamma$ and arbitrarily large square conductors $n$ such that every integer $1\le m\le cn$ has ordinary log generator at most $-\gamma n^2$ and at least $2\lfloor\exp(\gamma n^2)\rfloor+1$ sections at the original radius. The same conductors have a nonzero original section for all sufficiently large multiplicities.

The signed Weil degree $Q(D_n)$ is nonnegative on arbitrarily large conductors with an eventual tail of original sections, by the nonnegative Tate count there. The continuous ordinary prime contact $P(D_n)$ differs from $-Q(D_n)$ by an absolute constant. Hence $P(D_n)$ is bounded above on that same set.

Let $V$ be the exact ordinary floor loss. Second-order quadrature gives $\log d_{\rm ord}(mD_n)+V=m^2P(D_n)+O(n)$, uniformly in $m$. The positive pole degree is zero. The full logarithmic excess over the radius costs at most $O(m^2)$ more. For every $m\le n$ the floors save $V\ge b n^2$. For $m>n$ the allowance $m^2$ covers the quadratic saving. Thus there exist $A,\delta>0$ such that both the ordinary log generator and the full log excess over the radius are at most $Am^2-\delta n^2$ for every positive $m$ on the same conductors. Choosing $c$ small gives the stated exponential bounds.

## Lean

`cofinal_square_height_with_quadratic_saving` gives the simultaneous bound for all positive multiplicities. `cofinal_all_square_sections_at_linear_multiplicities` gives the exponential section count and the eventual original-radius fit on the same conductors. [LinearMultiplicitiesOnCofinalSquareConductors.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/LinearMultiplicitiesOnCofinalSquareConductors.lean)
