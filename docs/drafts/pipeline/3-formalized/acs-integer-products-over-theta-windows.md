# Integer products containing every square conductor in a dyadic band

Let $q_n=d_{\rm ord}(nD_n)$. There are fixed integers $K,B>0$ and integer exponents $0\le k_{N,n}\le K$ determined by theta alone such that, at every sufficiently large $N$,
\[
 B^{-N^3}\le\prod_n q_n^{k_{N,n}}\le B^{N^3}.
\]
Every conductor $N\le n\le2N$ occurs. The product uses conductors $2\le n\le1+\lceil N^{17/16}\rceil$. The sharp prefix product has unit weights through its endpoint and still needs its cubic bound. [Sharp prefix](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheSignedProductOverSquareConductors.lean)

## Proof

Write $T=2\log N$, $M=\lceil N^{17/16}\rceil$, and $a_n=\int_{2\log(n-1)-T}^{2\log n-T}\Phi(x)\,dx$ for $n\ge2$. The cell length lies in $[2/n,4/n]$. On it $\Phi(x)\le C e^{3x/2}\le C(n/N)^3$. On the central band $N\le n\le2N$ all cells lie in $[-2,2]$, where $\Phi\ge c>0$. Thus $w_n=4N^3a_n/(cn^2)$ is globally bounded and at least one on the central band. Set $k_{N,n}=\lfloor\sum_{j=2}^nw_j\rfloor-\lfloor\sum_{j=2}^{n-1}w_j\rfloor$ through the cutoff. Cumulative rounding preserves the integer upper and lower bounds.

For $L(u)=4h(u)-2h(u+\log4)$ let $G(n)=n^2L(2\log n)$. The shell width $w\le3/8$ gives $|L(2\log n)|\ll n^{3/4}$, and a unit root displacement costs $O(n^{-1/4})$. Therefore $|G(n+1)-G(n)|\ll n^{7/4}$. The error under one cumulative rounding against $G$ is at most its terminal absolute value plus its total variation, $O(M^{11/4})=O(N^3)$. [Root displacement](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheSignedDegreeAtTheNearestUpperSquare.lean)

The unrounded reading $N^{-3}\sum w_nG(n)$ is bounded. Replacing each cell by its upper-root trace costs $O(\int\Phi)$. The full translated theta mean of $L$ is zero. On the omitted left tail $x\le-T$ one has $|T+x|\le|x|$. On the right tail $x>2\log(M+1)-T\ge(\log N)/8$ one has $(T+x)/2\le17x/2$. The fixed theta moment of order $17/2$ therefore pays both omitted tails. [Theta annihilation](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheThetaMeanOfTheSquareTrace.lean)

Finally $|\log q_n+G(n)|\ll n^2$ by the ordinary-contact estimate and square sampling. The unrounded quadratic mass is $O(N^3\int\Phi)$, and cumulative rounding against $n^2$ costs $O(M^2)$. Hence $|\sum k_{N,n}\log q_n|\ll N^3$. Exponentiation supplies the integer base. [Arithmetic comparison](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneMultiplicityPerSquareConductor.lean)

[Lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/IntegerProductsOnEverySquareConductorScale.lean) proves `rational_theta_square_generator_product_bounds` and `actual_square_generator_products_at_every_scale`.
