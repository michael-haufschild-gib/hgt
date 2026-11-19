# Square-root truncation of the rough cofactor

- **Stage** 1-in-progress
- **Target** Remove a specified part of the actual Möbius prefix at square-root-plus-epsilon cost, uniformly in the sharp cutoff.

At \(X\) put \(y=\lfloor\log(X+1)\rfloor^2\). For a squarefree integer \(n\le X\), write \(d=\gcd(n,P(y))\), \(r=n/d\). The smooth part and rough part are unique. For \(1/2<s<1\), the unsigned count with \(r\le Y\) is at most
\[
  X^s E_s(y)\sum_{1\le r\le Y}r^{-s}
  \ll_s X^s E_s(y)Y^{1-s}.
\]
Count the admissible smooth cofactors through \(\lfloor X/r\rfloor\) by Rankin's inequality. Forgetting the coprimality of \(r\) only increases this upper bound. Since \(E_s(y)=X^{o(1)}\), for every \(0\le\gamma\le1\) the count with \(r\le X^\gamma\) has exponent at most \((1+\gamma)/2\). In particular every subpower rough cofactor can be dropped at square-root-plus-epsilon cost. This gives the estimate on the indicated portion of the actual signed prefix unconditionally. The opposite portion carries the open remainder.

The upper exponent is attained in the unsigned count. For \(0<\gamma<1\), take a smooth box of size \(H\) from the critical cofactor construction and independently one prime \(r\in(T/2,T]\), where \(T=\lfloor H^{\gamma/(1-\gamma)}\rfloor\). At \(X=HT\) these primes exceed \(y(X)\) and satisfy \(r\le X^\gamma\). All products are distinct. There are \(\gg T/\log T\) such primes and exponentially more than \(\sqrt H\) squarefree smooth cofactors along the sequence of critical boxes. This excess absorbs \(\log T\), so even the endpoint \(O(X^{(1+\gamma)/2})\) fails. At \(\gamma=0\) the slice is exactly the squarefree smooth population. At \(\gamma=1\) it contains every squarefree integer.
