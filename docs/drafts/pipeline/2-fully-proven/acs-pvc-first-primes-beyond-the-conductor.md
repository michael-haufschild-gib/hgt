# Removing first primes at most the conductor

Let \(B_{>}(N)\) be the original seventeen-ninths prefix restricted to \(p>n\). On every fragment ending at \(M\), the removed price is \(O(M^3(1+\log(2M))^2)\). Thus the full one-sided \(11/3\) and \(3+\eta\) targets can both be tested using \(B_{>}\). Each remaining product \(q=pv\) has exactly one prime divisor above \(n\), since \(v\le n<p\). Bounding \(B_{>}\) remains open.

**Proof.** Write \(L\) for the spline horizon, \(f\) for the dyadic spline and \(U=\lfloor n^{17/9}\rfloor\). Eventually \(U\ge\mathrm{productLower}(1,L)\), so a product \(q>U\) first enters at \(k=q\) and remains through \(L\). For \(4<p\le n\) all \(v\le n\) have \(pv\le n^2\le L\). Summing in \(k\) first gives the exact weight
\[
  n^{-1}\{V_{L+1}(pv/n^2)+f(pv/n^2)\}.
\]
The second summand is the returned first endpoint. Since \(W(0)=1\) and \(f(0)=0\), the one-cell mesh is \(V_1=-f\). The numerator is therefore \(V_{L+1}-V_1\), with the same uniform variation estimate on both terms. The cofactor interval is exactly \((\lfloor U/p\rfloor,n]\).

The signed cofactor coefficients \(a_p(v)=\mathbf1_{p\nmid v}\mathrm{innerJump}(1,v)\) have uniformly bounded prefixes. Subtract the multiples of \(p\) from a full prefix and apply the large-prime dilation identity. For \(d=p/n^2\), the mesh \(V_b(vd)\) is bounded and its adjacent differences are \(O(1/v)\) uniformly in \(b\) and \(d\). This follows by comparing \(xV_b((v+1)d/x^2)\) at \(x=1\) and \(x=\sqrt{1+1/v}\) using its bounded conductor derivative. The spline \(f\) is bounded and Lipschitz, so its differences are \(O(d)\) with \(nd\le1\). Abel summation on the cofactor interval therefore costs \(O(1+\log(2n))\), including the sample at each end. Summing \(\log p\) over \(p\le n\) costs at most \(n\log(2n)\). After the \(n^{-1}\) normalization and the exterior \(n^2\), summation proves the fragment bound. The finitely many initial conductors have bounded total cost.

**Lean status.** The returned endpoint and bounded cofactor prefixes are available. The mesh variation and the complete small-first-prime estimate await kernel verification. [First quotient endpoint](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheEndpointAtQuotientZero.lean) · [Prime multiples in the cofactor prefix](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheInnerWeightOnLargePrimeMultiples.lean) · [Real mesh](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheIntegralOnTheRescaledProductShell.lean)
