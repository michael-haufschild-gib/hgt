# The noncoprime part of the ordinary prime pair sum

Write \(I_N=(\sqrt N,N]\cap\mathbb N\), \(e_n=\sum_{n/2<k\le n}\Lambda(k)/k-\log2\), and let \(\Theta\) be the supremum of the real parts of the zeta zeros. The [reciprocal octave](acs-pvc-one-sided-mass-in-the-reciprocal-prime-octave.md) gives the lower bound on the negative mass used below.

For \(M\in I_N\) set \(a_d=\mathbf1_{d\ \mathrm{prime}}\log d-1\), \(f_M=\sum_{M<d\le2M}a_d/d\), and \(w_N(d,e)=\#\{M\in I_N:M<\min(d,e),\ \max(d,e)\le 2M\}\). Removing proper powers and comparing the harmonic sum to \(\log2\) gives \(|e_{2M}-f_M|\ll M^{-1/2}\). The cost in the Euclidean norm over \(I_N\) is \(O(\sqrt{\log(2N)})\). The diagonal in \(\sum_M f_M^2\) costs \(O(\log^2(2N))\): \(w_N(d,d)\le d\), and partial summation of the Chebyshev upper bound controls \(\sum_{p\le 2N}(\log p)^2/p\). All remaining terms form the signed sum
\[
 V(N)=2\sum_{d<e\le2N} \frac{a_d a_e}{de}\,w_N(d,e).
\]
Both endpoints are shared; \(w_N(d,e)>0\) forces \(e<2d\). At every actual right zero, the negative-mass lower bound on even indices and Cauchy–Schwarz give \(V(N)\gg_\rho N^{2\Re\rho-1}\) for all late \(N\). Conversely, the pointwise bound above \(\Theta\) gives \(\lim\log(1+|V(N)|)/\log N=2\Theta-1\), including under RH. A **one-sided upper** bound \(V(N)\ll N^{2/3}\) at arbitrarily large endpoints would therefore suffice for \(11/3\). Diagonal terms, proper powers and the discrete density all fit below that allowance. The signed correlation between distinct factors remains open.

At the intermediate exponent both ends of the pair interval can be removed in absolute value. On \(D\le d<2D\), pairs with \(0<e-d\le h\) cost \(O(h\log(2D))\). Indeed \(w_N(d,e)\le d\), \(|a_e|\ll\log(2D)\), and \(\sum_{D\le d<2D}|a_d|\ll D\). Pairs with \(0<2d-e\le k\) cost \(O(k^2\log(2D)/D)\) for \(k\ge1\), because the common interval has at most \(d-\lceil e/2\rceil\le(2d-e)/2\) entries. Take \(h=D^{2/3}/\log(2D)\) and \(k=D^{5/6}/\sqrt{\log(2D)}\). Both costs summed over dyadic \(D\) are \(O(N^{2/3})\), uniformly in the original terminal \(N\). Only the signed covariance in the intervening pair range needs a new estimate for \(11/3\).

**A linear term from noncoprime pairs.** Both entries of a distinct noncoprime pair in \((M,2M]\) are composite. A prime dividing its partner would force that partner to be at least twice the prime. Thus \(a_da_e=1\) on these pairs. Write \(L(t)=\sum_{t<j\le2t}1/j\). Their contribution at a single terminal, counting both orders as in \(V\), is exactly
\[
 L(M)^2-\sum_{M<d\le2M}d^{-2}
 -\sum_{h\le2M}\frac{\mu(h)}{h^2}L(M/h)^2 .
\]
Indeed the last sum counts all ordered coprime pairs by the common-divisor identity, and the diagonal is disjoint from them for \(M\ge1\). For \(B=\lfloor2M/h\rfloor\), \(L(M/h)=H_B-H_{\lfloor B/2\rfloor}\) is the alternating harmonic sum through \(B\). Thus the row error has sign \((-1)^{B+1}\) and size at most \(1/(B+1)\le h/(2M)\). Since \(L+\log 2\le3\) here, replacing all squared rows by \((\log2)^2\) costs at most \(3(1+H_{2M})/(2M)\), including the full row. The diagonal costs at most \(1/M\), and extending the Möbius series beyond \(2M\) costs \(O(1/M)\). Consequently the noncoprime contribution to \(V(N)\) is
\[
 (1-\zeta(2)^{-1})(\log 2)^2 |I_N|+O(\log^2(2N)).
\]
Lean verifies the exact common-divisor sum and a uniform numerical error bound. For every set of terminals \(S\subseteq\{1,\ldots,N\}\), the absolute error from \(|S|(1-6/\pi^2)(\log 2)^2\) is at most \(5(1+\log(2N))^2\). [Exact identity](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheNoncoprimePartOfTheOrdinaryPrimeOctave.lean#L79) · [Arbitrary terminal sets](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheNoncoprimePartOfTheOrdinaryPrimeOctave.lean#L291)

The coprime pairs must cancel this linear term to within the \(N^{2/3}\) allowance. Discarding noncoprime pairs in absolute value costs order \(N\).

For the full pair sum, the Hardy–Littlewood congruence prediction contributes \(-3(\log N)^2/16+O(1+\log N)\) on these terminals. The actual prime diagonal cancels its logarithmic square. The proof on paper uses a probability measure on squarefree divisors and the exact remainder at each right endpoint. [Congruence term and diagonal](acs-pvc-the-congruence-term-in-the-reciprocal-prime-pair-sum.md)
