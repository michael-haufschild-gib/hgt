# Signed moments left by reversible prime exchanges

- **Stage** 1-in-progress
- **Question** What signed cancellation survives on the fixed divisors of arbitrarily many disjoint prime ranges?

Write \(Q_B=\prod_{p\in B}p\) for a prime range with a nonempty table of distinct singles \(p_w\) paired to distinct products \(w=qr\). Let \(L_B\) be its divisors after removing exactly the table endpoints. Their logarithmic generating function is
\[
 H_B(s)=\sum_{d\in L_B}\mu(d)d^{-s}
 =\prod_{p\in B}(1-p^{-s})+\sum_w(p_w^{-s}-w^{-s}).
\]
At zero this vanishes. Its derivative is \(\log(\prod_w w/\prod_w p_w)\). This is nonzero even if individual exchanges point in opposite directions: equality of those products would equate integers with respectively \(2\#\{w\}\) and \(\#\{w\}\) prime factors counted with multiplicity. At least two primes belong to every active band, so the full Euler product has zero derivative there.

For \(m\) disjoint active bands the combined fixed-divisor polynomial is the product of these \(H_B\). Thus every signed logarithmic moment below \(m\) vanishes, and the signed moment of degree \(m\) is exactly \((-1)^m m!\prod_B H'_B(0)\ne0\). The analogous polynomial in the number of prime factors has the explicit local factor \((1-z)^{|B|}+\#\{w\}\,z(1-z)\). These identities concern the actual fixed patterns of the first-eligible involution.

At cutoff \(X\), uniquely write a squarefree fixed integer as \(ad\), where \((a,\prod_B Q_B)=1\) and \(d\) is a combined fixed divisor. Its signed contribution is the corresponding finite difference of the coprime Möbius prefix at the points \(\lfloor X/d\rfloor\). Thus polynomial approximation of this prefix in the logarithmic divisor variable can exploit every vanishing moment. The discontinuous remainder and the signed crossings of matched pairs still need bounds at the same sharp cutoff.
