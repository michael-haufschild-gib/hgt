# Vertical contacts for signed conductor divisors

- **Stage** 1-in-progress
- **Route** ACS arithmetic section count on integer translates of the cubic spline.

For conductor (n), use the integral graph (Y=G_n(T)), where
(G_n(T)=\sum_{d\mid n}\operatorname{rad}(d)T^d). Its horizontal degree is (n).
The content of (G_i-G_j) is (p) at any proper ratio (p^r), and (1) at every other distinct pair. The first changed power of (p) gives a coefficient of absolute value (p). Two changed primes force coprime coefficients. Gauss's lemma then computes the vertical order of the Sylvester resultant for two thickened unions, including arbitrary multiplicities.

At mesh index (i) use signed lower weight (\sqrt i\log(1+1/i)f_i) and upper weight (g_i/\sqrt i). Their product at (j=it) supplies the log-cell measure and the factor (1/\sqrt t). Round both multiplicities after dilation. On a mesh starting at (\lfloor\sqrt m\rfloor), the normalized rounding error is (O_{f,g,B}(m^{-1/2})). Compare the logarithms of the two oriented restriction orders with the full smooth prime pairing.

**Remaining ACS problem.** Realize the debit from same-sign contacts together with the real-place diagonal and both pole moments as the size of one effective object. Horizontal degree alone does not give that comparison.
