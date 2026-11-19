# The moving product and cofactor cuts on odd products

Fix the first-prime cutoff \(P\), strict product cutoff \(U\), and closed cofactor cap \(n\). Let \(Q(0)=0\), \(Q(j)=\mathrm{centeredPrimeWeight}(1,j)\) for \(j>0\), and \(d(j)=Q(j)-Q(j-1)\). Set \(z_k=2^{-k}\) for \(0\le k<7\), \(z_7=2^{-6}\). For odd \(t\),
\[
 \sum_{k=0}^7 z_k d(2^kt)=\mathbf1_{t=1}.
\]
Differencing the four quotient stencil rows gives a unit mass and a linear combination of divisor steps with \(a=1,64,129,64\cdot129\). Each step \(\mathbf1_{a\mid j}-2\mathbf1_{2a\mid j}\) telescopes against these weights. Its endpoint vanishes since \(a\mid2^7t\) iff \(a\mid2^6t\) for all four moduli. In the product–quotient sum with odd part \(u\), applying this identity to the outer quotient leaves only the inner product with odd part \(u\). For each ordinary prime \(p\mid u\) with \(p>\max(4,P)\), put \(v=u/p\). Discard \(p\mid v\) by coprimality. With \(a=1,2,4\), let \(J_a=\mathbf1_{au>U,\;av\le n}\). Put \(c=\mathrm{cofactorDyadicCoefficient}\). With weights \(1,1/2,1/2\) on the three product dilations, the coefficient of \(\log p\) is
\[
 (\mathbf1_{v=1}-1)J_1+\tfrac12(1-c)J_2+\tfrac12(1+c)J_4 .
\]
The verified identity retains the strict lower product cut and the closed upper cofactor cap before summing over primes. With the cap inactive, the successive values for \(u\le U/4\), \(U/4<u\le U/2\), \(U/2<u\le U\), and \(U<u\) are \(0,(1+c)/2,1,\mathbf1_{v=1}\), respectively.

For \(n\ge4\), write \(\lambda_P(u)=\log u\) if \(u\) is itself an eligible prime and zero otherwise. The weights \(\alpha=(1-c)/2\) and \(\beta=(1+c)/2\) are positive and sum to one. Below or at \(U\) only the two positive terms survive. Above \(U\) the combined reading is exactly
\[
 \lambda_P(u)-
 \sum_{n/2<v\le n}\log p-
 \beta\sum_{n/4<v\le n/2}\log p ,
\]
where both sums retain \(p\mid u\), \(p>\max(4,P)\), \(v=u/p\), and \(p\nmid v\). The lower product endpoint gives a surplus on \((U/4,U]\). The cap gives a deficit in two cofactor intervals above \(U\). For \(U\le P\) and \(4u\le nP\), the combined reading recovers \(\lambda_P(u)\) exactly on every odd product, including equality at either cutoff. Indeed every eligible cofactor satisfies \(4v\le n\). [Outer quotient inversion](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMovingProductAndCofactorCutsOnOddProducts.lean#L136) · [Two cofactor bands](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMovingProductAndCofactorCutsOnOddProducts.lean#L266) · [Singleton through both cuts](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMovingProductAndCofactorCutsOnOddProducts.lean#L349)

The Lean declarations are `positive_quotient_dyadic_recovery`, `above_product_cut_two_cofactor_bands`, `below_product_cut_two_cofactor_caps`, `clipped_product_quotient_boundary_signs`, and `ordinary_prime_above_both_moving_cuts`.
