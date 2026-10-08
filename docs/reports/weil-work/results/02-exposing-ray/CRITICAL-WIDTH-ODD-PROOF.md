# Cycle 16 paper proof: literal opposite tail and shorter positive residual

Status: source and complete opposite-tail statements formalized in WeilWorkExposingRayCriticalOddSource and WeilWorkExposingRayCriticalOddTail; both final leaf/cache audits pass. This proves a source and opposite tail, not complete opposite-ray realization or WP02. The optional recentered compact aperture and full residual pole observations below are paper consequences; the exported compact polar and energy theorems use aperture L+1.

## Actual filters and exact polarity

Write q=polarWeight(1)=1/(2cosh(1/2)), h=cosh(1/4), and T_s U(t)=U(t-s). For a real profile U set

    E(U)=U-q(T_1+T_-1)U,
    G(U)=q[T_1-T_-1-2h(T_(1/2)-T_(-1/2))]U,
    H(U)=U-2hq*T_(-1/2)U+2hq*T_(1/2)U-2q*T_1 U.

Direct linear expansion gives H=E-G. With d=cosh(1/2)=2h²-1 and P_s=1-(T_s+T_-s)/(2cosh(s/2)), the exact factorizations are

    E=P_1 U,
    G=-(h/d)(T_(1/2)-T_(-1/2))P_(1/2)U,
    H=(2h/d)(h+T_(1/2))P_(1/2)U.

Thus both half-poles vanish for all three filters whenever the displayed transforms are defined: P_(1/2) has the exact scalar zero at +/-i/2, and translations preserve it. Finite translate Fourier linearity is justified by the corpus full-theta envelope (U=Phi) or continuous compact support (U=Phi*chi_L). For full Phi, every Weil zero evaluation vanishes termwise by the existing literal radical transform identity. No RH or positivity assumption is used.

For U_L=Phi*chi_L and L>=0, all filtered sources are C² and supported within [-L-1,L+1]; their actual half-poles vanish, so they are genuine IsPolarTest(L+1) sources. H has smaller translation width3/2; after recentering by1/4 its support radius is L+3/4. Polarity and archimedean energy are invariant under this recentering.

## Complete all-lag identity

For even real U, E(U) is even, G(U) is odd, and H=E-G. The symmetrized mixed correlations vanish exactly. For example, changing variable t to y-t shows

    integral E(t)G(t-y) dt = -integral G(t)E(t-y) dt.

All integrals exist: full Phi and all finite translates have global exponential envelopes; U_L and its translates are continuous and compact. Expanding the full product therefore gives, at EVERY real lag y,

    corr(E,E)(y)+corr(G,G)(y)=corr(H,H)(y).

Equivalently, expand the finite covariance coefficients on the half-step lattice; coefficients at every lag agree. This algebraic filter identity actually holds for every real common profile with integrable translated products, even without evenness. In particular there is no dropped cross term, discarded negative region, or asymptotic-only equality.

The same finite coefficient identity gives a pointwise real-frequency identity

    |FT(E)(tau)|²+|FT(G)(tau)|²=|FT(H)(tau)|².

Each compact C² source has an integrable product with the signed archimedean symbol. Integrating that identity gives the exact signed energy identity A(E_L)+A(G_L)=A(H_L). No sign for A(H_L) is asserted. This identity identifies the surviving energy obligation instead of treating opposite tail sign as cheap realization.

## Literal normalization and faster remainder

For full U=Phi, E(U)=P_1Phi and its actual atom trace is

    e(n)=polarExposingKernel(1,log n)+polarExposingKernel(1,-log n).

The all-lag identity gives atom(G,n)+e(n)=atom(H,n). H is an order-zero derivative packet with translation positions [-1/2,0,1/2,1], hence radius3/4 after recentering. The cycle15 uniform packet theorem yields, for every 0<r<2*pi*exp(-3/2), a constant C_H with |atom(H,n)|<=C_H exp(-r*n), n>=1.

The literal exposingWeight is e(n)+sum_(k>=1)2^-k e_k(n). For k>=1, c_k=1/(k+1)<=1/2. Each P_(c_k)Phi is an order-zero packet in [-1/2,1/2] with coefficient l1 mass 1+2polarWeight(c_k)<=2. The same uniform packet theorem yields one constant, independent of k, at every rate below 2*pi*exp(-1). Dyadic summability bounds the full infinite remainder, with no sign assumption on individual terms.

Combining these two estimates gives the main constructive statement:

    for every 0<r<2*pi*exp(-3/2), exists C>0, all n>=1,
    |atomCoeff(G,n)+exposingWeight(n)| <= C exp(-r*n).

The interval between the literal rate r0=2*pi*exp(-2) and the new remainder endpoint is nonempty. Choose r0<b<r and use the proved lower envelope w(n)>=D exp(-b*n). Then |atom(G,n)/w(n)+1|<=C/D exp(-(r-b)n), eventually. Thus the ratio tends to -1, with eventual strict negativity of atom(G,n), while both polar and zero-carrier identities hold exactly. This is exact tail proportion, stronger than equality of logarithmic rates or a tail sign theorem.

## Hostile audit and remaining core

The filter algebra is elementary; no novelty claim is made for parity, covariance expansion, or complementary filters in general. The source-specific result is literal opposite exposing-tail normalization with a strictly faster complete remainder, together with exact positive residual and actual compact polar sources. All normalizations refer to actual atomCoeff, without a hidden 1/sqrt(n); the dual convention's2*pi can be paid by a constant nonnegative mixture scaling.

Full G is not compact. Compact G_L preserves poles exactly, but truncation error must still be quantified at the required aperture if used in a finite realization. Faster tail error is not zero trace, and the finite-head discrepancy is fixed as L grows. A fixed head repair cost does not fit exposingTail(N)->0. The signed residual energy A(H_L) has no established sign or sufficiently small bound. No complete opposite-ray family, universal WeilDualBound, cone nonemptiness or RH conclusion follows yet.
