# Collective polar-packet coercivity — paper proof

Status: dependency-closed paper proof; exact finite-N coercivity and inverse-mass bound pass targeted Lean source audit (exit 0). Main WP02 estimate remains open.

Let Psi be the corpus's fixed smooth nonzero real bump supported in [-1/4,1/4]. Put

    P = integral Psi^2 >= 0,
    D = integral (Psi'')^2 > 0,
    R = P/D.

For N>=0 put w=1/(N+1), x_m=log(m)-log(N)/2, and use only 1<=m<=N. For arbitrary complex coefficients c_m define

    G(x) = sum_m c_m Psi((x-x_m)/w),
    F(x) = (d^2/dx^2-1/4)G(x).

These are the existing common-width polar resonators. Every sum is finite. They are smooth, compactly supported, and Fhat vanishes at +/-i/2. No positivity assumption is made.

## Exact mass comparison

Distinct x_m differ by at least w. Each summand has support radius w/4. Thus supports are disjoint. Writing S=sum |c_m|^2 gives

    ||G||_2^2 = w P S,
    ||F||_2^2 = K_w S,
    K_w = integral |Psi''(x/w)/w^2-Psi(x/w)/4|^2 >= D/w^3.

The last inequality follows by expanding the square and integrating by parts: the cross contribution is positive. Therefore ||G||_2^2 <= R w^4 ||F||_2^2. Fourier Plancherel preserves this comparison, including its 2*pi factor. This calculation is in physical space; no archimedean Fourier cross term has been discarded.

## Pointwise archimedean bound

The corpus proves Re digamma(1/4+iy) >= log(2+|y|)-C_d. With

    C_a = C_d + log(2) + log(pi)

one obtains A(tau/(2*pi)) >= log(2+|tau|)-C_a, because 2+|tau| <= 2(2+|tau|/2).

For any r,q>0, log(r/q) <= (r/q)^4/4. Indeed apply log(x)<=x-1 to x=(r/q)^4 and discard -1/4. Hence

    log(r)-C_a <= A(tau/(2*pi)) + r^4/[4(2+|tau|)^4].

The exact Fourier multiplier is

    |Fhat(tau)|^2 = (tau^2+1/4)^2 |Ghat(tau)|^2.

Since (tau^2+1/4)^2 <= (2+|tau|)^4, multiply the scalar inequality to get

    (log(r)-C_a)|Fhat|^2
       <= A(tau/(2*pi))|Fhat|^2 + (r^4/4)|Ghat|^2.

All three displayed integrands are integrable for these smooth compactly supported functions, by the existing Weil/Fourier library. This avoids any additional logarithmic integrability assertion.

## Uniform collective inequality

Integrate and choose r=1/w=N+1. The mass comparison gives

    archEnergy(F) >= (log(N+1)-C_a-R/4) integral |Fhat|^2.

This includes N=0 and all zero coefficients, when both masses are zero. C=C_a+R/4 is explicit, independent of N and coefficients. For N+1>=exp(C), every packet has nonnegative archimedean energy. If the Fourier mass is bounded below while N tends to infinity, its energy diverges. Thus arbitrary collective interference in this packet space cannot create bounded-energy near-null sequences with mass bounded below.

## Frontier and novelty audit

This is a restriction on one concrete packet family, not a positivity theorem for all polar tests or all exposing-ray mixtures. General tests can have compact polar primitives with no O(w^4) inverse-mass bound. That is precisely where this argument stops. Nothing implies the WP02 dual bound or RH.

The logarithmic uncertainty parent is classical; Laptev–Weth, Spectral properties of the logarithmic Laplacian (2021), gives related domain bounds and scaling. Their stated dimension range must not be silently changed. Our proof above is directly one-dimensional and uses the corpus's concrete polar primitive. Scientific novelty beyond parent theory is unestablished; the useful corpus delta is a coefficient-uniform lower bound complementary to the existing Toeplitz upper bound.

Source: https://link.springer.com/article/10.1007/s13324-021-00527-y
