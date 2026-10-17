# Annular regularization and signed prime–polar Chebyshev transport

## Domain and exact statement

Let f be any real continuous compactly supported source, h its autocorrelation,
and R=h(0). Choose arbitrary a,d>0 and L≥0. Define

\[
 H(t)=\frac1d\int_a^{a+d}h(t+y)\,dy,\qquad
 V(t)=\frac{h(t+a+d)-h(t+a)}d,
 \quad E(x)=\psi(e^x)-e^x.
\]

Define the actual finite-window signed pairing

\[
 D_L(k)=\sum_{2\le n\le e^L}\frac{\Lambda(n)}{\sqrt n}k(\log n)
       -\int_0^L 2\cosh(x/2)k(x)\,dx.
\]

Then H is continuously differentiable, H'=V, and

\[
 D_L(H)=H(0)+e^{-L/2}H(L)E(L)
 -\int_0^L e^{-x/2}\bigl(V(x)-H(x)/2\bigr)E(x)\,dx
 -\int_0^L e^{-x/2}H(x)\,dx. \tag{1}
\]

No source derivative, prime-correlation sign, grid-zero, asymptotic estimate,
or energy bound occurs in this statement. Endpoint L may itself be a prime-power
logarithm: the sum includes that atom, and E(L) uses the same right-continuous
convention. The formal construction initially takes L=log(N+2), covering every
integer truncation and arbitrarily large windows.

Let

\[
 K_{a,d}(f)=\frac1d\int_a^{a+d}\sqrt{2R(R-h(y))}\,dy,\qquad
 M_L=\sum_{2\le n\le e^L}\frac{\Lambda(n)}{\sqrt n}
                +\int_0^L2\cosh(x/2)\,dx.
\]

Then

\[
 |D_L(h)-D_L(H)|\le M_LK_{a,d}(f). \tag{2}
\]

For every η>0 the local cost satisfies the archimedean estimate

\[
 K_{a,d}(f)\le
 \eta\int_a^{a+d}(R-h(y))w_{\rm arch}(y)\,dy
 +\frac{R}{2\eta d^2}\int_a^{a+d}e^{-y/2}\sinh y\,dy. \tag{3}
\]

The last integrand is at most y exp(y/2). All integrals above are finite on
these compact annuli, even if the full Lévy energy of f is infinite.

## Dependency-closed paper proof

**Regularity.** Continuity of the compact-source autocorrelation follows from
continuity of translation in its convolution. If P(t)=∫₀ᵗh(u)du, then
H(t)=(P(t+a+d)−P(t+a))/d. The fundamental theorem gives H'=V, and V is continuous.

**Arithmetic Stieltjes identity.** Put G(x)=exp(−x/2)H(x). On the finite window,
the cumulative atom mass is ψ(exp x). For each atom t=log n,
G(t)=G(L)−∫ₜᴸG'(x)dx. Multiply by Λ(n), sum the finite set, and interchange
finite sum and integral. This yields

\[
 \sum_{2\le n\le e^L}\Lambda(n)G(\log n)
 =G(L)\psi(e^L)-\int_0^L G'(x)\psi(e^x)\,dx.
\]

Values at the finitely many atom positions do not affect the Lebesgue integral.
The weight exp(−log(n)/2)=1/√n gives the literal requested prime measure.

**Continuum term and boundary.** Ordinary integration by parts gives
∫₀ᴸG(x)eˣdx=G(L)eᴸ−G(0)−∫₀ᴸG'(x)eˣdx. Subtract this from the arithmetic
identity and use G'=exp(−x/2)(V−H/2). Since
2cosh(x/2)=exp(x/2)+exp(−x/2), the remaining polar term is exactly the last
integral in (1). This proves (1), including both endpoints.

**Local transport.** Pillar XIV gives |h(t+y)−h(t)|≤sqrt(2R(R−h(y))) for every
t,y. Integrate on the annulus and divide by d to obtain |H(t)−h(t)|≤K uniformly
in t. Both original measures in D_L are positive and finite; the triangle
inequality proves (2). For (3), apply the scalar Young inequality with weights
ηw_arch(y) and 1/d, then use Pillar XV's exact reciprocal identity. Integrate
over the positive annulus; no improper integral or unknown integrability enters.

## What this resolves and what remains

The regularization is performed on the test correlation, retaining the actual
prime atoms. It supplies an explicit derivative for the global discrepancy
pairing while charging the change in the original signed functional to local
origin increments. This removes the derivative-admission gap between the two
transport mechanisms for compact continuous sources.

M_L grows with the window, so this theorem alone gives no cutoff-uniform estimate.
Improving the total-mass loss requires cancellation-aware or spatially varying
transport; it cannot be obtained by silently deleting M_L. H need not be an
autocorrelation or positive definite. Neither property is used in (1); positivity
enters only through the original h in (2) and (3).

## Verification status

Paper proof above is complete. Both Lean leaves pass direct
`lake --old env lean <leaf> -o <leaf.olean>` checks without diagnostics. The
constructed-source endpoints are `SignedPrimePolar.pairing_correlationAverage_eq`,
`SignedPrimePolar.abs_pairing_sub_chebyshevWork_le`, and
`SignedPrimePolar.abs_pairing_sub_chebyshevWork_le_levy`.
`SignedPrimePolar.pairing_eq_literal` verifies the original atom weights and polar
density. Six endpoint axiom audits report only propext, Classical.choice and
Quot.sound. Printed main signatures have no extra analytic premise. Both leaves
are wired into the area umbrella, and generated indexes are refreshed.

Repository lint was run; its sole error is the unrelated concurrent module
`RHTower.FermiNymanDyadicFoldGeometry` missing from its own umbrella. No whole-tree
or umbrella build was run. Classical Stieltjes summation is reused infrastructure,
not a separate research contribution. This package counts once toward the target
of 100; the overall research goal remains active.
