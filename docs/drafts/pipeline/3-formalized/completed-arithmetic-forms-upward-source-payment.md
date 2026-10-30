# Polynomial payment of the complete upward source

For a fixed positive conductor and the actual tilted spline, put
$B=\lceil ec\rceil$. The squared-norm estimate is
\[
\|U_{m,c,N}\|^2\le C_m\left[
c^{10}\left(\frac{\log N}{N}\right)^2+
\frac{c^6}{\sqrt{\log N}}\right].
\]
Here $U_{m,c,N}$ is the literal normalized upward prime residual, including
both offset signs and both horizon boundaries. The domain is $c\ge1$,
$c/N\le1$, $B\le N$, and $2(e+3)cB\le N$, above one conductor-dependent
horizon.

The exact small-width offset identity decomposes each row into logarithmic
kernel replacement, prime-cutoff replacement, and the symmetric pair of
affine-shell residuals. Their harmonic squared costs are respectively
\[
A_m c^4(B+1)^6(\log N/N)^2,\qquad
D_m(B+1)^6/\sqrt{\log N},\qquad
F_m c^6/\sqrt{\log N}.
\]
The strip inequality $B+1\le(e+2)c$ and the three-term square inequality
give the stated payment. Retaining the kernel's $N^{-2}$ factor prevents
its fourth overlap power from degrading the logarithmic shell rate.

Lean: `CompletedArithmeticForms/UpwardSourcePayment.lean`,
`exists_logarithmicUpward_error_sharp_horizon_bound`,
`exists_reciprocalUpward_shell_polynomial_bound`,
`exists_tiltedWeil_upward_polynomial_payment`.
