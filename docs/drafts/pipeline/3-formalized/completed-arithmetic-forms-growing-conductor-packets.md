# Completed conductor packets at growing overlap

Let $A_{c,N}$ be the complete tilted-spline Weil matrix, $r_{m,N}$ its
normalized Ramanujan vector, and $E_m(c)$ its completed conductor energy.
For every fixed $m>0$, one constant and one horizon give
\[
\|A_{c,N}r_{m,N}-E_m(c)r_{m,N}\|^2
\le C_m\left[c^{10}(\log N/N)^2+c^6/\sqrt{\log N}\right].
\]
The joint domain is $c\ge1$, $c/N\le1/3$, $B=\lceil ec\rceil\le N$,
and $2(e+3)cB\le N$. The exact residual includes prime adjunction,
self remainder, polar center, separated cross remainder, two-pole remainder,
near Gamma/downward cancellation, near center, and upward shell realization.
Kernel replacement retains its stronger $(\log N/N)^2$ cost.

Write
\[
\kappa=\frac{2\,\mathrm{tiltedSplineTailConstant}}{\int\phi^2}>0.
\]
The literal Fourier spectrum has eighth-power decay. Its positive coprime-tail
series gives $E_m(c)\le[m/\varphi(m)]E_1(c/m)$ and hence, for $c\ge m>0$,
\[
\kappa c^{-7}\le E_m(c)\le D_m c^{-7}.
\]
Every fixed finite positive-conductor family therefore has uniformly bounded
energy ratios at sufficiently large overlap.

The complete relative residual obeys
\[
\frac{\|A_{c,N}r_{m,N}-E_m(c)r_{m,N}\|^2}{E_m(c)^2}
\le C'_m\left[c^{24}(\log N/N)^2+c^{20}/\sqrt{\log N}\right].
\]
Along $c_N=(\log N)^\alpha$, $0<\alpha<1/40$, every source-domain
inequality holds eventually, both displayed costs vanish, and
\[
c_N^7\|A_{c_N,N}r_{m,N}-E_m(c_N)r_{m,N}\|\to0,\qquad
\frac{\|A_{c_N,N}r_{m,N}-E_m(c_N)r_{m,N}\|}{E_m(c_N)}\to0.
\]

The actual Gram discrepancy satisfies, for $N\ge2$,
\[
|\langle r_{m,N},r_{\ell,N}\rangle-\delta_{m\ell}|
\le\frac{2m\ell+1}{\log N}.
\]
Together with the complete quadratic energy ceiling, its scaled mixed-entry
cost is $O_{m,\ell}(c^9/\log N)$. Thus
\[
c_N^7\bigl(\langle A_{c_N,N}r_{m,N},r_{\ell,N}\rangle
-\delta_{m\ell}E_m(c_N)\bigr)\to0.
\]
For every fixed injective family $m:\mathrm{Fin}(d)\to\mathbb N_{>0}$,
one horizon makes the literal complete energy of
$\sum_i b_i r_{m_i,N}$ strictly positive for every nonzero real coefficient
vector $b$. The varying diagonal has common scaled floor $\kappa$; the
finite entry error pays all mixed coefficients simultaneously.

Lean: `CompletedArithmeticForms/WeilPolynomialResidual.lean`,
`exists_tiltedWeil_polynomial_residual_bound`;
`ConductorOverlapDecay.lean`, `tiltedConductorEnergy_two_sided`,
`exists_finite_conductor_energy_ratio_bound`;
`WeilGrowingOverlap.lean`, `tendsto_tiltedWeil_relative_residual_norm`;
`WeilGrowingPackets.lean`, `eventually_tiltedWeil_growing_packet_pos`.

Full-horizon positivity at growing overlap remains open. For the same
profile, eventual complete nonnegativity at
$c_N=2(\log N)^\alpha$, $\alpha>1/4$, is the separate RH-equivalent endpoint.
