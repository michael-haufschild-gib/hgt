# The physical Wigner band and its divisor-trace sign

The literal radial profile is
$$P_c(v)=c^2(c^2+9-6c\cosh(2v))e^{-c\cosh(2v)},$$
and its Wigner transform uses phase $e^{2ibv}$.
Its exact Schläfli representation is
$$\widehat P_c(b)=c^2\{(c^2+9)K_{ib}(c)+6cK'_{ib}(c)\}.$$
The derivative reserve gives
$$\Re\widehat P_c(b)\ge c^2(c^2-6c+3)K_{ib}(c)>0,
\qquad c\ge6,\quad |b|\le c.$$

For an actual source product $k$ at center $u$, $c=2\pi k e^{2u}$.
Every $k\ge1$, $u\ge0$ lies in $c>6$.
The complete fixed-product packet equals
$$e^u\widehat P_c(b)\sum_{nm=k}e^{-ib(\log n-\log m)}.$$
In the band $|b|\le c$, its sign is therefore exactly the sign of the real
finite divisor trace. Diagonal atom pairs have trace one and positive band
density. Positivity of every arithmetic divisor trace is not asserted.

The full center-mixed sign requires control of the signed divisor trace,
the complementary frequency region, and the cofinal completed-shell domain.

Lean: `CompletedArithmeticForms/WignerSpectralBand.lean`:
`thetaCuspWignerRadialTransform_eq_bessel`,
`thetaCuspWignerRadialTransform_band_lower`,
`thetaCuspWignerProductFiber_physical_band_sign`, and
`thetaCuspSourcePairWigner_diagonal_re_pos`.
The capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
