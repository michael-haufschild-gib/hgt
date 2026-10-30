# A physical Schläfli derivative reserve

For the literal Schläfli function $f(x)=K_{i\tau}(x)$, define
$$W_\tau(x)=e^{-x}\{f'(x)+(1+x^{-1})f(x)\}.$$
Its argument system gives the exact identity
$$W_\tau'(x)=-e^{-x}\left\{x^{-1}+(1+\tau^2)x^{-2}\right\}f(x).$$
The source has $W_\tau(x)\to0$ as $x\to\infty$.
On $x\ge|\tau|$, positivity of $f$ makes $W_\tau$ nonincreasing,
hence $W_\tau\ge0$ and
$$f'(x)\ge-(1+x^{-1})f(x).$$

For $q\ge3$ and $|\tau|\le2q$, this pays the signed source combination
$$ (4q^2+9)K_{i\tau}(2q)+12q K'_{i\tau}(2q)
\ge(4q^2-12q+3)K_{i\tau}(2q)>0.$$
Positivity of a finite frequency band alone does not bound the signed
polynomial-weighted Fourier tail or prove an all-rank Hankel cone.

Lean: `CompletedArithmeticForms/BesselBarrierPayment.lean`:
`hasDerivAt_besselBarrierFlux`, `tendsto_besselBarrierFlux_zero`,
`besselArgDeriv_re_lower_on_band`, and `besselSignedRadialCombination_pos`.
The capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
