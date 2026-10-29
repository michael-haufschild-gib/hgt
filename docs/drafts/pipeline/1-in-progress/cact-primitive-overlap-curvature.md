# Primitive arithmetic curvature of the overlap symbol

## Question

Does the candidate arithmetic spectrum beyond touching have a positive representation at every fixed overlap ratio, including every conductor?

## Objects under investigation

For the unit indicator profile, the proposed ground energy is

\[
E_1(c)=1-\log(2\pi c)+c
-2\sum_{1\le h<c}\left(\log(c/h)-1+h/c\right).
\]

On `K<c<K+1`, its derivative is `-(c-K)(K+1-c)/c²`. At integer `K`, its value is twice the Stirling remainder. The proposed integral representation is therefore

\[
E_1(c)=\int_c^\infty \frac{\{t\}(1-\{t\})}{t^2}\,dt.
\]

The actual affine unit law suggests the correction

\[
\beta_m(c)=\frac2{\varphi(m)}\sum_{1\le h<c}
c_m(h)\left(\log(c/h)-1+h/c\right).
\]

The existing excitation is `log(m)+tameDifferent(m)`. Möbius inversion of the Ramanujan coefficients, together with the corresponding logarithmic totient identity, should give

\[
E_m(c)=\frac1{\varphi(m)}\sum_{d\mid m}d\mu(m/d)E_1(c/d)
=\frac1{\varphi(m)}\int_c^\infty\frac{A_m(t)}{t^2}\,dt,
\]

where

\[
A_m(t)=\sum_{d\mid m}d^2\mu(m/d)\{t/d\}(1-\{t/d\}).
\]

## Positive mechanism to formalize

For `m>1` and integer `k`, finite torsion Parseval predicts

\[
A_m(k)=\sum_{\zeta\text{ primitive of order }m}
\left|\sum_{j=0}^{k-1}\zeta^j\right|^2
=k\varphi(m)+2\sum_{h=1}^{k-1}(k-h)c_m(h).
\]

For `0<=u<=1`, the quadratic coefficient in `A_m(k+u)` vanishes because `sum_(d|m) mu(m/d)=0`. Thus `A_m(k+u)` is the convex interpolation of two nonnegative finite arithmetic energies. Modulus one is the original nonnegative quadratic. This gives a finite proof mechanism for positivity, without requiring an infinite Fourier expansion.

The equivalent Fourier expression would be

\[
A_m(t)=\frac{m^2}{\pi^2}
\sum_{k\ge1,\ (k,m)=1}\frac{1-\cos(2\pi kt/m)}{k^2}.
\]

It explains primitive-frequency selection but is not needed if the finite proof succeeds.

## Status and obligations

`PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder.lean` is an unchecked draft of the finite root-energy calculation, Möbius inversion, nonnegativity, and strict positivity off conductor multiples. The draft also cancels the constant mode for nontrivial conductors and states the resulting signed divisor-sum positivity. The draft now also includes exact real-cell interpolation and its positivity consequences. The fractional-part identification and a global nonnegative bound are now drafted too; the integral identity and symbol matching remain open. Integer quantization gives a draft lower bound of one off conductor multiples. A sharper lower bound by the totient should follow from the integral cyclotomic norm and arithmetic–geometric mean; the surrounding corpus supplies the exact embedding and norm tools, but this stronger step is not yet formalized. Corpus searches211–224 inspected existing primitive, covariance, Fourier, and Ramanujan identities. No numerical experiments were used.

Even a proof of all displayed symbol identities would leave separate obligations: realize the symbol in the actual overlapping complete Weil operator; control smooth approximation; prove an exhaustive low-energy description with the required conductor and overlap uniformity. Positivity of selected arithmetic modes is not positivity of the full operator and does not imply RH.
