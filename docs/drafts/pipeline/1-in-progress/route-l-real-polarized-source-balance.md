# Route L: real polarized source balance

- **ID:** L-C34
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; actual source normalization and radial balance
- **Depends on:** [C33](../3-formalized/route-l-burnol-reciprocal-window-incidence.md)
- **RH status:** unproved

The proof chain is complete original source → cyclic/fixed physical reader
agreement → original conormal vanishing → RH. C33 identifies the physical
incidence with the radial difference of two actual Fourier-window jet
quotients. The remaining step is a source-derived zero of that difference.

## Conjecture and actual normalization test

Test whether Fourier orthogonality supplies the real polarized pairing
whose scalar value is the difference of squared physical amplitudes.
The original and Fourier partner have equal Hilbert norms, but their
leading jets `J_L` and `K_L` are different normalization factors. Before
using orthogonality after normalization, determine their exact relative
modulus from the literal completed source formulas.

Writing `rho=sigma+i*tau`, C33 gives the same nonzero factor
`G(rho) zeta^(m)(rho)` in both jets. The remaining endpoint gauge is
`F_L(z)=(exp(L*z)-1)/z`, evaluated at `rho` and `1-rho`.
Its squared modulus is

`2 exp(L*sigma) (cosh(L*sigma)-cos(L*tau))/(sigma^2+tau^2)`.

Candidate positive estimate: for fixed real `b`,
`Q(a,b)=(cosh(a)-cos(b))/(a^2+b^2)` is strictly increasing for `a>0`.
Indeed its derivative numerator is bounded below by

`a^2 sinh(a)-2a(cosh(a)-1) + b^2(sinh(a)-a)`.

The bound uses `cos(b) >= 1-b^2/2`. The first summand is positive for
`a>0`: twice differentiating `a*sinh(a)-2(cosh(a)-1)` gives
`a*sinh(a)>0`, with both initial values zero. The second is nonnegative.
This suggests a strict quantitative normalizer bias in the direction
of the horizontal spectral displacement, rather than norm preservation.

Prove the endpoint estimate, then apply it to the actual completed jets
and source normalization. A scalar polarization identity alone would
only restate the physical defect. No source-metric preservation, common
normalization, radial equality or reflected fixedness is assumed.
