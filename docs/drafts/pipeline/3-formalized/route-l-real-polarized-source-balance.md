# Route L: actual normalized-source radial bias

- **ID:** L-C34
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; actual source normalization, strict radial bias and exact polarization criterion
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

The positive estimate is now proved: for fixed real `b`,
`Q(a,b)=(cosh(a)-cos(b))/(a^2+b^2)` is strictly increasing for `a>0`.
Indeed its derivative numerator is bounded below by

`a^2 sinh(a)-2a(cosh(a)-1) + b^2(sinh(a)-a)`.

The bound uses `cos(b) >= 1-b^2/2`. The first summand is positive for
`a>0`: multiply `sinh(a/2)<(a/2)*cosh(a/2)` by `sinh(a/2)>0`
and use the double-angle identities to obtain
`2(cosh(a)-1)<a*sinh(a)`. The second summand is nonnegative.
This proves strict quantitative normalizer bias in the direction
of horizontal spectral displacement.

The endpoint estimate applies to the actual completed jets
and source normalization. A scalar polarization identity alone would
only restate the physical defect. No source-metric preservation, common
normalization, radial equality or reflected fixedness is assumed.

## Consequence for the literal normalized sources

The strict endpoint estimate and its actual-source application are closed in Lean. For
`1/2 < sigma < 1`, it gives the stronger quantitative statement

`exp(L*(2*sigma-1)) |K_L|^2 < |J_L|^2`.

Set `X_L=J_L^-1 f_L` and `Y_L=K_L^-1 F(f_L)` in the actual even
Hilbert carrier. Both denominators and `f_L` are nonzero. Fourier
transport gives the exact weighted relation `J_L F(X_L)=K_L Y_L`.
It does not remove the weights. Unitarity gives

`||X_L||=||f_L||/|J_L|`, `||Y_L||=||f_L||/|K_L|`.

Consequently the strict source-energy bound is

`exp(L*(2*sigma-1)) ||X_L||^2 < ||Y_L||^2`.

Norm equality of these actual normalized sources is exactly critical-line
placement. The real polarized pairing of their sum and difference is
zero exactly in that case. Before normalization, the analogous real
pairing of `f_L+F(f_L)` and `f_L-F(f_L)` is zero unconditionally.
Both statements hold with the same actual window and Fourier operator.
The normalized pairing is the real part of the complex Hilbert inner
product. No orthogonality after normalization is assumed or proved
unconditionally. The theorem does not assert existence of an off-line
zero or refute the global RH-equivalent balance statement.

The normalization test therefore fails to derive the required balance
from Fourier unitarity. Its positive survivor is the exact weighted
transport, the quantitative strict energy bound, and the classification
of the proposed pairing's zero. The next attack must derive compensation
from the complete source while preserving these weights and its first
nonzero derivative at the original divisor.

## Search and external methods

Two completed deep/method searches returned 20 candidates and 20 source
arguments each; all statements and returned method excerpts were inspected.
The real-pairing search was partial at generation 824183, semantic
coverage 2179457/2333890. Its proposed ingredient set combines invariance
under a common scalar with Fourier integral duality. The literal jets
have different factors, and the duality theorem requires ordinary
integrability, not just the established L2 source admission. The circle
Fourier orthogonality hit likewise does not identify the conormal reader.
The endpoint search was partial at generation 824193, semantic coverage
2177721/2332223, with no proposed ingredients or proof ideas. Direct
corpus inspection supplied the strict `sinh(x)<x*cosh(x)` inequality
and the global cosine quadratic bound used in the proof.

Broad recent arXiv queries used polarization, convexity and hyperbolic.
The [CMB systematics](https://arxiv.org/abs/2609.00841) and
[quantum-network stabilization](https://arxiv.org/abs/2609.02841)
abstracts concern calibration and coupled experimental effects; no
mathematical source-balance result was adopted.
[Convexity from order](https://arxiv.org/abs/2609.05775), Theorem 4.5
and its proof, characterizes separating affine flats using oriented
maps and homogenized cones. Applying it would require the actual source
cones and their separating flat; it does not supply radial balance.
The [degenerate hyperbolic boundary paper](https://arxiv.org/abs/2608.17767)
derives a conormal trace estimate by cutoff integration by parts,
retaining source and initial energy on the right side (equations
2.26–2.28 and the displayed combined bound were inspected). No
identification of its PDE domain with the Burnol source, or zero of
that retained energy, has been established. No external theorem is
used as an unproved Lean input.

## Formal audit

`GaloisForLFunctions.RHTower.BurnolCoPoissonNormalizedSourceRadialBias`
contains 19 theorems and four definitions, with the exact bodies checked
in `/tmp/route_l_window_modulus_c34.lean`. The complete scratch check
passed with no diagnostics. Duplicate checking found 23 declarations
and zero collisions. The module is wired into `RHTower`.

The final targeted `lake build` passed, compiling only the new leaf
(27 seconds; dependencies cached). All 19 theorem names were audited
exactly once using `/tmp/route_l_normalized_source_c34_axioms.lean`;
each depends only on `propext`, `Classical.choice` and `Quot.sound`.
The formal index was regenerated and the global formal lint gate passed
(existing repository size warnings only). No added axioms, proof placeholders,
numerical experiments, full builds or umbrella builds were used.
