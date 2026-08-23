# Off-line zeros are the residue modes of the anti-causal Euler leakage

- **ID:** euler-leakage-residue-mode-expansion
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) -- scientifically non-new bridge
- **Source:** Suzuki's shifted xi Mellin operator; contour transport from the Euler half-plane
- **Statement:** `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` If the
  shifted xi quotient has finitely many uncancelled upper-half-plane poles, its complete
  wrong-support Euler leakage is the finite residue-mode operator of those poles. A simple off-line
  zero contributes one explicit decaying exponential mode with coefficient
  `-xi(rho-2 omega)/xi'(rho)`; a zero of multiplicity `m` contributes an
  `m`-dimensional exponential-polynomial block.

## Goal

Make the global Hardy leakage theorem explicit. The source object should not merely have the same
rank as the off-line divisor: its wrong-support kernel should display the off-line zeros as the
exact modes created when the Euler-contour is transported to the critical boundary.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement and contour route
- [x] 1 -> 2 fully-proven: complete finite-divisor paper proof, `[PROVED HERE]`
- [x] 2 -> 3 formalized: Lean theorem and axiom check
- [ ] 3 -> 4 publication-ready: infinite-divisor topology and external novelty review

### Lean status

- [x] Exact shifted-xi numerator and denominator at the spectral pole `z_rho`.
- [x] Chain-rule identity
  `d/dz xi(1/2+omega-iz)|_(z=z_rho) = -i xi'(rho)`.
- [x] Punctured-neighborhood residue limit and explicit contour coefficient `(7)` for every
  certified simple xi zero and positive shift, in
  `RHTower/ShiftedXiResidueMode.lean`.
- [x] Literal expansion of `sum_k a_k (t-s)^k`, exact bivariate coefficient matrix, and exact
  rank `m` for a multiplicity-`m` block whenever its top Laurent coefficient is nonzero, in
  `RHTower/ResidueModeMultiplicityBlock.lean`.
- [x] Linear independence of all `t^q exp(lambda_j t)` at pairwise distinct complex nodes, with
  arbitrary multiplicities, via the corpus confluent-Vandermonde determinant, in
  `RHTower/ExponentialPolynomialModeIndependence.lean`.
- [x] Arbitrary-order Laurent extraction: a finite principal part times `exp(-i s u)` has exactly
  the asserted exponential-polynomial residue; its leading Laurent coefficient gives nonzero top
  polynomial coefficient and exact block rank, in `RHTower/HigherPoleResidueMode.lean`.
- [x] All four new leaves built exactly and axiom-audited: only `propext`, `Classical.choice`,
  `Quot.sound`.
- [x] Strict interval Gram and compact positive-half-line synthesis realize every complete input
  moment vector, in `RHTower/ExponentialPolynomialIntervalMoments.lean`.
- [x] Exact dependent-block assembly on the actual negative output half-line: local nonzero top
  coefficients give a globally surjective coefficient map, restricted exponential-polynomial modes
  remain independent, and the operator rank is exactly `sum_j m_j`, in
  `RHTower/FiniteResidueModeOperatorRank.lean`.
- [x] Both assembly leaves built exactly and axiom-audited: only `propext`, `Classical.choice`,
  `Quot.sound`.
- [x] Finite-pole contour transport from the Euler half-plane to the boundary pairing: canonical
  removable normalization, selected horizontal sides, line integrability, and exact finite-pole
  residue transport in `RHTower/SuzukiFinitePoleContourTransport.lean`,
  `RHTower/SuzukiSelectedContourSides.lean`, `RHTower/SuzukiContourLineIntegrability.lean`, and
  `RHTower/SuzukiFinitePoleResidueTransport.lean`.
- [x] Fixed Euler-line inversion, causal high-line vanishing on the reflected wrong-support core,
  and the resulting residue-only normalized boundary formula in
  `RHTower/SuzukiFinitePoleLeakage.lean`.
- [x] Final leakage leaf built exactly; its four new declarations axiom-audited with only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Setup

Fix `omega>0` and put

```text
Theta_omega(z)=xi(1/2-omega-iz)/xi(1/2+omega-iz).
```

Let

```text
L_omega=P_- M_(Theta_omega)|H^2_+
```

be the anti-causal Hardy leakage. Under Suzuki's shifted Mellin transform, this is the compression

```text
1_(0,1) widehat(Theta_omega) 1_(1,infinity)
```

on `L^2((0,infinity),dx)`. Pass to logarithmic coordinates with the unitary

```text
(U f)(t)=exp(t/2) f(exp(t)).
```

Then the input half-line is `s>0` and the output half-line is `t<0`.

Assume that, after common-divisor cancellation, `Theta_omega` has finitely many poles `z_j` in the
upper half-plane, of orders `m_j`.

## Theorem

The logarithmic leakage `mathcal L_omega=U L_omega U^(-1)` has the kernel

```text
K_omega(t,s)
= i sum_j Res_(z=z_j) [Theta_omega(z) exp(-i z(t-s))],
                                                    t<0<s. (R)
```

Consequently

```text
rank(mathcal L_omega)=sum_j m_j.                           (1)
```

If all relevant zeros are simple, write `rho=beta+i gamma` and

```text
z_rho=-gamma+i(beta-1/2-omega).
```

Then `(R)` becomes

```text
K_omega(t,s)
=-sum_(Re rho>1/2+omega)
   xi(rho-2 omega)/xi'(rho)
   * exp((beta-1/2-omega+i gamma)(t-s)),
                                                    t<0<s. (2)
```

The sum is over the finite uncancelled right-hand off-line divisor, with conjugate terms included.

## Paper proof

`[PROVED HERE; NOVELTY UNVERIFIED]`

Suzuki's inverse shifted Mellin formula has the formal boundary kernel

```text
h_omega^*(r)
=1/(2 pi) integral_R Theta_omega(u) r^(-1/2-iu) du.        (3)
```

For a line `Im z=c>1/2+omega`, both shifted xi arguments lie in `Re s>1`. The quotient is given
there by the absolutely convergent Euler formula

```text
Theta_omega(z)
=pi^omega
 * s_minus(s_minus-1)/(s_plus(s_plus-1))
 * Gamma(s_minus/2)/Gamma(s_plus/2)
 * product_p (1-p^(-s_plus))/(1-p^(-s_minus)).             (4)
```

The inverse transform on this high line is the causal kernel constructed by Suzuki and is supported
in `r>=1`. Hence it makes no contribution when `r<1`.

Take smooth compactly supported input in `(1,infinity)` and test output in `(0,1)`. Their Mellin
transforms decay rapidly on horizontal lines, so the contour in `(3)` may be moved from the real
axis to `Im z=c` without an unproved pointwise inversion or horizontal-side term. The high-line
pairing vanishes by the support statement. Cauchy's theorem leaves exactly the crossed poles:

```text
h_omega^*(r)
=i sum_j Res_(z=z_j)
   [Theta_omega(z) r^(-1/2-iz)],             0<r<1.        (5)
```

Density then extends the identity from smooth test functions to the bounded leakage operator.

Put `x=exp(t)`, `y=exp(s)`, and `r=x/y`. In the multiplicative convolution, the factors introduced
by `U` cancel the `r^(-1/2)` in `(5)`:

```text
exp(t/2) r^(-1/2-iz) exp(-s/2)=exp(-iz(t-s)).               (6)
```

Substitution of `(6)` into `(5)` proves `(R)`.

At a pole of order `m`, its residue in `(R)` is an exponential in `t-s` multiplied by a polynomial
of degree `m-1`. Expanding that polynomial shows that the output lies in

```text
span{exp(-i z_j t), t exp(-i z_j t), ..., t^(m-1) exp(-i z_j t)}.
```

The coefficient matrix between the output basis `t^r exp(-i z_j t)` and the input moments
`integral s^q exp(i z_j s)g(s)ds` is anti-triangular: its anti-diagonal comes from the nonzero top
Laurent coefficient times `(t-s)^(m-1)`. Hence it has rank `m`, so all `m` modes occur.
Exponential-polynomials for distinct poles are linearly independent. Therefore the total rank is
`sum_j m_j`, proving `(1)`.

For a simple xi zero `rho`, the denominator derivative at `z_rho` is

```text
d/dz xi(1/2+omega-iz)|_(z=z_rho)=-i xi'(rho),
```

while the numerator is `xi(rho-2 omega)`. Thus

```text
i Res_(z=z_rho) Theta_omega(z)
=-xi(rho-2 omega)/xi'(rho).                               (7)
```

Since `-i z_rho=beta-1/2-omega+i gamma`, equations `(R)` and `(7)` give `(2)`.

## Constraint on entry

An off-line zero is therefore not merely a point in a divisor. It is a stable anti-causal mode of
the global Euler transfer operator. To enter the critical line, its decay exponent

```text
beta-1/2-omega
```

must reach the support boundary, and the corresponding residue mode must be removed from the
wrong-support operator. The unit-channel theorem in
`euler-hardy-leakage-offline-zero-rank.md` shows that, at an isolated transverse crossing, this mode
does not fade in operator norm: it peels off as a unit-strength channel.

This gives a no-jet source statement:

```text
entry = loss of an explicit residue mode under contour transport from the Euler half-plane.
```

## General self-dual completed Euler products

The contour proof applies verbatim to a centered self-dual completed Euler product of Cartwright
class. A simple zero `rho` contributes the same mode with coefficient equal to the numerator value
at the reflected shift divided by the derivative of the denominator completion. Known poles are
first removed by a symmetric pole-clearing factor.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The formula is correct but fails the parent-theory and anti-theatre
gates. After erasing xi notation, it is the standard residue/state-space realization of a rational
or finite-pole Hankel symbol: a pole of order `m` produces an exponential-polynomial block of rank
`m`. Suzuki already supplies the shifted symbol and the high-line causal transform. Contour
transport gives the displayed coefficient routinely. This is a useful explicit bridge, not new
scientific knowledge.

- Suzuki (2012), arXiv `1204.1827`, constructed the high-line causal kernel and proved the Boolean
  equivalence between innerness and absence of wrong-support output.
- Residue realizations of finite-rank Hankel operators and exponential-polynomial kernels are
  classical systems/operator theory.
- The searched Suzuki paper and its citation chain do not state `(R)`, the xi residue coefficient
  `(7)`, or the identification of each off-line zero with a wrong-support residue mode.
- The audit also covered Suzuki's later Selberg-class Hamiltonian paper (arXiv `1606.05726`),
  *Integral operators arising from the Riemann zeta function* (arXiv `1907.07302`), and *Chains of
  reproducing kernel Hilbert spaces generated by unimodular functions* (arXiv `2012.11121`); none
  contains the off-line residue-mode formula.
- Searches for the exact coefficient `xi(rho-2 omega)/xi'(rho)`, shifted-xi Hankel residues, and
  anti-causal zeta modes found no matching theorem.
- The surviving research residue is whether the *infinite* Euler source enforces a nonclassical
  constraint on these modes that cannot be read off from generic Hankel realization theory.

## Open core

1. Establish an unconditional weak-operator residue expansion for an infinite off-line divisor,
   with a canonical symmetric summation independent of the contour sequence.
2. Express the finite-mode Gram matrix directly as a limit of the Euler-region Pick matrices.
3. Find prime-side estimates forcing the residue-mode operator to vanish or remain norm-continuous
   at `omega=0`.

## Log

- 2026-07-10 -- finite-divisor residue-mode formula and explicit simple-zero coefficient proved;
  scientific novelty audit open.
- 2026-08-23 -- equation `(7)` and its underlying simple-pole residue limit formalized and audited;
  finite-pole contour transport and multiplicity/rank blocks remain before stage 3.
- 2026-08-23 -- completed finite-pole contour bridge: canonical removable normalization, selected
  side limits, boundary/high-line integrability, exact residue transport, fixed Euler-line Fourier
  inversion, causal high-line vanishing, and residue-only wrong-support formula. Combined with the
  already formalized arbitrary-multiplicity residue blocks and exact finite-mode operator rank, this
  closes the finite-divisor theorem. Exact leaf build and new-declaration axiom audit passed.
- 2026-08-23 -- multiplicity-block polynomial expansion and exact anti-triangular matrix rank
  formalized and audited; contour transport, higher-order residue extraction, and distinct-pole
  assembly remain.
- 2026-08-23 -- distinct-node exponential-polynomial independence formalized through the existing
  confluent polynomial-jet determinant; contour transport, Laurent extraction, and final operator
  rank assembly remain.
- 2026-08-23 -- arbitrary-order principal-part residue extraction and exact block-rank consequence
  formalized; finite contour transport and operator-level total-rank assembly remain.
- 2026-08-23 -- compact positive-half-line moment surjectivity, dependent residue-block assembly,
  negative-half-line mode independence, and exact total operator rank formalized and audited;
  finite-pole contour transport remains.
