# Literal Euler half-density contraction no-go

- **ID:** ULF-EHC-001
- **Stage:** 2-fully-proven
- **Type:** FALSIFIED
- **Source:** `1-in-progress/universal-law-field/STATUS.md` · MUST-121
- **Statement:** On the additive log/Fourier half-density carrier, every finite literal Euler operator has norm `prod p in S, (1 + p^(-1/2))`; these norms diverge over cofinal prime sets, so literal Euler formation has no bounded, hence no contractive, operator completion there.

## Goal

Decide the literal form of the proposed mechanism before divisor specialization:
whether multiplicative Euler formation itself acts contractively on the additive
Fourier-self-dual half-density completion.

## Gates

- [x] 0 -> 1 in-progress: exact carrier and operator fixed; source-pure; no zero or divisor
- [x] 1 -> 2 fully-proven: complete paper proof below; `[PROVED HERE]`; no open dependency
- [ ] 2 -> 3 formalized: Lean theorem and targeted audit
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, and Lean certificate

## Exact setup

Let `H = L^2(R, dt)`. For `a in R`, let

`(tau_a f)(t) = f(t + a)`.

Under the unitary logarithmic half-density coordinate on even
`L^2(R, dx)`, normalized dilation by `p` becomes `tau_(log p)`. For a
finite set `S` of primes, the literal finite Euler operator is therefore

`E_S = prod_(p in S) (I - p^(-1/2) tau_(-log p))`.

Changing every translation sign leaves all norm statements unchanged.

## Theorem [PROVED HERE]

For every finite set `S` of primes,

`||E_S|| = prod_(p in S) (1 + p^(-1/2)).`

Consequently, along any increasing exhaustion of the primes,
`||E_S|| -> infinity`. Hence the literal finite Euler operators admit no
strongly or weakly convergent bounded-operator completion on the full
half-density carrier and are not contractions for any nonempty `S`.

## Proof

Apply the additive Fourier transform. Translation by `-log p` becomes
multiplication by `exp(-i xi log p)`, so `E_S` becomes multiplication by

`m_S(xi) = prod_(p in S) (1 - p^(-1/2) exp(-i xi log p)).`

The multiplication-operator norm is the essential supremum of `|m_S|`.
The triangle inequality gives

`|m_S(xi)| <= prod_(p in S) (1 + p^(-1/2)).`

The real numbers `{log p / (2 pi) : p in S}` are rationally independent:
an integral relation `sum k_p log p = 0` exponentiates to
`prod p^(k_p) = 1`, and unique prime factorization forces every `k_p = 0`.
Kronecker's theorem therefore makes the one-parameter phase orbit

`xi |-> (exp(-i xi log p))_(p in S)`

dense in the full torus. In particular, there are `xi_n` for which every
phase tends to `-1`. Thus `|m_S(xi_n)|` tends to the displayed upper
bound. Continuity of `m_S` makes the ordinary supremum equal its essential
supremum. This proves the exact norm formula.

For `0 <= x <= 1`, `log(1+x) >= x/2`. Hence

`log ||E_S|| >= (1/2) sum_(p in S) p^(-1/2)
              >= (1/2) sum_(p in S) p^(-1).`

Euler's divergence of the reciprocal-prime sum proves cofinal norm
divergence. Strong operator convergence would imply pointwise boundedness
and then uniform norm boundedness by Banach-Steinhaus, contradiction.
Weak operator convergence is also norm bounded by uniform boundedness,
so it is impossible as well. QED.

## Corpus weld

- `FieldOneFiniteStageThetaEulerSourceIdentification` identifies the exact
  finite Euler action on the dense even-Schwartz theta source.
- `EvenL2LogUnitary.logEvenUnitary_evenDilation` turns normalized dilation
  into additive log translation.
- `HardyTitchmarshSourceTransport.evenPrimeLocalFactor` is exactly
  `I - p^(-1/2) U_p^*`.
- `DirectedLiteralSourceFormationRecoveryProperness` proves that joint
  formation/recovery moderation, not formation alone, is exactly the
  unitary half-density axis.
- `ArithmeticFormationCompletionBoundaryFusion` proves that absence of a
  completion-born arithmetic boundary is equivalent to RH; it does not
  prove that absence automatically.

## No-go closure

- **Exact killing theorem/mechanism:** Simultaneous prime phases can approach
  the maximally expansive phase. Exact finite-stage norms exceed one and
  diverge cofinally.
- **Strongest positive survivor:** The critical axis is still exactly the
  locus of bilateral formation/recovery properness. Therefore admissibility
  can only be a relative graph/form law coupling the two orientations (and
  the archimedean subtraction), not contractivity of the raw Euler product.
- **New insight:** The infinite Euler object must be born through relative
  completion or renormalized boundary cancellation. Scalar normalization of
  each `E_S` by its norm makes contraction automatic at every finite stage
  and therefore carries no horizontal selection information.
- **Status:** Internal corpus audit complete; paper proof dependency-closed;
  Lean formalization pending.

## Log

- 2026-09-02 — literal contractivity formulation falsified; exact norm law proved on paper
