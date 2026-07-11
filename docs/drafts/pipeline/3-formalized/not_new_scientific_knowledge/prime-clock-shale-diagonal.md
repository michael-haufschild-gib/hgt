# The prime-clock Shale diagonal

- **ID:** `prime-clock-shale-diagonal`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** relational-time and infinite-phase-space reframe, separate from the live RHTower routes in
  `docs/reports/rhtower_status_1107.md`
- **Statement:** In the infinite one-particle prime phase space, the formal prime amplitudes at `s`
  and at its FE--Schwarz reflection `1-conj(s)` differ by an `l2` vector if and only if
  `Re(s)=1/2`. Hence the critical line is exactly the unitary-equivalence seam of the two reflected
  coherent prime sectors, and RH is equivalent to every Xi zero lying in that seam.

## Goal

Replace the single-Hamiltonian question by a timeless compatibility question between infinitely many
prime clocks. The real part of `s` labels a representation sector; the imaginary part supplies a
common phase evolution inside that sector. Functional-equation reflection compares two sectors. The
theorem determines exactly where that comparison is unitarily implementable.

## Gates

- [x] 0 → 1 in-progress: prime phase space, reflected amplitudes, square-energy criterion, and
  finite-truncation attack stated.
- [x] 1 → 2 fully-proven: complete proof below.
- [x] 2 → 3 formalized: `PrimeClockShaleDiagonal.lean`; focused build and axiom audit pass.
- [ ] 3 → 4 publication-ready: fails the parent-theory and significance gates for new scientific
  knowledge; it is a source-built selector, not a zero-localization mechanism.

## Infinite prime superspace

Let `P` be the set of rational primes and let the one-particle space be

```text
h_P = l2(P).
```

For `s=sigma+it`, define the formal prime displacement

```text
alpha_s(p) = p^(-s) = p^(-sigma) exp(-it log p).
```

The FE--Schwarz line reflection is

```text
tau(s) = 1-conj(s) = 1-sigma+it.
```

The imaginary part is the same on both sides. Therefore

```text
|alpha_s(p)-alpha_tau(s)(p)|^2
  = (p^(-sigma)-p^(-(1-sigma)))^2.
```

The total reflected displacement energy is

```text
E(sigma) = sum_p (p^(-sigma)-p^(-(1-sigma)))^2.
```

In the coherent-sector interpretation of the Weyl/CCR algebra, two displaced representations are
unitarily equivalent precisely when their displacement difference belongs to the one-particle
Hilbert space. This is the coherent-shift face of the infinite-dimensional implementability
criterion originating with [Shale](https://doi.org/10.1090/S0002-9947-1962-0137504-6).

## Shale diagonal theorem `[PROVED HERE]`

For every real `sigma`,

```text
E(sigma) < infinity  iff  sigma = 1/2.
```

### Proof

At `sigma=1/2` the two amplitude families agree term by term, so `E(1/2)=0`.

Assume `sigma<1/2` and put `delta=1-2sigma>0`. For every prime `p`,

```text
p^(-sigma)-p^(-(1-sigma))
  = p^(-sigma) (1-p^(-delta)).
```

Since `p>=2`,

```text
1-p^(-delta) >= 1-2^(-delta) =: c_delta > 0.
```

Also `2sigma<1`, so `p^(-2sigma)>=p^(-1)`. Hence

```text
(p^(-sigma)-p^(-(1-sigma)))^2 >= c_delta^2 / p.
```

Euler's divergence of the prime harmonic series gives `E(sigma)=infinity`. The case
`sigma>1/2` follows by the exact symmetry `E(1-sigma)=E(sigma)`. ∎

## Relational-time reading

`[BRIDGE]` For fixed `sigma`, changing `t` multiplies every prime coordinate by the clock phase
`exp(-it log p)`. This is a unitary diagonal action and does not change `E(sigma)`. Thus the theorem
does not use time evolution to select the line. It says instead:

> The two functional-equation clock perspectives belong to the same infinite coherent sector only
> at the self-dual real part `sigma=1/2`.

This is compatible with perspective-neutral constrained quantum systems, where a physical state is
defined before a clock perspective is chosen and different internal-frame descriptions must be
related through the common constrained structure; see, for example,
[Vanrietvelde--Hoehn--Giacomini--Castro-Ruiz](https://arxiv.org/abs/1809.00556).

The infinite number of primes is essential. For every finite prime set the reflected difference is
automatically square-summable for every `sigma`; no finite clock inventory sees the Shale diagonal.

## RH equivalence `[PROVED IN LEAN]`

The Lean theorem `riemannHypothesis_iff_xiZero_primeClockShale` proves

```text
RiemannHypothesis
  iff
for every rho, Xi(rho)=0 implies E(Re(rho))<infinity.
```

The forward direction uses functional-equation reflection to exclude both sides of the line. The
reverse direction combines the Shale diagonal theorem with the existing exact no-right-half-Xi-zero
form of RH.

This is a meaningful change of arena:

```text
zero location in the s-plane
  becomes
unitary equivalence of two infinite prime-clock sectors.
```

It is not a proof of RH. The equivalence does not show why a zero of the completed arithmetic
constraint must inhabit a unitarily implementable sector.

## Attack and status

- `[PROVED]` The selector is source-built from prime amplitudes and uses no zero divisor.
- `[PROVED]` The selector is genuinely infinite-dimensional; every finite-prime truncation is blind.
- `[PROVED]` The critical line is its exact, not asymptotic, equivalence locus.
- `[OPEN CORE]` Construct from the completed Euler--Gamma constraint a perspective-neutral physical
  state or rigging map whose zeros can occur only when the two reflected prime-clock sectors are
  unitarily equivalent. Scalar functional-equation equality alone does not give such an intertwiner.
- `[ATTACK]` FE--Schwarz-symmetric entire countermodels with off-line quartets show that symmetry alone
  cannot supply the missing sector-gluing theorem.
- `[BRIDGE]` After project terminology is erased, the proof is the Shale square-summability criterion
  plus Euler's divergent prime harmonic series. The exact zeta formulation was not found in the
  preliminary literature search, but the parent-theory derivation is direct. The result therefore
  fails the new-scientific-knowledge gate.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/PrimeClockShaleDiagonal.lean` proves:

- `primeClockReflectionEnergy_half`;
- `not_summable_primeClockReflectionEnergy_of_lt_half`;
- `primeClockReflectionEnergy_one_sub`;
- `not_summable_primeClockReflectionEnergy_of_half_lt`;
- `summable_primeClockReflectionEnergy_iff`;
- `riemannHypothesis_iff_xiZero_primeClockShale`.

The focused module build passes. Every theorem in the module has only the standard project axioms
`[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-07-11 — theorem proved on paper and in Lean; RH equivalence formalized; classified BRIDGE.
