# CCM terminal frontier ledger

**Updated:** 2026-07-24  
**Purpose:** compact persistent state; facts to reuse, routes not to repeat, and one live attack.

## Terminal theorem

For `L ≥ π/2`, set `ξ = 2π/L` and

```text
CΓ(L) = ccmFirstClockContinuousHalfWaveBudget L ξ
P+(L) = ccmFirstClockPrimeAlignedMass L ξ
P-(L) = ccmFirstClockPrimeCounterMass L ξ.
```

Corpus Lean proves unconditionally

```text
π B₁(L) = CΓ(L) + P+(L) - P-(L),
CΓ(L) > 0,
RH ↔ ∀ L ≥ π/2, P-(L) ≤ CΓ(L) + P+(L).
```

Success remains exactly one of:

1. prove this inequality for every physical `L`;
2. exhibit a concrete violating `L`;
3. exclude every CCM-admissible infinite source transport.

No criterion equivalent to RH counts as completion.

## What is known

- Gamma orientation and midpoint reflection are closed.
- Source-to-RH Landau/Volterra transfer is closed.
- Abel-to-half-weight diagonal reweighting moves outer/inner odds in the wrong direction.
- Dirichlet convolution, including operator-valued infinite convolution series, is scalar on each
  irreducible prime face.
- Aligned block subdivision gives one genuine non-diagonal infinite source carrier. Its finite
  block intersections recover the LCM ridge.
- Unrenormalized cofinal block intersections collapse to zero in `ℓ²`.
- Radial four-grade graph closure is maximally multivalued.
- Natural square-scale block Gram is indefinite; canonical source debt repairs it only to rank one.
- Cubic local Gram positivity stays inside one prime-power tower and does not transport first-clock
  half-waves.
- Half-density localization and Selberg regrouping have no cancellation inside one semiprime
  product fibre. Cancellation, if it exists, must couple distinct products.
- The squarefree-to-Euler map is no longer missing.  The dyadic Fock isometry
  `U f(d,m)=mu(d)f(dm^2)` sends the pointed squarefree state to the Euler state and transports the
  centered Fisher connection with vanishing cofinal defect.  Its sharp Euler cutoff becomes the
  non-product affine projection `log d+2 log m<T`.
- The canonical Xi-pointed charged graph is no longer missing.  Coprime inner factorization gives
  the closed isometric graph with domain `B_omega H2`.  Its orthogonal domain defect
  `K(B_omega)` is exactly the off-line divisor model space.  Full domain, not graph construction or
  graph closedness, is the RH-bearing property.

## Mechanisms tested in current attack

### Euler exterior-current sum

**Verdict:** rejected as terminal source lift.

The literal prime-power amplitude has squared mass
`Λ(n)n^(-1-u)`. Its unnormalized skew exterior current has energy of order `u⁻⁴` at the Euler
edge. Projective normalization restores finite Fisher energy but changes the observable to an
overlap logarithmic derivative; it no longer transports the continued Xi column. Direct
cellwise summation therefore cannot supply a fixed four- or eight-unit budget.

### Normal-cone/blown-up scalar graph

**Verdict:** rejected by existing exact source-gain theorem.

At the physical critical ray the graph gain remains `1/(2(σ-1))`. Analytic removal of a scalar
zero does not make the source map nonexpansive.

### Diagonal Euler chart

**Verdict:** rejected and Lean-formalized by parallel Fable work.

Every fixed off-line divisor point escapes in the diagonal pullback and contributes vanishing
anti-causal energy. Finite divisor packets become invisible. This chart cannot transfer a local
energy bound to the global divisor.

### Ward edge `L²` quantization

**Verdict:** useful alternative detector, not source producer.

Parallel Fable work has formalized the cross-kernel algebra for the proposed edge integral.
Completing its `8π` law would yield another RH-equivalent detector. It does not prove the
first-clock source inequality unless a source identity bounds that integral.

### Projective co-Poisson cancellation

**Verdict:** rejected as rediscovery of the existing quotient wall.

Multiplication of the normalized Möbius Mellin vector by zeta cancels the reciprocal Euler factor.
After quotienting, however, contractivity is exactly the previously isolated co-Poisson critical
boundary dissipation/Berezin-order sign.  The cancellation supplies no new source positivity.

### Polarized complex aperture

**Verdict:** rejected by a counterfeit off-line divisor.

For `Re a>0` and `Re u>=0`,

```text
f_u(a)=(a-u)/(a+conj(u)),
|a+conj(u)|^2-|a-u|^2=4 Re(a) Re(u).
```

Its packet Pick defect has the same positive rank-one-plus-Cauchy factorization as the real
aperture law.  But the proof works for every arbitrary strict-right fake divisor packet, including
packets violating the budget-eight Ward inequality.  It is analytic phase positivity with no
arithmetic source incidence.

### Critical prime-CAR parity

**Verdict:** rejected by the already-formalized critical superselection obstruction.

Replacing scalar Möbius parity by a CAR parity automorphism retains algebraic parity but does not
retain the pointed and antipodal squarefree product vectors in one uniformly comparable critical
Hilbert sector.  `CriticalPrimePoissonGCDMobiusVacuum.lean` proves their finite-aperture distortion
grows at least on the prime-harmonic `log log` scale, while `PrimeClockShaleDiagonal.lean` proves
that reflected infinite prime sectors meet only on the critical line.  A normal CAR incidence from
a zero to that common sector is therefore the same missing zero-to-sector descent already retired
in `heat-echo-superselection-descent-is-rh.md`.

## Do not repeat

- finite-rank, diagonal, scalar, same-prime, one-product, or radial-Fock positivity;
- another RH-equivalent criterion without an unconditional source sign;
- estimates of already-closed Gamma, Volterra, first-clock transfer, or orientation interfaces;
- an ordinary bounded contraction of the saturated four-unit detail;
- “Gamma chart is asymptotically isometric” as a global Xi-weld argument;
- product-fibre Selberg averaging: one ordinary semiprime fibre has only one real cosine mode.
- co-Poisson zeta cancellation without a proof of the quotient Berezin sign;
- a complex/polarized Cayley aperture law: arbitrary fake divisors satisfy it;
- prime CAR/CCR sector gluing without a source-derived normal intertwiner.

## Fixed `W_P` frontier

For every finite right-half-plane packet `P`, corpus defines

```text
W_P = [[G_P,r_P],[r_P*,4]],
W_P >= 0 for every P  <->  RH.
```

It also proves the closed budget-eight version

```text
8 G_P-r_P r_P* >= 0 for every P  <->  RH.
```

The doubled Möbius parity source has a father Gram tending to `G_P`, a transverse Fisher detail
of squared norm four, and the native cutoff commutator has two adjoint boundary orientations with
total critical Ward density eight.  This is the only live source budget.

### Results that must not be mistaken for the missing source theorem

- `[REDISCOVERED]` Projection/reflection and Lüders identities already occur in
  `SoninProjectionQuantumWalk`, `SoninLudersPinching`, and the pointed/finite-rank Burnol Ward
  modules.
- `[PROVED, INSUFFICIENT]` The actual Xi phase is a contractive Hardy multiplier on every finite
  packet, and `V=1-phase` obeys target four-unit nonexpansiveness at every nonnegative aperture.
  This bounds multiplier **values**, not the aperture tangent `r_P`.
- `[KILLED]` Aperture-only Schwarz--Pick differentiation: the common contractive aperture set of
  all right-half-plane Cayley cells is exactly the real ray `[0,∞)` and has empty complex
  interior (`C45`).
- `[KILLED]` One-sided Möbius--Gamma scalar graph: its exact source gain on the critical ray is
  `1/[2(σ-1)]` (`C42`).
- `[KILLED AT BUDGET 4]` Saturated bounded cofinal contractions and their moving-connection escape
  cannot create the Ward column from an orthogonal four-unit detail (`C43`--`C44`).
- `[PROVED, NOT A SOURCE PRODUCER]` Fable's edge-`L²` master kernel identity gives a route to
  another RH-complete detector.  It supplies no unconditional source bound for that detector.

## One live conjecture

`[CONJECTURE — AFFINE DYADIC FISHER-TO-GRAPH INCIDENCE]`

Under the proved dyadic Fock isometry, the Euler cutoff is the affine joint projection

```text
Q_T(d,m)=1_(log d+2 log m<T).
```

Gamma/Sonin completion must act jointly, before scalar quotient evaluation, on the two adjoint
boundary corners

```text
C_T^+=(1-Q_T)F_sigma Q_T,
C_T^-=Q_T F_sigma(1-Q_T).
```

The conjectured source identity says their cofinal image lies in the full domain of the canonical
Xi-pointed graph, has mixed packet column `r_P`, and has joint defect
`8 G_P-r_P r_P*`.  Equivalently, the completed image has no component in the denominator model
space `K(B_omega)`.

This must be an operator-valued, two-sided affine-cutoff theorem.  Treating either corner through
the scalar Möbius--Gamma graph first is falsified by `C42`; using only the graph's already-proved
isometry silently restricts the domain to `B_omega H2` and assumes the desired conclusion.

## Exact open calculation

The squarefree-to-Euler isometry and the canonical charged graph are both constructed.  The only
uncomputed composition is the affine cutoff boundary through Gamma/Sonin completion.  For the
centered Fisher connection, compute

```text
C_T=C_T^++C_T^-=[Q_T,F_sigma].
```

Test the completed transform on `C_T` **before** quotient evaluation:

1. compute both affine boundary faces `log d+2 log m=T` and retain their orientation;
2. prove cancellation of the critical scalar gain only after the two adjoint faces are added;
3. pair the result against the Cauchy derivative jets spanning `K(B_omega)` and prove every
   model-space component vanishes;
4. identify the surviving finite packet column with the existing
   `continuedXiAntiCausalWardColumn`;
5. prove the joint map is contractive in the native eight-unit commutator norm.

Exact falsifier: if any model-space pairing is an unconstrained residue coordinate, if the sum
retains an uncancelled `1/(sigma-1)` gain, or if the calculation reduces to the existing Berezin
sign/full-domain assertion, then no new source law has been obtained and this formulation must be
retired.

The first-clock cross-product Type-II Stokes proposal remains a separate fallback.  It is not the
current `W_P` attack.
