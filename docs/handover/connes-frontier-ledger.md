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
- The local parity--residual Euler factorization and the full affine-Euler **probability/Fisher
  scalar laws** are proved.  Corpus search found no Lean declaration of the claimed global
  Hilbert-space isometry `U f(d,m)=mu(d)f(dm^2)`, no affine joint cutoff projection on that carrier,
  and no conjugation theorem transporting the centered Fisher connection.  Those operator claims
  were previously overstated in this ledger and must not be treated as available.
- The canonical Xi-pointed charged graph is no longer missing.  Coprime inner factorization gives
  the closed isometric graph with domain `B_omega H2`.  Its orthogonal domain defect
  `K(B_omega)` is exactly the off-line divisor model space.  Full domain, not graph construction or
  graph closedness, is the RH-bearing property.
- The real Euler-response kernel
  `J(x,y)=(Q(x)+Q(y))/(x+y)` is unconditionally positive on every one- and two-node packet.
  This is already proved on paper and promoted through the full Xi divisor in Lean.  A transverse
  single-zero orbit first becomes negative on exactly three distinct nodes; for the full Xi sum,
  cross-orbit masking is the remaining exterior-cubic obstruction.
- The normalized all-valuation transverse prime coefficient is already the Laplace sample of the
  Brownian interval vector `1_[0,a]`; its aperture Gram is `min(a,b)`.  Brownian/Monge positivity
  alone was tested and fails to orient the arithmetic response masks.

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
- one- or two-node Euler-response estimates: these packets are already strictly positive
  unconditionally; the first possible response obstruction is exterior degree three.
- Brownian/Monge/total-positivity arguments that do not transport the arithmetic Boolean mask.

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
of squared norm four.  More importantly, the native Fisher cutoff commutator already splits into
two adjoint non-diagonal boundary orientations.  The lower corner

```text
L_(sigma,u)=(1-Q_(sigma,u)) F_sigma Q_(sigma,u)
```

has exactly half the two-sided commutator energy.  Hence its unconditional critical limit obeys

```text
0 <= E_lower(u) <= 4(1-exp(-u)),
E_lower(u)/u -> 4,
integral_(0,infinity) E_lower(u) du = 4.
```

This is formalized in `MobiusCriticalFisherLowerBoundaryBudget.lean`.  Therefore budget eight is
not the live source target: one native corner already has the exact four-unit budget required by
`W_P`, globally over the complete physical cutoff ray.  The open theorem is its completed
one-sided incidence.

### Results that must not be mistaken for the missing source theorem

- `[REDISCOVERED]` Projection/reflection and Lüders identities already occur in
  `SoninProjectionQuantumWalk`, `SoninLudersPinching`, and the pointed/finite-rank Burnol Ward
  modules.
- `[PROVED, INSUFFICIENT]` The actual Xi phase is a contractive Hardy multiplier on every finite
  packet, and `V=1-phase` obeys target four-unit nonexpansiveness at every nonnegative aperture.
  This bounds multiplier **values**, not the aperture tangent `r_P`.
- `[PROVED, SCALAR-ENERGY COMPLETE; NOT A CRITICAL SOURCE VECTOR]` The physical affine Euler
  cutoff, its Fisher overlap and energy, its squarefree critical limit, and the exact one-corner
  conservation law `integral E_lower=4` are already formalized.  No further scalar calibration,
  cutoff integration, or factor-of-two repair is needed.  This does **not** produce a strong
  critical vector in one fixed source Hilbert space: `MobiusChannelCriticalMassEscape.lean`
  proves that the normalized critical Möbius channel is weakly null but not strongly null and
  that every fixed compact synthesis sends it to zero.
- `[CLASSICAL ANALYSIS; LEAN CONNECTOR ONLY]` The half-line Laplace feature
  `u ↦ exp(-wu)`, its Cauchy Gram `1/(w+conj z)`, represented-column Gram positivity, and the
  hard-cut/soft-semigroup divided-difference identity are classical Paley--Wiener/RKHS and
  double-operator-integral mechanisms.  Their formalization in
  `FisherOneCornerCoareaTransform.lean` is useful plumbing, not a literature-new theorem.
- `[CORPUS-NEW CONNECTOR; CLASSICAL LAYER-CAKE CORE]` The finite Fisher one-corner coarea formula
  refines the already-formalized Gini/layer-cake laws by retaining the Fisher pair amplitude.
  Do not advertise it as the missing CCM theorem.
- `[KILLED]` Aperture-only Schwarz--Pick differentiation: the common contractive aperture set of
  all right-half-plane Cayley cells is exactly the real ray `[0,∞)` and has empty complex
  interior (`C45`).
- `[KILLED]` One-sided Möbius--Gamma scalar graph: its exact source gain on the critical ray is
  `1/[2(σ-1)]` (`C42`).
- `[KILLED AT BUDGET 4]` Saturated bounded cofinal contractions and their moving-connection escape
  cannot create the Ward column from an orthogonal four-unit detail (`C43`--`C44`).
- `[PROVED, NOT A SOURCE PRODUCER]` Fable's edge-`L²` master kernel identity gives a route to
  another RH-complete detector.  It supplies no unconditional source bound for that detector.
- `[REDISCOVERED; REJECTED]` Differentiating the real-aperture Schur/Pick defect at aperture zero
  gives the classical Herglotz kernel
  `(r(w)+conj(r(v)))/(w+conj(v)) >= 0`.  It controls the sign of the infinitesimal Pick defect,
  not the size of `r`; the corpus already quantizes this positive edge mass.  It cannot imply the
  four-unit bound.
- `[REDISCOVERED; REJECTED]` Writing a charged quotient as `A/B` and differentiating
  `B O` into `B' O + B O'` is standard model-space/Julia operator theory.  A claimed
  “covariant cancellation” is admissible only if a pre-divisor Euler--Gamma identity proves that
  the resulting `K(B)` component vanishes.  If the cancellation assumes membership in `B H²`,
  full domain, or zero model-space pairing, it is RH itself.
- `[CORPUS DUPLICATE; REJECTED]` The absolute-Euler Cauchy--Laplace loss, its tail-shift
  representation, the factor `exp(-2a min(y,z))`, and the stationary de-Poissonized Weil form are
  already proved on paper in
  `critical-logderivative-euler-safe-cauchy-loss-law.md` and
  `critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`.  Recasting the fixed
  `W_P` problem as that observability inequality is not new knowledge and does not supply its
  missing sign.

## One live conjecture

`[CONJECTURE — ONE-CORNER GAMMA/SONIN INCIDENCE]`

The candidate global dyadic reindexing would turn the Euler cutoff into the affine joint
projection

```text
Q_T(d,m)=1_(log d+2 log m<T).
```

The actual source object is the single lower boundary corner

```text
L_T=(1-Q_T)F_sigma Q_T.
```

Gamma completion and strict-right anti-causal projection must act on `L_T` before any scalar
overlap quotient.  The conjectured identity says its cofinal image is the one-sided Xi boundary
operator, its finite Cauchy packet column is `r_P`, and its contraction defect is exactly

```text
4 G_P-r_P r_P*.
```

Equivalently, the completed one-corner image has no excess denominator-model-space component
beyond the packet column represented by the target boundary operator.

This must be an operator-valued affine-cutoff theorem.  Treating `L_T` through the scalar
Möbius--Gamma graph first is falsified by `C42`; using only the charged graph's already-proved
isometry silently restricts the domain to `B_omega H2` and assumes the desired conclusion.
Adding the adjoint corner first is unnecessary and loses the exact one-sided target.

## Exact open calculation

Local squarefree--Euler parity factorization, physical affine **scalar** cutoff law, squarefree
lower-corner rank-one decomposition, four-unit one-corner budget, scalar Möbius--Gamma current
weld, Julia transport, and canonical charged graph are constructed.  The global dyadic Hilbert
reindexing and its affine projection still require operator-level construction; after that, the
decisive uncomputed composition is the **operator** lower corner through Gamma/Sonin completion.
Test that transform on `L_T` before quotient evaluation:

1. work at finite `sigma` on a moving/cofinal carrier.  A fixed compact synthesis after the
   critical limit is impossible by `MobiusChannelCriticalMassEscape.lean`;
2. retain both rank-one summands inside the one lower corner; they are the tangent and moving-base
   connection terms and neither may be scalarized separately;
3. prove cancellation of the Euler-pole `1/(sigma-1)` terms inside their joint completed image;
4. identify the cofinal image with the one-sided anti-causal boundary operator on a source-defined
   graph core;
5. identify its finite packet column with the existing
   `continuedXiAntiCausalWardColumn`;
6. prove a uniform finite-`sigma` contraction before taking the cofinal limit.

Exact falsifier: if any model-space pairing is an unconstrained residue coordinate, if the sum
retains an uncancelled `1/(sigma-1)` gain, or if the calculation reduces to the existing Berezin
sign/full-domain assertion, then no new source law has been obtained and this formulation must be
retired.

The global equality `integral E_lower=4` strengthens the hostile test only after a legitimate
finite-`sigma` cofinal realization has been constructed.  If its limiting target column spends
four units, the uniformly contractive completion must be asymptotically isometric on the escaping
coarea field.  Thus no positive-measure cutoff component may be discarded by Gamma completion,
Sonin compression, Hardy projection, or graph closure.  A fixed compact factor is already excluded;
a nonzero causal, Gamma-polar, or denominator model-space remainder kills equality and therefore
kills this proposed incidence.

The first-clock cross-product Type-II Stokes proposal remains a separate fallback.  It is not the
current `W_P` attack.
