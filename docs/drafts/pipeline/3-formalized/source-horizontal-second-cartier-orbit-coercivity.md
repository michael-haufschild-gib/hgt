# Second-Cartier nonlinear-shell orbit coercivity

- **ID:** P-SHC-ORBIT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `rh-current-frontier-map.md` · shared L/P second-Cartier open core
- **Statement:** The positive radial energy of the coefficient-faithful polarized second-Cartier ghost has a bounded prime-transfer orbit exactly at unit character modulus; every retained strict-right Xi fibre has explicit reciprocal geometric escape.

## Goal

Close the possibility that compactness is already implicit in the nonlinear Hermitian-incidence
shell.  Produce the exact coercive observable that detects its otherwise invisible hyperbolic
direction, retain the literal endpoint coefficient and prime character, and identify the precise
extra source theorem still needed for RH.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, exact leaf build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external novelty audit

## Definitions

Write a pointed Krein jet as `w=(u,(a,b))` and set

\[
  Q(w)=|u|^2+|a+b|^2.
\]

For `c != 0`, the polarized quadratic ghost is

\[
  H_c=(1,(c,c)).
\]

For `lambda != 0`, the proved prime transfer is

\[
  T_\lambda(u,s,d)=(\lambda u,\overline\lambda^{-1}s,d),
  \qquad s=a+b,\ d=a-b.
\]

Its `n`-th source orbit is represented without a choice of logarithm by
`T_{lambda^n} H_c`.

## Theorem 1 — exact orbit energy

For every natural `n`,

\[
 Q(T_{\lambda^n}H_c)
 =|\lambda|^{2n}+4|c|^2|\lambda|^{-2n}. \tag{1}
\]

### Proof

The anchor is `lambda^n`.  The source sum is
`conj(lambda^n)^(-1)(c+c)`.  Multiplicativity of complex norm and
`|conj z|=|z|` give (1). `[PROVED HERE]`

## Theorem 2 — sharp bounded-orbit classification

Assume `c != 0` and `lambda != 0`.  Then

\[
 (\exists C\in\mathbb R\;\forall n\in\mathbb N,
   Q(T_{\lambda^n}H_c)\le C)
 \quad\Longleftrightarrow\quad |\lambda|=1. \tag{2}
\]

### Proof

If `|lambda|=1`, both factors in (1) are one, so the energy is the constant
`1+4|c|^2`.

Conversely, suppose the orbit is bounded by `C`.

- If `|lambda|>1`, the first term `|lambda|^(2n)` is unbounded, contradicting
  (1) and the bound.
- If `0<|lambda|<1`, then `|lambda|^(-2)>1`; the second term is the positive
  constant `4|c|^2` times `(|lambda|^(-2))^n`, hence is unbounded, again a
  contradiction.

Since `lambda != 0`, trichotomy leaves `|lambda|=1`. `[PROVED HERE]`

## Theorem 3 — actual Xi-fibre reciprocal escape

Let `q` be a retained strict-right Xi copy, `p` a rational prime, and let the
actual shell scale be

\[
 c_q=8\,|C_{x,u,q,r}|^2 J_N,
\]

where the corpus proves `C_{x,u,q,r} != 0` from nonzero Julia coupling and
aperture, and `J_N>0` is the finite BV endpoint third jet.  Put

\[
 \lambda_{p,q}=p^{1/2-q}.
\]

Then `c_q != 0`, `lambda_{p,q} != 0`, and strict-rightness gives
`0<|lambda_{p,q}|<1`.  Therefore

\[
 Q(T_{\lambda_{p,q}^n}H_{c_q})\longrightarrow +\infty.
 \tag{3}
\]

In particular the orbit is unbounded and cannot have compact closure in the finite-dimensional
jet topology. `[PROVED HERE]`

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity`

Main declarations:

- `sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy`
- `sourceHorizontalSecondCartierLiteralEndpointRadialEnergy_eq_positiveOrbitEnergy`
- `sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff`
- `sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy`
- `sourceHorizontalActualXiSecondCartierKreinOrbitBounded_iff_endpointModerate`
- `not_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded`
- `tendsto_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbit_energy_atTop`
- `everySourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded_iff_rh`
- `sourceHorizontalActualXiSecondCartierKreinOrbitCoercivity_capstone`

The exact endpoint bridge identifies `Q` with squared opposite Hardy eigen-coordinates; on the
actual fibre its positive physical leg is literally the already-constructed Wold--BV endpoint
descent with the same conormal coefficient, clock, divisor copy, and prime label.  Bounded `Q` is
equivalent to moderation of that literal endpoint ghost.  The capstone conjoins actual-fibre
divergence, endpoint non-moderation, and the exact support-fibre sum
`xiSupportMultiplicity q.1.1 • ghost`, retaining every divisor copy.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound` for all main declarations.  Exact leaf build passes.

## Endpoint consequence and remaining producer

The coefficient-faithful identification with the literal endpoint is now proved, not postulated.
Its physical Hardy ghost is moderate exactly when `Q` is bounded, hence exactly when
`|lambda_{p,q}|=1`.  On a retained strict-right fibre both properties are formally false.

What remains is not another coefficient identification.  Existing conormal short is diagonal after
the complete four-orientation sum and records only `4|C|^2`; existing Hermitian incidence and Krein
form record the invariant product of reciprocal legs.  Neither supplies physical order.  The
surviving open core is now precise:

> Prove from completed source geometry that the already-identified literal endpoint ghost belongs
> to a compact-circle distribution/order space for every retained Xi divisor.

That theorem cannot be a redefinition: the present product-topology endpoint image is explicitly
non-moderate off line.  It must add a genuine source-natural physical-order law.  Any descent
depending only on incidence, determinant, Krein form, or the existing scalar short is provably
blind to (3).

## No-go closure

- **Exact killing mechanism:** nonlinear incidence plus Krein conservation leaves the complete
  reciprocal hyperbola; strict-right actual fibres have the explicit unbounded orbit (3).
- **Strongest positive survivor:** exact formula (1), classification (2), and actual-fibre
  coercive escape (3).
- **New insight:** compactness cannot be extracted from present shell axioms.  Viable producer is
  a bounded endpoint admission that controls positive radial energy, not another conserved
  indefinite scalar.
- **Status:** dependency-closed Lean proof; umbrella import wired.  RH remains open because no
  source-derived uniformly bounded literal endpoint admission controlling `Q` has been proved.

## Heavy-conjecture log

- Direct Krein conservation ⇒ compactness: **failed**; conserved level is a hyperbola.
- Positive paired-source budget ⇒ boundedness: **failed/circular**; corpus proves this comparison
  is RH-strength and false on every retained strict-right fibre.
- Integral Cartier monodromy ⇒ physical eigenvalue one: **failed/overstrong**; it would erase the
  legitimate critical-line phase, while a radial version requires the missing same-fibre star law.
- Compact theta divisor mode + Field-One half-density unitary ⇒ unit prime character:
  **failed at the action weld**; the corpus proves nontrivial normalized prime translation does not
  even remain in the fixed theta Hilbert fibre.  The finite-stage Field-One operator/source weld
  acts on the dense even-Schwartz carrier but does not turn the Xi evaluation functional into a
  nonzero eigenvector of that unitary.
- Cubic/second-Casimir trace equality: **reduced** to positive orbit energy; source nilpotence alone
  does not identify its square with the physical square.
- Positive orbit coercivity: **proved** by (1)--(3).

## Log

- 2026-08-18 — exact paper theorem proved; nonlinear shell compactness closed negatively with
  explicit positive coercivity survivor.
- 2026-08-18 — formalized exact energy, bounded-orbit classification, actual Xi-fibre divergence,
  RH firewall, and multiplicity-faithful capstone; exact leaf build and axiom audit pass.
- 2026-08-18 — formalized coefficient-faithful equality with literal two-sided Hardy endpoint
  energy and exact bounded-orbit iff endpoint-moderation bridge; off-line endpoint non-moderation
  is now part of capstone.
