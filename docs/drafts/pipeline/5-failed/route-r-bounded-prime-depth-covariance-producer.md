# Route R bounded prime-depth covariance producer

- **ID:** route-r-bounded-prime-depth-covariance-producer
- **Stage:** 5-failed
- **Type:** TERMINUS / EXACT RH-EQUIVALENT CRITERION
- **Source:** user-directed Route R frontier · 2026-08-06 conjecturing loop
- **Statement:** A coefficient-faithful landing of the retained rational-adelic prime class on an isometric prime-depth orbit, with bounded physical polarization satisfying the explicit Route R covariance on that orbit, forces the Hodge-mate coefficient to vanish.

## Goal

This attack asked whether bounded physical polarization on an isometric retained prime-depth orbit
could replace the terminated first-wall reader lane.  Hostile completion proved the certificate is
inhabited exactly when the Hodge-mate coefficient already vanishes.  It is therefore a useful exact
classification and no-go, but not a source producer.

## Gates

- [x] 0 → 1  in-progress: well-posed candidate and hostile attacks recorded
- [x] hostile converse: trivial Stokes/identity/zero realization exists whenever `K = 0`
- [x] exact classification paper-proved: certificate existence iff `K = 0`; global existence iff RH
- [x] classification formalized unconditionally in Lean
- [x] moved to failed/terminus after positive survivor extraction
- [ ] 3 → 4  publication-ready: not claimed

## Falsified producer conjecture

Fix an ordinary prime `p` and Xi divisor point `rho`.  Put

`K = ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho`.

There exist a complex normed source completion `E`, a linear landing `L` from the genuine relative
first cohomology, a bounded Stokes readout `tau`, bounded complex-linear operators `H,U : E → E`,
such that:

1. `tau (L z)` is the existing source Stokes regulator of `z`;
2. `U` is isometric;
3. for `x = L(ccmRationalAdelicPrimeRelativeClass p)` and every `n ≥ 0`,

   `H(U(U^[n] x)) - U(H(U^[n] x)) = K • U(U^[n] x)`.

Only this orbitwise covariance is requested; no global commutator identity is needed.

## Dependency-closed consumer proof `[PROVED HERE]`

The Stokes period of the retained class is one.  Compatibility of `tau` with the source regulator
therefore gives `tau x = 1`, hence `x ≠ 0`.

Write `x_n = U^[n] x`.  Orbitwise covariance and induction give

`H x_n - U^[n](H x) = n K • x_n`.

Because `U` is isometric, `‖x_n‖ = ‖x‖` and `‖U^[n](H x)‖ = ‖H x‖`.  Boundedness of `H` yields

`n |K| ‖x‖ = ‖H x_n - U^[n](H x)‖ ≤ 2 ‖H‖ ‖x‖`.

Cancel `‖x‖ > 0`.  If `K ≠ 0`, choose a natural number
`n > 2 ‖H‖ / |K|`; then `n |K| > 2 ‖H‖`, contradiction.  Thus `K = 0`.

Existing Route R coefficient faithfulness gives `Re rho = 1/2`.  Producing one certificate for
every Xi divisor point therefore proves RH through the existing right-half-plane endpoint.

## Conjecture / attack log

- **C1 fixed-source Gamma reversal:** failed.  Genuine dagger changes the period orientation.
- **C2 rational Cartier orbit rigidity:** failed.  Available functor has gain one; physical
  naturality is the missing RH-strength statement.
- **C3 reciprocal Gamma tensor:** failed.  Its desired contraction is the fixed same-fibre identity.
- **C4 unique Stokes rank port:** failed.  The explicit Bockstein occupies that same port.
- **C5 reflected-Gaussian support escape:** failed.  Existing Green bound is target-relative and
  supplies no source capacity bound.
- **C6 unipotent shear recurrence:** failed as a new producer.  Existing invariant-line theorem is
  already equivalent to `K = 0`.
- **C7 degree-six cyclic compression:** failed.  Source trace is cyclic; physical first trace is the
  singular noncyclic marginal.
- **C8 bounded prime-depth covariance:** fails as a producer.  It uses the infinite prime-depth
  orbit excluded from finite-rank models and converts exact covariance into `K = 0`; however, the
  converse certificate is immediate from `K = 0`, so certificate existence contains exactly the
  desired conclusion.

## Exact converse and circularity classification `[PAPER-PROVED] [LEAN-PROVED]`

If `K = 0`, take carrier `E = ℂ`, source landing equal to the existing period-one Stokes
regulator, Stokes readout and prime-depth dilation equal to the identity, and physical polarization
equal to zero.  Stokes compatibility and isometry are tautological; orbit covariance reduces to
`0 = K • x`, hence holds.  Combined with bounded-covariance rigidity,

```text
Nonempty (CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho)
  ↔ ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0.
```

Pointwise globalization and the existing fixed-corona endpoint give

```text
CCMRationalAdelicPrimeXiGlobalBoundedCovarianceProducer p ↔ RiemannHypothesis.
```

Thus absence of `K = 0` as a syntactic structure field did not make the package non-circular.  The
orbit covariance law itself carries exactly that semantic load.

## Novelty / collision audit

Abstract bounded-commutator rigidity is classical (Wintner–Wielandt).  New content claimed here is
only the Route R reduction and its coefficient-faithful source certificate, not the abstract
operator theorem.  Internal search found no existing module coupling the retained period-one
rational-adelic class to an isometric prime-depth orbit and the explicit completed-Xi Hodge-mate
coefficient by this orbitwise covariance law.  Existing barrelled/cofinal producers instead require
a null orbit plus pointwise bounded readouts.

## Strongest positive survivor

The abstract orbitwise Wintner–Wielandt theorem remains useful: any independently constructed
bounded polarization and isometric dilation satisfying the explicit covariance would annihilate
the coefficient.  The exact converse now supplies a cheap hostile test for future constructions:
unless the operators and covariance are derived from stronger pre-divisor structure, the package is
only a representation of `K = 0`.

The surviving Route R burden remains the singular comparison already named in the frontier map:
derive the fixed physical Cartier/positive same-fibre identification from pre-divisor source data,
or derive a weaker cofinal comparison modulo `ℓ¹ + o(1/p)` whose annihilated source field retains
the leading physical first-wall coefficient.  Merely postulating bounded covariance is closed.

## Log

- 2026-08-06 — conjecture frozen after seven failed alternatives; dependency-closed consumer proof written.
- 2026-08-06 — consumer, coefficient-annihilation, and conditional RH endpoint formalized; target
  module built; axiom audit `[propext, Classical.choice, Quot.sound]`; formal lint green.  Actual
  source construction remains the named open core.
- 2026-08-07 — hostile converse constructed: Stokes regulator + identity dilation + zero
  polarization gives a certificate from `K = 0`.  Lean proves local certificate existence iff
  `K = 0` and global producer iff RH.  Candidate retired as exact criterion re-encoding.
