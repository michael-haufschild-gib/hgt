# Canonical profinite constraint--orientation limit

- **ID:** `canonical-profinite-constraint-orientation-limit`
- **Stage:** 3-formalized
- **Type:** THEOREM / UNIVERSAL HT CONSTRAINT GEOMETRY
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The finite products of labelled simplicial constraint geometries and residue-sign
  cubes have a canonical profinite inverse limit.  Its combinatorial space is the product of all
  abstract simplicial complexes on `ℕ` with the Cantor sign cube, its distinguished positive
  section is the all-positive sign sequence, and the fixed universal prime-log source realizes the
  complete sign factor by a normally convergent family of signed Cauchy transforms.

## Goal

Replace the finite-only limitation in the universal constraint--orientation theorem by an exact
cofinal object.  The theorem contains two logically different assertions:

1. the finite combinatorial systems have a canonical inverse limit;
2. the fixed positive prime-log source realizes every point of the orientation limit analytically.

Infinite residue sign changes need not preserve the raw algebraic differential field by the finite
rational-gauge argument.  The completed statement is now exact: every infinite orientation lies
in the same compact-open completed rational Cauchy ring, and the stronger summable-residue law
makes this ring independent of the source gauge as well.

## Canonical finite system

For a finite vertex set `S ⊆ ℕ` and an independently chosen finite prime set `T`, let

```text
X_(S,T) = Simp(S) × {+1,-1}^T,
```

where `Simp(S)` is the finite set of downward-closed families of subsets of `S`.  Inclusion in
each coordinate gives restriction bonding maps.  These maps are canonical, surjective, and
functorial.

The inverse limit is canonically

```text
Simp(ℕ) × {+1,-1}^Primes.                         (1)
```

where `Simp(ℕ)` is the set of downward-closed families of finite subsets of `ℕ`.  The formal
inverse-limit statement is an explicit equivalence: coherent restriction data over all pairs
`(S,T)` reconstruct uniquely as one element of `(1)`, and restriction followed by reconstruction
is the identity in both directions.  With the product topology, `Simp(ℕ)` is the closed subspace of
`{0,1}^{Fin(ℕ)}` cut out by downward closure and the second factor is the Cantor cube.  The
all-positive finite vertices form a compatible section whose limit is `(+1,+1,...)`.

## Analytic orientation realization

Let `λ_p = log p` and let `w_p > 0` be the actual weights of the fixed universal prime-log
source.  For a sign function `ε : Primes → {+1,-1}`, define

```text
g_ε(z) = Σ_p ε(p) w_p / (λ_p-z).                    (2)
```

The dyadic factor in `w_p` and boundedness of the fixed gauge make `Σ_p w_p` finite.  Hence
`(2)` converges normally on compact subsets away from the prime-log divisor and its finite
restrictions converge to it independently of the chosen cofinal exhaustion.

The signed Cauchy mass at `λ_p` has sign `ε(p)`; equivalently, the ordinary meromorphic residue is
`-ε(p)w_p`.  Every pole remains simple and nonzero.  Therefore

```text
g_ε is Herglotz on the upper half-plane  iff  ε(p)=+1 for every p.  (3)
```

The forward implication follows because any negative residue dominates the regular complement
near its pole.  Thus positivity selects the compatible all-positive section intrinsically.

## Completed algebra over the full fiber

Finite sign changes are rational base-field gauges and retain the fixed raw differential field.
For arbitrary infinite signs `ε,δ`, finite rational transitions from `g_ε` toward `g_δ`
converge locally uniformly to `g_δ`.  Therefore all infinite orientations generate the same
compact-open completed rational Cauchy ring once the common prime atoms and constants are included.
The stronger summable-residue theorem gives the same completion for all bounded phase gauges, not
only for different signs of one fixed source.  Raw differential-field equality and completed-ring
equality remain correctly distinguished.

## Gates

- [x] 0 → 1: canonical directed system and analytic candidate identified
- [x] 1 → 2: complete proof of the inverse-limit identification and analytic orientation law
- [x] 2 → 3: unconditional internal formalization of the proved layers
- [x] finite-stage compatibility: the infinite carrier restricts exactly to every finite chamber
- [x] pole law: every prime-log pole is simple and has its prescribed nonzero signed mass
- [x] Herglotz law: the all-positive sequence is the unique positive point
- [x] raw infinite differential-field claim excluded from the theorem
- [x] exact compact-open completed-ring invariance proved over the full orientation fiber
- [x] completed-ring invariance strengthened to the full source--orientation product
- [x] novelty audit: canonical completion and analytic bridge, not a new HT-independence mechanism
- [x] publication theorem revised to distinguish inverse-limit existence from strong field invariance

## Approach

The proof reconstructs a global face predicate by reading a finite face `J` at its own stage and
uses coherence to prove downward closure and uniqueness.  A global Boolean coordinate is read at
the singleton stage.  These constructions are inverse to restriction.

For the analytic factor, absolute summability of the dyadic prime weights gives normal convergence
off the locally finite prime-log divisor.  Deleting one atom gives a holomorphic regular part at
its pole.  The exact polar splitting identifies the nonzero simple residue.  If a Cauchy mass is
negative, its term contributes `-w_p/y` at `λ_p+iy` and dominates the regular part as `y → 0+`.
Thus Herglotz positivity is equivalent to the all-positive Boolean sequence.

## Formal theorem surface

- `canonicalConstraintOrientationLimitEquiv`
- `universalPrimeOrientationLimit_coe_finset`
- `hasSimplePoleAt_universalPrimeOrientationLimit`
- `universalPrimeOrientationLimit_nonneg_iff_allPositive`
- `canonicalConstraintOrientationLimit_primeCarrier_nonneg_iff_allPositive`
- `summablePrimeCauchyCompletedRing_eq`
- `UniversalFacetSource.completedOrientationRing_eq`

The implementations are in `CanonicalConstraintOrientationLimit.lean` and
`UniversalPrimeOrientationLimit.lean`.

## Log

- 2026-07-13 — finite inverse-limit existence separated from analytic realization and same-field
  invariance; infinite rational-gauge failure isolated as the open core.
- 2026-07-13 — proved the exact coherent-thread equivalence, arbitrary-sign normal convergence,
  exact finite-chamber restriction, signed simple-pole law, and unique infinite Herglotz point;
  moved the theorem to the formalized stage.
- 2026-07-13 — replaced the manuscript's auxiliary finite-only orientation with intrinsic
  prime-residue chambers, added the canonical profinite completion theorem and proof, and stated
  the infinite same-field boundary explicitly.
- 2026-07-13 — resolved the analytic boundary at the correct completed level: all summable residue
  carriers, hence all phase sources and infinite orientations, have one compact-open completed
  rational Cauchy ring.
