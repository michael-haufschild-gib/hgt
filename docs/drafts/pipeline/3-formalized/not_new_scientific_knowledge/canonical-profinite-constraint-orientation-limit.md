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

It does not assert that the complete infinite orientation family preserves the same embedded
differential field.  An infinite residue sign change is not a rational gauge, so finite-chamber
field invariance cannot be passed to the limit.

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

## Boundary of the theorem

Finite sign changes are rational base-field gauges and retain the fixed differential field.
Infinite sign changes give a
normally convergent meromorphic correction with infinitely many poles and need not lie in
`ℂ(z)`.  Consequently the canonical analytic inverse limit exists, but equality of the embedded
differential fields at all its points is a separate conjecture requiring a sign-uniform
pole-rigidity theorem.

## Gates

- [x] 0 → 1: canonical directed system and analytic candidate identified
- [x] 1 → 2: complete proof of the inverse-limit identification and analytic orientation law
- [x] 2 → 3: unconditional internal formalization of the proved layers
- [x] finite-stage compatibility: the infinite carrier restricts exactly to every finite chamber
- [x] pole law: every prime-log pole is simple and has its prescribed nonzero signed mass
- [x] Herglotz law: the all-positive sequence is the unique positive point
- [x] strong product claim excluded from the theorem
- [x] novelty audit: canonical completion and analytic bridge, not a new HT-independence mechanism
- [ ] publication theorem revised to distinguish inverse-limit existence from strong field invariance

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

The implementations are in `CanonicalConstraintOrientationLimit.lean` and
`UniversalPrimeOrientationLimit.lean`.

## Log

- 2026-07-13 — finite inverse-limit existence separated from analytic realization and same-field
  invariance; infinite rational-gauge failure isolated as the open core.
- 2026-07-13 — proved the exact coherent-thread equivalence, arbitrary-sign normal convergence,
  exact finite-chamber restriction, signed simple-pole law, and unique infinite Herglotz point;
  moved the theorem to the formalized stage.
