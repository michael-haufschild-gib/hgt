# Reciprocal pairing of a local Euler weight misses the Lee--Yang chamber

- **ID:** `reciprocal-euler-pair-lee-yang-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NO-GO] [POSITIVE COUPLING TARGET] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/EulerReciprocalLeeYangNoGo.lean`
- **Consumer:** `../../1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`

## Theorem

The direct reciprocal symmetrization of a positive local Euler weight `a` produces

```text
(1+a z)(1+a^(-1)z)
  = 1 + (a+a^(-1))z + z^2.
```

Its normalized two-spin coefficient is

```text
c(a) = (a+a^(-1))/2.
```

Lean proves, for `a>0`,

```text
c(a) >= 1,
leeYangPairCircle(c(a)) <-> a=1.
```

Therefore every genuine contracting Euler weight `0<a<1` yields a reciprocal quadratic with an
off-circle pair.  For example `a=1/2` gives roots `-1/2` and `-2`.

## Positive successor

Reciprocal field pairing is exactly the wrong operation.  A finite Ising detour must place the
arithmetic data in ferromagnetic interaction weights

```text
c = exp(-2J) <= 1,
```

not in a local fugacity and its inverse.  The completed prime--Gamma source must therefore build
nonnegative couplings or a verified Lee--Yang single-site measure.  Functional-equation pairing of
Euler factors does not provide the finite circle theorem.

## Formal certificate

The module proves:

- `one_le_reciprocalEulerPairCoefficient`;
- `leeYangPairCircle_reciprocalEulerPair_iff`;
- `not_leeYangPairCircle_reciprocalEulerPair_of_lt_one`.

The exact module builds.  Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] reciprocal coefficient inequality proved
- [x] exact unit-circle vanishing locus classified
- [x] contracting Euler weights excluded
- [x] positive interaction-coupling target isolated
- [x] exact Lean build
- [x] accepted-axiom audit
