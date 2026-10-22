# Deninger big-Witt Frobenius multiplicative submass

- **Stage:** 5-failed
- **Date:** 2026-08-15
- **Route:** L
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerBigWittFrobeniusMultiplicativeSubmassNoGo.lean`
- **Status:** CONJECTURE REFUTED; EXACT RESIDUE HIERARCHY FORMALIZED

## Failed conjecture

After upgrading the division-free `F_2` operation to the canonical natural
big-Witt RingHom, use Witt multiplication of finite polarized sources to
create cross-pair interaction before norm extraction. The conjecture was that
some finite multiplicative level could cancel the linear physical residue and
produce the missing cofinal submass relation.

## Exact killing mechanism

For multiplicative level `m`, define the source by first taking the `m`th
Witt power of the finite polarized aggregate and then applying canonical
Frobenius two. RingHom multiplicativity and the first-ghost Calkin bridge give
the exact finite identity

```text
ghost_1(F_2(P_S(rho)^m))
  = (-2 * E_S^Calkin(rho))^m.
```

Thus multiplication does not generate alternating cross-pair terms. It takes
the ordinary power of the same positive Calkin energy.

After normalization by the matching reciprocal mass power, Lean proves

```text
ghostGround_m(S) / primeReciprocalMass(S)^m
  -> (-4 * orbitwisePrimeSeamWeightedNormSq(rho))^m.
```

At every off-critical open-strip point this limit is nonzero for every
natural `m`, including `m=0`. Therefore no finite multiplicative level is
submass.

## Strongest positive survivor

The exact residue hierarchy is the positive survivor. Canonical Frobenius
multiplication rigidly propagates the one-particle obstruction through every
finite Witt power:

```text
R_m(rho) = R_1(rho)^m.
```

This is stronger than failure of one attempted exponent. It classifies the
entire finite multiplicative closure of the polarized aggregate under the
fixed first-ghost reader.

## Frontier effect

Cross-pair coupling cannot be obtained by multiplying already aggregated
big-Witt sources. That operation occurs after the Hermitian energy collapse
and therefore only powers the lost-phase scalar. A live construction must
couple pair labels before positive norm/first-ghost scalarization, through a
singular one-leg trace or an equivalently phase-sensitive nonlocal source
relation.

## Audit

- direct foreground `lake env lean` passes
- exact leaf-only `lake build` passes; umbrella not built
- declaration axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`
- no computation, RH-equivalent premise, or new axiom occurs
