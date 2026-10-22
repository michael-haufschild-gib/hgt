# Fixed-shift Hankel-tail to dyadic RH bridge

- **ID:** `fixed-shift-hankel-tail-dyadic-bridge`
- **Stage:** Lean-formalized bridge; retained in progress because source positivity remains open
- **Type:** THEOREM / right-to-left RH reduction
- **Lean targets:**
  `formal/GaloisForLFunctions/RHTower/TraceHankelConverse.lean`,
  `formal/GaloisForLFunctions/RHTower/XiShiftedReciprocalHankelTailCriterion.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamTailFromSixtyFour.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredSeamPowerSixtyFourMassCriterion.lean`

## Goal

At a fixed nonnegative real Möbius shift `y`, put

```text
w_q = lambda_q / (1 + y lambda_q),
lambda_q = -(rho_q - 1/2)^(-2).
```

For every cutoff `M`, prove that positivity of every finite Hankel quadratic using only shifted
moments from order `2M+1` onward is equivalent to RH.  At `y=1`, identify `w_q` with the existing
fixed-shift squared-Xi seam coordinate.  This gives the exact backward chain

```text
cofinal fixed-shift Hankel cone
  -> every shifted atom is real
  -> dyadic tail from power 64
  -> RH.
```

## Paper proof

The map `lambda -> lambda/(1+y lambda)` preserves conjugation, is injective, never vanishes on an
Xi atom, and satisfies

```text
Im(w_q) = Im(lambda_q) / |1+y lambda_q|^2.
```

Thus `w_q` is real exactly when `lambda_q` is real.  The shifted family is trace class because
`|w_q| <= |lambda_q|`, and only finitely many shifted atoms exceed any positive norm threshold.

Fix a hypothetical nonreal atom `alpha=w_q`.  Multiplication by `X^M` does not vanish at `alpha`.
The phase-corrected outer-orbit separator annihilates every atom of modulus at least `|alpha|`
except the `alpha`/`conj(alpha)` fiber, while a radial monomial suppresses the inner atoms.
Dominated convergence leaves a finite sum of strictly negative conjugate-pair contributions,
contradicting nonnegativity on the principal ideal `X^M R[X]`.  Hence every shifted atom is real,
so every Xi reciprocal square is real and RH follows.

Conversely RH makes every shifted atom positive real, hence every tail Hankel quadratic is a sum
of nonnegative atomic squares.

At `y=1`, direct algebra gives

```text
xiShiftedReciprocalSquare 1 q = xiSquaredSeamOneCoordinate q.
```

Therefore the tail criterion directly supplies the dyadic tail from power `64`.

## Tail-from-64 phase collapse

The earlier chain retained a separate power-32 annulus hypothesis.  It is redundant.  Tail
nonnegativity makes `w_q^64` satisfy the complete dyadic half-plane condition, hence
`w_q^64` is nonnegative real.  The unconditional strict power-16 sign selects `w_q^16` as the
positive real fourth root.  The unconditional strict power-8, power-4, power-2, and power-1 signs
then select the positive square root successively.  Thus `w_q` is positive real and RH follows.

Lean proves

```text
XiSquaredSeamDyadicTailFromSix <-> RiemannHypothesis.
```

This removes `XiSquaredSeamPowerThirtyTwoAnnulusEmpty` from the live backward chain without
proving that annulus empty separately.

## Gates

- [x] prior-corpus audit: central principal-ideal converse exists; fixed-shift tail converse does not
- [x] dependency-closed paper proof
- [x] reusable countable principal-ideal converse in Lean
- [x] fixed-shift tail criterion in Lean
- [x] fixed-shift/seam coordinate identity in Lean
- [x] tail-from-64 phase collapse in Lean
- [x] direct shifted-Hankel/source-tail to dyadic-tail connectors in Lean
- [x] single power-64 Hermitian/source inequality criterion in Lean
- [x] RHTower umbrella imports wired
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] `scripts/formal_tools.py lint`
- [x] target build:
      `lake build GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion`
- [ ] prove source-built `PrimeArchShiftedReciprocalHankelTailNonnegative 1 M` for one cutoff
- [ ] RH

## Single-scalar right-edge reduction

The cofinal Hankel cone is sufficient but no longer the smallest live predecessor.  Put

```text
H64 = sum_q |w_q^64|,
S64 = Re(primeArchShiftedReciprocalMoment 1 63)
    = sum_q Re(w_q^64).
```

The triangle inequality gives `S64 <= H64` unconditionally.  Lean now proves

```text
H64 <= S64 <-> RiemannHypothesis.
```

Indeed, reverse domination forces equality.  Since every pointwise defect
`|w_q^64| - Re(w_q^64)` is nonnegative and summable, equality forces every defect to vanish.
Thus every `w_q^64` is nonnegative real; its positive integer powers give the complete dyadic tail
from `64`, which implies RH by the phase-collapse theorem.  Under RH every `w_q` is positive real,
so equality holds term by term.

This moves the open right edge from all-degree Hankel positivity to one scalar comparison:

```text
[OPEN] Hermitian power-64 mass H64 <= explicit prime--Gamma source moment S64
  -> dyadic tail from power 64
  -> RH.
```

The remaining mathematical channel is precise: realize or dominate the anti-holomorphic mass
`sum_q |w_q|^64` from unconditional source data.  Holomorphic moment transport alone gives `S64`
and cannot silently replace this paired/conjugate mass.

## Degree-32 transverse-charge identification

The Hermitian gap is not an opaque norm difference.  Pointwise,

```text
|w^64| - Re(w^64)
  = |w^32|^2 - Re((w^32)^2)
  = 2 Im(w^32)^2.
```

Lean proves the global identity

```text
H64 - S64 = 2 C32,
C32 = sum_q Im(w_q^32)^2 >= 0,
H64 <= S64 <-> C32 = 0 <-> RH.
```

Thus the most-right open source target can be stated without a norm inequality:

```text
[OPEN CORE C32] prove from the prime--Gamma/source response that
  sum_q Im((lambda_q/(1+lambda_q))^32)^2 = 0.
```

This is a single fixed rational-aperture transverse charge.  It is narrower than the existing
all-degree polynomial charge interface.  Any proposed producer must identify this paired square
from source data; proving only the holomorphic trace `S64` or its sign does not touch `C32`.

The paper theorem
`../2-fully-proven/new_scientific_knowledge/shift-one-seam-power64-cassini-jensen.md` now realizes
the Hermitian mass as a weighted Jensen integral of the canonical translated squared source
`Psi(u)=Phi(1-u)`, centered at `Psi(0)=xi(3/2)`.  This gives the source-only predecessor

```text
[OPEN] 8192 * integral_0^infinity E64(r)/r^65 dr <= S64
  -> C32=0
  -> RH.
```

Lean now proves the exact atom integral and Tonelli divisor sum in
`formal/GaloisForLFunctions/RHTower/XiSquaredSeamPowerSixtyFourJensenKernel.lean`, the exact
functional-equation pair quotient in
`formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniPairQuotient.lean`, and the complete
circle-average weld and global identity `H64 = 8192 * integral E64(r)/r^65 dr` in
`formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniGlobalJensenLaw.lean`.  No source/divisor,
multiplicity, pairing, Tonelli, or circle-average interface remains open.  Exact rightmost open
statement is now only the Cassini--Jensen domination inequality displayed above.

Lean additionally proves the exact residual law

```text
C32 = 4096 * integral_0^infinity E64(r)/r^65 dr - S64/2 >= 0,
residual = 0 <-> RH.
```

This rules out treating Jensen nonnegativity or a generic structured-variance lower bound as the
missing producer: those are the unconditional `C32 >= 0` direction.  Required new input must force
the same residual to vanish, equivalently reverse its already-proved nonnegative orientation.
