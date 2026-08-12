# Sonin complex-phase odd Fisher Frankenstein splice

- **ID:** `sonin-complex-phase-odd-fisher-frankenstein-splice`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CROSS-ROUTE SPLICE / EXACT OPEN CORE
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL BRIDGE] [NOT RH]`
- **Statement:** One common cofinal Sonin schedule retains the two complex Fisher orientations
  `+it` and `-it`; their signed limit is
  `4 * I * t * (1 - t^2) / (1 + t^2)^2`, whose zero fibre on the Xi strip is exactly the zero
  fibre of the source-zero horizontal carrier and exactly equality of the two coefficient-faithful
  deconvolved prime-orientation classes.

## Goal

Replace the orientation-destroying positive Fisher scalar landing by a signed complex phase before
scalarization, while preserving each Xi divisor copy, source transport, prime coefficient field,
and both reflection orientations. Test whether source involution or another existing route then
annihilates the signed observable unconditionally.

## Gates

- [x] 0 → 1: positive scalarization wall isolated; complex pre-scalar phase selected
- [x] 1 → 2: complex Euler limit, shared-depth diagonal, odd profile, and zero-radical bridges proved
- [x] 2 → 3: exact Lean leaf built and capstones axiom-audited
- [ ] 3 → 4: requires a source theorem forcing the odd observable to vanish; this is presently the
  RH-equivalent open producer

## Result

For every fixed inward complex phase `u`, the critical squarefree Fisher current has limit

```text
2u / (1+u)^2.
```

For the reflection pair `u=it` and `u=-it`, Lean constructs one shared sequence of finite Sonin
depths, not two independently chosen schedules, on which the difference converges to

```text
P(t) = 4 i t (1-t^2) / (1+t^2)^2.
```

The Xi source law already proves `|t|<1`. Therefore `P(t)=0 ↔ t=0`. The new copywise
specialization and Frankenstein bridges prove

```text
P(t_q)=0
  ↔ sourceZeroHorizontalCarrierAt K q = 0
  ↔ fisherDeconvolvedOrientationClass t_q
       = fisherDeconvolvedOrientationClass (-t_q)
  ↔ Re(q)=1/2.
```

No divisor sum occurs: `q : XiZeroCopy` retains prime labels through the carrier families and
retains divisor multiplicity through the copy index.

## Conjecture → proof/failure loop

1. **Positive Sonin/Fisher landing orients reflection.** Failed: both real landings are eventually
   strictly positive.
2. **Complex pre-scalar Fisher phase survives non-equivariant Sonin pullback.** Proved for arbitrary
   fixed inward complex `u`.
3. **Separate cofinal schedules suffice for the two orientations.** Rejected: schedule mismatch
   would destroy coefficient-faithful subtraction.
4. **One finite-depth schedule carries both `+it` and `-it`.** Proved by diagonalizing the signed
   finite-depth error itself.
5. **The signed profile detects horizontal displacement.** Proved sharply on `|t|<1`; its only
   zero is `t=0`.
6. **Existing source involution forces signed-profile vanishing.** Failed: corpus involution laws
   exchange the two classes; fixedness/equality is already equivalent to neutral grade.
7. **Existing source carrier and same-carrier orientation laws are unrelated receivers.** Failed:
   Lean proves they have exactly the same copywise zero fibre as the Sonin odd profile.

## No-go closure

- **Exact killing mechanism:** source reflection supplies interchange `t ↔ -t`, not equality.
  Asking it to annihilate `P(t)` is equivalent to asking the deconvolved orientations to coincide,
  hence equivalent copywise to `t=0`.
- **Strongest positive survivor:** explicit signed cofinal observable plus exact cross-route
  identification with both complete source-zero carrier and deconvolved same-carrier orientation
  equality.
- **New insight:** analytic Sonin transport, resolution/prime-Bockstein carrier, and coefficient-field
  orientation quotient are not three open cores. They are three realizations of one radical. A
  future proof must produce vanishing before these receiver equivalences, from an independent
  arithmetic conservation/cancellation law.
- **Status:** dependency-closed and formalized. Global vanishing remains unproved and is explicitly
  audited as RH-equivalent.

## Lean realization

Module:

```text
GaloisForLFunctions.RHTower.SoninCofinalComplexPhaseOddFisherSplice
```

New capstones:

```text
xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff
exists_xiZeroSoninCofinalCriticalPhaseOddFisherScore_diagonal
xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff_sourceCarrier
xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff_orientationClass
xiZeroSoninCriticalPhaseOddFisherVanishes_iff_riemannHypothesis
```

## Verification

- `lake env lean GaloisForLFunctions/RHTower/SoninCofinalComplexPhaseOddFisherSplice.lean`: pass
- `lake build GaloisForLFunctions.RHTower.SoninCofinalComplexPhaseOddFisherSplice`: pass
- umbrella import: present
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-08-12 — added multiplicity-labelled Xi specialization, exact horizontal-carrier and
  same-carrier orientation bridges, RH-equivalence audit, umbrella wiring, and leaf build
