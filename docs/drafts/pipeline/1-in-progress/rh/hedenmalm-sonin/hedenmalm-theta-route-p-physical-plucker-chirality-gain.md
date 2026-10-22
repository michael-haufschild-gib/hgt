# Route-P physical Pluecker chirality gain

- **ID:** `P-G79`
- **Stage:** `1-in-progress`
- **Type:** exact source-faithful local Schur gain
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `../../../5-failed/route-p-critical-plucker-complement-depletion-audit.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalPhysicalPluckerChiralityGain.lean`

## Conjecture P-G79.A: physical cross-prime chirality improves the half-factor

P-G76 proved that complement averaging artificially forces a half-Fisher factor and that physical
same-prime chirality is invisible to the prime-only Fisher clock. The survivor required a literal
cross-prime cell. Test the hostile cell

```text
(2,0), (2,1), (3,0), (3,1)
```

with its source-defined harmonic aperture and unsymmetrized Gamma-sewn Cauchy--Binet packet.

**Verdict: true, unconditionally proved.** The complement-odd Fisher correction factorizes exactly:

```text
sum_s chi_w(s) F_comp(s)
  = 2 (w_0 - w_5) (F_3 - F_2).
```

All mixed complementary pairs cancel. Lean proves both remaining factors strictly positive:

```text
rawWeight((2,0),(2,1)) > rawWeight((3,0),(3,1)),
F_3 > F_2.
```

Normalization preserves first inequality. Hence physical Schur fraction is strictly greater than
`1/2`; no complement averaging or fitted scalar appears. A second strict estimate proves the
fraction is below `1`: positive physical pair probabilities leave a strictly positive selected
Fisher mean. Therefore every information-depleted residual coefficient remains strictly positive.

```text
1/2 < physical Schur fraction < 1,
0 < physical reducedWeight(pk) < (1/2) depletedWeight(pk).
```

## Closed hostile gate

P-G76 already proved half the information-depleted hostile mass lies below completed-seam ceiling
`29/625`. Since literal physical fraction is strictly larger than half, Lean now proves

```text
sum_(i : Fin 4) physicalReducedWeight(hostileCell i) < 29/625.
```

This replaces P-G76's conditional symmetrized local adequacy with unconditional physical local
adequacy.

## Higher universal principle

Complement chirality is not merely data lost by scalarization. On a cross-prime packet it becomes
an ordered covariance between two monotone source axes:

```text
minor mass decreases with prime scale,
Fisher clock increases with prime scale.
```

Their opposite ordering gives positive complement-Fisher gain. Same-prime failure was the shadow
of a missing heterogeneous axis: depth changes chirality but not Fisher clock; prime changes both.
Correct operation is therefore **retain chirality until it meets a cross-prime monotone clock**, not
erase chirality by symmetry and not compress each prime fibre independently.

## Lean realization

Headline declarations:

- `gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq`;
- `gammaSewnCriticalPhysicalPlucker_p3ConsecutiveRawWeight_lt_p2`;
- `gammaSewnCriticalPhysicalPlucker_probability_five_lt_zero`;
- `gammaSewnCriticalPhysicalPlucker_chiralityFisherMoment_eq`;
- `gammaSewnCriticalPhysicalPlucker_chiralityFisherMoment_pos`;
- `gammaSewnCriticalPhysicalPlucker_schurFraction_gt_half`;
- `gammaSewnCriticalPhysicalPlucker_complementaryFisherMean_lt_total`;
- `gammaSewnCriticalPhysicalPlucker_schurFraction_lt_one`;
- `gammaSewnCriticalPhysicalPlucker_reducedWeight_pos`;
- `gammaSewnCriticalPhysicalPlucker_reducedWeight_lt_half`;
- `gammaSewnCriticalPhysicalPlucker_reducedHostileMass_lt_ceiling`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalPhysicalPluckerChiralityGain
Build completed successfully (12732 jobs).
```

Capstone `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Full-corpus formal lint currently reports unrelated concurrently added modules absent from theorem
umbrellas. P-G79 itself is umbrella-wired and contains no `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` declaration.

## Next conjecture P-G80

Generalize prime `2 < 3` comparison. For arbitrary ordered primes `p < q` and any aperture
`0 < a < log(p)/2`, prove consecutive-depth physical minor at `p` exceeds that at `q`. The same
factorization would give a universal positive chirality--Fisher theorem on every ordered two-prime
cell. Then audit whether cofinal all-prime packetization preserves enough gain to dominate complete
critical mass without assuming global Feshbach identification.

## Honest boundary

P-G79 closes exact hostile local mass obstruction with a positive coefficientwise physical source
residual. It does not yet prove global all-prime summability/sign, identify scalar fraction with actual Feshbach
elimination, sew archimedean/polar channels, or prove RH.
