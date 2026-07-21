# Prime-orientation completed-ring sign no-go

- **ID:** prime-orientation-completed-ring-sign-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** universal prime-orientation compact-open completion and exact simple-pole residues
- **Statement:** The completed common-atom ring is identical for orientations of opposite Herglotz status, so no predicate of that ring can classify positivity; pointed residues still separate every unequal pair.

## Goal

Determine exactly which HTGeometry data can survive into an RH-bearing Hilbert metric.  The theorem
rules out the unpointed completed function ring as a sign producer and identifies the minimal
source data that remains order-sensitive.

## Gates

- [x] 0 → 1 in-progress: exact carrier, sign predicate, and collision identified
- [x] 1 → 2 fully-proven: finite proof from compiled chamber invariance and Herglotz uniqueness
- [x] 2 → 3 formalized: permanent Lean theorem and direct leaf check
- [ ] 3 → 4 publication-ready: standalone mathematical exposition and external novelty audit

## Exact theorem

For a Boolean prime orientation `epsilon`, let

```text
IsHerglotz(epsilon)
 := for every z with Im z>0,
      Im(universalPrimeOrientationLimit epsilon z)>=0.
```

The corpus proves

```text
primeOrientationCompletedRing epsilon
 =primeOrientationCompletedRing delta
```

for all orientations, while

```text
IsHerglotz(epsilon) iff epsilon=(fun _ => false).
```

Therefore there are distinct `epsilon,delta` with equal completed rings and opposite Herglotz
status, and

```text
not exists P : Subring C(PrimeOrientationDomain,C) -> Prop,
  forall epsilon,
    P(primeOrientationCompletedRing epsilon) iff IsHerglotz(epsilon).
```

## Positive survivor

If `epsilon != delta`, some prime coordinate `p` differs.  The corresponding meromorphic carriers
have exact simple poles at `primeLogSupport p` with unequal residues

```text
-universalPrimeOrientationWeight epsilon p
  != -universalPrimeOrientationWeight delta p.
```

Thus compact-open ring completion is sign-blind, but the residue-pointed carrier is faithful.  The
existing finite-chamber Krein/Hamming laws then retain the number and location of orientation
disagreements.

## No-go closure

- **Exact killing theorem/mechanism:** completed-ring chamber invariance identifies every Boolean orientation, whereas Herglotz positivity distinguishes exactly one orientation.
- **Strongest positive survivor:** unequal orientations are separated by an explicit pointed simple-pole residue; the unquotiented residue vector remains faithful and order-sensitive.
- **New insight:** HTGeometry can supply independence, minimality, and residue coordinates, but not the missing sign after passing to the completed ring.  A true aperture Hilbert metric must live on a residue-pointed source cone and preserve its Krein orientation through localization.
- **Status:** formalized unconditionally in `PrimeOrientationCompletedRingSignNoGo.lean`; direct leaf check and exact module build pass.  The classifier no-go and pointed-residue survivor use only `propext`, `Classical.choice`, and `Quot.sound`.

## Lean certificate

Permanent declarations:

- `IsHerglotzPrimeOrientation`
- `isHerglotzPrimeOrientation_iff_allPositive`
- `exists_primeOrientation_completedRing_collision_oppositeHerglotz`
- `no_primeOrientationCompletedRing_HerglotzClassifier`
- `exists_primeOrientation_residue_separation_of_ne`

## Log

- 2026-07-20 — completed-ring sign blindness isolated and its pointed-residue survivor formalized.
- 2026-07-20 — exact module build and axiom audit passed.
