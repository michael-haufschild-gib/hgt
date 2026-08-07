# Suzuki Interior-Excursion Shift Selection

- **ID:** suzuki-interior-excursion-shift-selection
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** Suzuki 2026 finite-aperture defect path; prime--Gamma Xi first-defect calibration
- **Statement:** Ground-pole polarization is sufficient but not necessary for Suzuki's canonical
  Xi-matching shift. A single strict interior resolvent excursion above the Xi calibration,
  together with non-target endpoint limits, produces the same attained greatest-root selector.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
  `[NOVELTY-BOUNDARY-AUDITED]`

## Goal

Prevent an illegitimate collapse of the live Suzuki route to the bottom-reflection-cone conjecture.
The ground cone gives an endpoint sign change and is a strong source theorem, but a continuous
defect path can cross the target in its interior even when both endpoint values lie below it.

This card proves the complete topological selector once one literal finite-shift witness exists.
It does not prove that Suzuki's restricted-Weil path has such an excursion, construct the
two-angle meromorphic limit, or imply RH.

## Setup

Let

```text
kappa : (-infinity,lambda_a) -> R
```

be a continuous Suzuki defect-angle path with endpoint limits

```text
kappa(lambda) -> kappa_free       (lambda -> -infinity),
kappa(lambda) -> kappa_ground     (lambda -> lambda_a-).  (1)
```

Fix a target `kappa_*`, and put

```text
S_*={lambda<lambda_a : kappa(lambda)=kappa_*}.            (2)
```

## Theorem 1: class-complete greatest-root law

Assume

```text
kappa_free != kappa_*,
kappa_ground != kappa_*,
S_* is nonempty.                                         (3)
```

Then `S_*` has a greatest member. In particular,

```text
lambda_*=sup S_*
```

is attained and

```text
IsGreatest S_* lambda_*.                                 (4)
```

### Proof

Because the free limit avoids `kappa_*`, one far-negative half-line contains no roots. Because
the ground limit avoids `kappa_*`, one punctured interval below `lambda_a` contains no roots.
Thus every root lies in one compact interval `[L,U]` contained in
`(-infinity,lambda_a)`. Continuity makes the root set closed there. A nonempty compact subset of
the real line attains its maximum, and its supremum equals that maximum.

The argument uses no endpoint ordering, monotonicity, differentiability, or root uniqueness.

## Theorem 2: interior-overshoot branch

Assume

```text
kappa_free < kappa_*,
lambda_0 < lambda_a,
kappa_* < kappa(lambda_0).                               (5)
```

Then `S_*` is nonempty. If also `kappa_ground!=kappa_*`, Theorem 1 gives the canonical greatest
root.

### Proof

The free limit supplies `lambda_1<lambda_0` with
`kappa(lambda_1)<kappa_*`. The intermediate value theorem on `[lambda_1,lambda_0]` produces a
root. Theorem 1 then applies.

For the unconditional Xi calibration, cofinal apertures already satisfy

```text
kappa_free(a)<kappa_Xi.
```

Hence one strict literal finite-shift inequality

```text
kappa_Xi < kappa_a(lambda_0)                              (6)
```

is enough, regardless of whether the bottom residue lies above or below `kappa_Xi`.

## Exact source form

At any finite shift with parity energies `E+O!=0`,

```text
kappa=(E-O)/(E+O)=kappa_*
iff
(1+kappa_*)O=(1-kappa_*)E.                               (7)
```

Likewise the strict overshoot in (6) is exactly

```text
(1+kappa_Xi)O(lambda_0)
  <(1-kappa_Xi)E(lambda_0).                              (8)
```

Thus the full first-jet source problem is a disjunction:

```text
pole branch:
  bottom reflection cone,

interior branch:
  finite-shift parity-resolvent excursion (8).           (9)
```

The pole branch is not the route itself.

## Hostile falsification audit

- If either endpoint equals the target, roots may accumulate at that endpoint and a greatest
  interior root need not exist.
- A nonempty matching set is indispensable; endpoint avoidance alone gives no root.
- An interior value equal to the target is enough for nonemptiness but not a strict sign-change;
  the strict overshoot in (5) is a convenient source-verifiable sufficient condition.
- If the ground cone fails, the interior branch remains logically alive. Declaring Suzuki dead
  from ground failure alone would be false.
- If every finite shift satisfies `kappa(lambda)<kappa_Xi` and the ground endpoint is also below
  it, then no first-jet matching shift exists. Proving that uniform inequality for the literal
  restricted-Weil path would close the selector negatively.

## Strongest positive conclusion

The exact cofinal first-jet target is no longer one bottom-eigenspace conjecture. At every
sufficiently large aperture, prove either the bottom reflection cone or one finite-shift
restricted-Weil overshoot. Endpoint avoidance then canonically selects the greatest matching
shift in both cases.

This enlarges the live source class without weakening provenance: the witness must come from
Suzuki's literal resolvent energies, not an abstract positive model.

## Novelty audit

Compact trapping of a continuous real root set and the intermediate value theorem are classical
and are not claimed as new. The candidate new knowledge is the Suzuki-specific correction:
mixed-ground pole polarization is only one sufficient branch, while a source-generated interior
resolvent excursion yields the identical canonical greatest-shift selector under strictly weaker
endpoint ordering. Targeted searches around Suzuki's 2026 screw-function construction found no
statement of this two-branch Xi-calibrated selector. Search absence does not establish priority;
specialist review remains required.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiInteriorExcursionShiftSelection.lean
```

Capstone declarations:

```text
suzukiDefectAngle_eq_target_iff
exists_isGreatest_suzukiDefectMatchingShiftSet_of_witness
exists_suzukiDefectMatchingShift_of_interior_overshoot
primeArchSuzukiGreatestDefectShift_spec_of_interior_overshoot
```

All theorems are unconditional. No `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, or computation
occurs.

## Log

- 2026-08-01 — pole-only simplification rejected; complete interior-excursion selector paper
  proof and unconditional Lean formalization completed.
