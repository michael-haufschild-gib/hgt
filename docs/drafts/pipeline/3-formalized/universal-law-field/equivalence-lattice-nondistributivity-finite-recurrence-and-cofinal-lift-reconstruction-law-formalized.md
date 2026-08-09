# Doctrine-lattice nondistributivity, finite recurrence, cofinal lift — Lean certification

- **ID:** ULF-DOCT-1
- **Paper card:**
  `equivalence-lattice-nondistributivity-finite-recurrence-and-cofinal-lift-reconstruction-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineLattice`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Reused corpus layer:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion` (`loopHistory`, `logLift`)

## Certified declarations

### Theorem 2.1 — the doctrine lattice is nondistributive

Observer doctrines are `Setoid`s, ordered by mathlib's complete lattice of equivalence relations
(meet = intersection, join = equivalence closure of the union).  `pointDoctrine k` is the doctrine
on `Fin 3` that separates `k` and identifies the other two states, so `pointDoctrine 2 = 12|3`,
`pointDoctrine 1 = 13|2`, `pointDoctrine 0 = 1|23`.

- `pointPair_separating` — two distinct point doctrines already separate every pair of states;
- `inf_pointDoctrine` — hence distinct point doctrines meet in `⊥`, the equality relation;
- `sup_pointDoctrine` — distinct point doctrines join to `⊤`: the third state is related to
  everything through one or the other doctrine;
- `pointDoctrine_ne_bot` — a point doctrine is not the equality relation;
- `doctrine_not_distributive` — therefore
  `α ⊓ (β ⊔ γ) = α ⊓ ⊤ = α` while `(α ⊓ β) ⊔ (α ⊓ γ) = ⊥ ⊔ ⊥ = ⊥`, and these differ.

### Theorem 3.1 — every finite doctrine family sees closed recurrence

`sourceShift` is `n ↦ n + 1` on `ℤ` and `modDoctrine m` is the congruence doctrine mod `m`.

- `sourceShift_mod` — the induced history on `ZMod m` is translation by one;
- `shiftMod_iterate` — its `k`-th iterate is translation by `k`;
- `induced_history_exact_period` — the induced history closes after exactly `m` steps and after no
  smaller positive number of steps;
- `jointObserver F` is the joint reader into `∏_{m ∈ F} ZMod m`.  `jointObserver_eq_iff` reduces a
  period to simultaneous divisibility and `jointObserver_periodic_iff` identifies the exact period
  set with the multiples of `Finset.lcm F id`;
- `jointObserver_fibre_infinite` — the fibre over any value contains every multiple of the lcm and
  is therefore infinite, so no finite family reconstructs the lift.

### Theorem 3.2 — the cofinal family reconstructs the open lift

`cofinal_separating` proves that agreement modulo every `m ≥ 2` forces equality in `ℤ`: the
difference is divisible by `|d| + 2`, which forces it to vanish.  `modDoctrine_iInf_eq_bot` states
the same fact as an identity in the doctrine lattice: the infimum of all congruence doctrines is the
equality relation.

### Section 4 — the phase doctrine is another doctrine, not a universal law

`modulusReader` reads the modulus of a nonzero complex number as a positive real;
`modulusReader_surjective` and `phaseQuotientEquiv` prove the phase-doctrine quotient is *exactly*
`ℝ_{>0}`.  `phaseDoctrine_loopUnit` shows the `N`-fold winding loop of `ULF-TORS-1` is a single
constant history for that doctrine, while `phase_constant_lift_open` pairs this with the openness of
its logarithmic lift.

### Capstone

`dynamic_equivalence_law` bundles nondistributivity, the exact lcm period, the infinite fibres, and
the cofinal separation for an arbitrary finite family of congruence doctrines.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDoctrineLattice.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineLattice
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on nondistributivity, the exact induced
period, the joint period criterion, the infinite fibres, the cofinal intersection, the phase
statement, and the capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.  No
project axiom, placeholder, hypothesis interface, or unresolved theorem premise is used.

## Exact field consequence

Combining identifications is intrinsically non-Boolean before any topology, probability, or
curvature enters: what two observer doctrines jointly retain does not decompose into independent
pieces.  Recurrence is then a property of the *family* of doctrines, not of the source: every finite
congruence family sees an exactly periodic closed history with infinite fibres, and only a cofinal
separating family recovers the nonperiodic lifted translation.  Positivity is one such doctrine
among many.
