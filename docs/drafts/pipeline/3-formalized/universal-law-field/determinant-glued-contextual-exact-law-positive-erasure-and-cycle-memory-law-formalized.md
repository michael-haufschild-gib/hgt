# Determinant-glued contextual exact law, positive erasure, cycle memory — Lean certification

- **ID:** ULF-DGLU-1
- **Paper card:**
  `determinant-glued-contextual-exact-law-positive-erasure-and-cycle-memory-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantGluing`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Reused corpus layers:**
  `HTGeometry.ConstitutiveParityContextuality` (ULF-CTX-1),
  `HTGeometry.ConstitutiveDeterminantTorsion` (ULF-TORS-1)

## Certified declarations

### The sign dictionary

`paritySign x = (-1)^x` is proved to be an injective character of the parity group
(`paritySign_add`, `paritySign_injective`, `paritySign_eq_one_iff`) with
`paritySign_prod : paritySign (∑ f) = ∏ paritySign ∘ f`.  Hence:

- `vertex_determinant_constraint` — `∏_{e ∋ v} ε_e = (-1)^{b v}` **is** `∂_G x v = b v`;
- `anomaly_eq_one_iff` — `∏_v (-1)^{b v} = 1` **is** `∑_v b v = 0`.

### Theorem 2.1 — one determinant law carries effectivity and hidden memory

- `glued_anomaly_trivial` certifies (DG.12): for *any* glued family the double product over vertices
  and incident edges is one, because every edge sign is counted twice.  Odd charge is therefore a
  literal determinant-gluing anomaly.
- `exists_glued_law_iff` proves the three-way equivalence: a global exact law exists iff the total
  charge is even iff the anomaly is one.
- `solutionEquivKernel` exhibits the solution set as a torsor over the cycle space
  `ker ∂_G` (translation by any one solution; the inverse is the same map, by characteristic two),
  and `card_gluedLaws` computes, using `finrank_range_parityBoundary` and rank–nullity,

  `#{global exact laws} = 2 ^ (|E| + 1 − |V|) = 2 ^ β₁(G)`.

### Theorem 3.1 — every proper observer face is exact

Certified by `exists_parityBoundary_eq_on_of_ne_univ` (ULF-CTX-1) and re-exported inside
`positive_erasure` and `determinant_gluing_law`.

### Corollary 4.1 — positive erasure

`positive_erasure` bundles the three lossy readings and shows they are the same for *every* pair of
charges: each local complex `C(ε)` with `ε = ±1` is acyclic in both degrees
(`torsionDifferential_ker`, `torsionDifferential_range` of ULF-TORS-1), its positive determinant
shadow is `1` (`positiveShadow_paritySign`), and every proper observer face is exact.  None of the
three sees the anomaly or the cycle-memory torsor.

### Capstone

`determinant_gluing_law` bundles effectivity, the trivial glued anomaly, the cycle-memory count, and
proper-face exactness for one connected graph and one charge.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDeterminantGluing.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantGluing
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No project axiom, placeholder, hypothesis interface, or unresolved theorem premise is
used.

## Exact field consequence

Object-level effectivity, stable determinant memory, and positivity are three readings of one
restriction law, not three independent models multiplied together: the same incidence equation
decides whether a global law exists, is the determinant anomaly when it does not, is a torsor over
the cycle space when it does, and is invisible to the positive scalar shadow throughout.  Oriented
determinant gluing is load-bearing.
