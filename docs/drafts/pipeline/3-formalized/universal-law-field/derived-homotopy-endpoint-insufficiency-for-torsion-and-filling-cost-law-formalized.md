# Derived/homotopy endpoint insufficiency — Lean certification

- **ID:** ULF-ENDP-1
- **Paper card:**
  `derived-homotopy-endpoint-insufficiency-for-torsion-and-filling-cost-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveEndpointInsufficiency`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Reused corpus layers:**
  `HTGeometry.ConstitutiveDeterminantTorsion` (acyclicity and determinant history of `C(u)`),
  `HTGeometry.ConstitutiveQuadraticFilling` (null words, van Kampen area)

## Certified declarations

### Theorem 1.1 — the derived observer is lossy

A *derived observer* of the based family is an observer that cannot separate complexes with the
same homology: the same degree-one kernel and the same degree-zero image (`DerivedObserver`).  Since
`homology_indistinguishable` (ULF-TORS-1) proves every `C(u)` with `u ≠ 0` has kernel `⊥` and image
`⊤`, the hypothesis of a derived observer is always available, so `derivedObserver_constant` proves
every derived observer is constant on the whole family.  `torsion_not_derivedObserver` then shows
the determinant history `u ↦ u` is *not* a derived observer whenever the unit group has two distinct
elements.  This is exactly the card's statement that torsion does not factor through `D^b(k)`,
stated in terms of the homological data through which such a factorisation must pass.

### Theorem 2.1 — the endpoint observer is lossy

An *endpoint observer* of words is one that factors through the class in the presented group
`⟨a,b | [a,b]⟩` (`EndpointObserver`).  `nullWord_eq_one_in_quotient` (ULF-FILL-1) makes every null
word trivial there, so `endpointObserver_constant` proves every endpoint observer takes one value on
`{w n}`, while `area_not_endpointObserver` shows the van Kampen area does not: `area (w 1) = 1` and
`area (w 2) = 4`.

### Theorem 2.1, unweighted-topology half

`gridVertices n = (n+1)²`, `gridEdges n = 2n(n+1)`, `gridFaces n = n²` are the cell counts of the
`n × n` grid filling, and `gridFaces_eq_area` matches the face count with the certified area.
`grid_euler` proves

`V − E + F = 1`

for every `n` — the Euler characteristic of a disk.  Hence `eulerObserver_constant` proves every
observer factoring through the unweighted type (recorded by the Euler characteristic) is constant on
the family, while `gridFaces_not_eulerObserver` shows the cellular area is not.

### Capstone

`endpoint_insufficiency` bundles the six statements over `ℚ`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveEndpointInsufficiency.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveEndpointInsufficiency
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` reports only `propext`, `Classical.choice`,
and `Quot.sound`; the two Euler-characteristic statements need only `propext`.  No project axiom,
placeholder, hypothesis interface, or unresolved theorem premise is used.

## Scope note

The derived half is certified through the homological data — kernel and image in the two degrees —
that any factorisation through the derived category must respect; the categorical localisation
itself is not constructed, since the no-go needs only that a derived observer is a function of the
homology.  The unweighted half is certified through the Euler characteristic, the numerical shadow
of the homeomorphism type that the card invokes; the homeomorphism between the grid fillings and a
disk is not constructed, and the certified statement is correspondingly the Euler-characteristic
one.

## Exact field consequence

Ordinary derived and homotopy localisation is a strictly lossy observer of law history.  Determinant
memory and quantitative filling weight both survive the passage to the endpoint or to the unweighted
type only if carried as extra structure, so a universal law field cannot consist of homotopy types
and matching maps alone.
