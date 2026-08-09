# Even Moore law cell, effectivity, memory, positive collapse — Lean certification

- **ID:** ULF-MOORE-1
- **Paper card:**
  `even-moore-law-cell-effectivity-memory-and-positive-topology-collapse-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveMooreLawCell`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

The Moore law boundary is `x ↦ xⁿ`; a boundary law `y` is filled by `x` when `xⁿ = y`, so `H₂` is
the set of units killed by the boundary and `H₁` is measured by which boundary laws are hit.
`pow_left_inj_nonneg` is the auxiliary injectivity of `n`-th powers on the nonnegative reals.

### Theorem 2.1 — parity dichotomy

- `odd_fill_existsUnique` — for odd `n` every nonzero boundary law has **exactly one** nonzero
  filling, namely `sign(y) · |y|^{1/n}`; both law-homology groups are therefore trivial;
- `even_fillable_iff` — for even `n` a nonzero boundary is fillable iff it is positive;
- `even_fill_eq_pair` — every positive boundary has exactly the two fillings `±y^{1/n}`;
- `even_units_pow_eq_one_iff` — the kernel on units is exactly `{±1}`, i.e. `H₂ ≅ {±1}`;
- `even_coker_two` — the image on units is exactly the positive units, `-1` is not in the image, and
  every unit is congruent to `1` or to `-1` modulo the image: `H₁ ≅ {±1}`.

### Theorem 3.1 and §4 — positivity repairs and erases

- `positive_fill_existsUnique` — over the positive coefficients every boundary has exactly one
  filling for every degree `n ≥ 1`, so both law-homology groups vanish;
- `positive_repairs_and_erases` — for even `n` and a negative boundary, no oriented filling exists
  while the absolute value has a unique positive filling: one coefficient change repairs the
  effectivity obstruction and erases the filling memory at once;
- `even_mixed_positive_reconstructible` — the even Moore boundary on units is neither injective nor
  surjective, the mixed phase of ULF-MATCH-1, while its positive base change has singleton fibres,
  the reconstructible phase.  The four-phase classification is therefore not invariant under
  coefficient doctrine.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveMooreLawCell.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveMooreLawCell
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No project axiom, placeholder, hypothesis interface, or unresolved theorem premise is
used.

## Exact field consequence

One boundary operator determines global effectivity, hidden filling memory, the shape of the
observer matching fibre, and what a positive observer loses — and a single change of coefficient
doctrine moves information between those layers, killing an obstruction and a memory group at the
same time.  The realization-phase classification is therefore a property of the pair (law,
coefficient doctrine), not of the law alone.
