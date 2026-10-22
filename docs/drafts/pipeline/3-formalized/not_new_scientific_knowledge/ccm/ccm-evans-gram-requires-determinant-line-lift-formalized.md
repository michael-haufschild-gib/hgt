# Evans Gram requires a determinant-line lift — formalized closure

- **ID:** `ccm-evans-gram-requires-determinant-line-lift-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-evans-gram-requires-determinant-line-lift.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.HTGeometry.ComplexGramPlucker` — the complex Cauchy–Binet law, absent from
  mathlib: the Hermitian Gram determinant of a finite complex feature family is the sum of the
  squared moduli of its maximal coordinate minors, that is, the squared Pluecker norm of the top
  exterior power. Reusable, source-free, so it lives in `HTGeometry`.
- `GaloisForLFunctions.RHTower.CCM.CCMEvansDeterminantLine` — the Evans specialization and both
  obstructions.

Umbrellas: `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`, `(2)` | `evansExcessTarget`, `evansPlucker`, `evansGram` | the `(d+3)`-dimensional excess target, the top exterior power of the images of a basis of the `d`-dimensional source, and the Hermitian Gram matrix |
| `(3)` | `det_hermFeatureGram_eq_pluckerNormSq`, `det_evansGram_eq_pluckerNormSq` | `‖P‖² = det(M*M)`: the Gram determinant equals `∑_s \|minor_s\|²`. Proof: pair the exterior dual wedge of the Hermitian row functionals against the feature wedge, expand in the exterior basis, and use that the dual wedge reads each basis vector as the conjugate of the matching minor |
| `(4)` | `evansPlucker_eq_zero_iff`, `det_evansGram_ne_zero_iff`, `hermFeatureWedge_eq_zero_iff`, `det_hermFeatureGram_ne_zero_iff` | the Pluecker vector vanishes exactly when the presentation has a kernel, and so does the Gram determinant. The Gram half is proved directly from the Hermitian energy identity `∑_i conj(c_i)(G c)_i = ∑_k \|∑_j c_j v_j(k)\|²`, so no exterior-power independence lemma is needed |
| positivity | `det_evansGram_eq_nonneg_real`, `hermPluckerNormSq_nonneg` | the Gram determinant is a nonnegative real |
| target is not a line | `finrank_exteriorPower_evansExcessTarget`, `one_lt_choose_add_three`, `one_lt_finrank_exteriorPower_evansExcessTarget`, `not_nonempty_linearEquiv_exteriorPower_evansExcessTarget` | `dim ⋀^d Y = binomial(d+3,d) > 1` at every positive `d`, so `⋀^d Y` admits no linear isomorphism with the scalars: `P_a` is not a section of a determinant line |
| orientation is forgotten | `evansPlucker_update_neg`, `hermPluckerNormSq_update_neg`, `det_evansGram_update_neg` | reversing the sign of one source vector reverses the Pluecker vector and leaves the Gram determinant unchanged |
| no canonical scalar | `exists_scalar_extraction_disagreement` | at every kernel-free presentation there are two scalar extractions of `P_a`, one nonzero and one vanishing. A scalar read off the rectangular Pluecker vector therefore does not detect the kernel, while the Gram determinant does |

## Axioms

`#print axioms` on every non-private theorem of both modules (30 declarations checked) returns
exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

- The exact finite Evans reduction identifying `ker M_a` with `ker G_a`: that is the content of
  `ccm-rational-residual-finite-evans-matrix-law.md`, a parent of this card.
- The analytic Fredholm determinant line of the restricted Weil family with its crossing-form
  orientation — the missing carrier `(5)` that the card names as an open gate.

## Verification performed

- `lake env lean` on both modules: no errors.
- `lake build` of each new module: success.
- `#print axioms` on every non-private theorem: clean.
- Umbrella imports added for both modules.
