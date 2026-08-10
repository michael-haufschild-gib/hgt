# Balanced defect, zero index, recurrent boundary, open history — Lean certification

- **ID:** ULF-DEFECT-1
- **Paper card:** `balanced-defect-zero-index-recurrent-boundary-and-open-history-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveBalancedDefectZeroIndex`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Reused, not rebuilt

`GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex` (the Lean certification of
ULF-TOEPLITZ-1) supplies the whole single-shift calibration: `shiftOp`, `backOp`, `shiftFun_add`,
`adjoint_shiftOp`, `backOp_comp_shiftOp`, `defectOp`, `defectSubmodule`, `defectMap`,
`defectMap_surjective`, `range_defectOp`, `finrank_defectSubmodule`, `range_shiftOp`,
`boundaryObserver`, `boundaryObserver_add`, `boundaryObserver_mul`.

## New infrastructure

- `ToeplitzPair = WithLp 2 (ToeplitzSpace × ToeplitzSpace)` — the doubled Hardy space with its
  `ℓ²` direct-sum inner product;
- `toeplitzPair_ext` — componentwise extensionality;
- `pairOp A B` — the block diagonal `A ⊕ B`, with `pairOp_fst`, `pairOp_snd`, `pairOp_ext`,
  `pairOp_one`, `pairOp_comp`, `pairOp_sub`;
- `adjoint_pairOp` — `(A ⊕ B)* = A* ⊕ B*`, from `WithLp.prod_inner_apply`;
- `rangePairZeroEquiv`, `rangePairZeroEquiv'` — the ranges of `0 ⊕ D` and `D ⊕ 0` are carried
  isomorphically onto `range D` by the corresponding projection;
- `ker_backOp`, `backOp_surjective`, `shiftOp_injective`, `fstLinear`, `doubledCokerMap`.

## Certified declarations, by clause

| Clause | Lean |
|---|---|
| 1: `Tₙ` Fredholm | `kerDoubledEquiv`, `cokerDoubledEquiv`, `finrank_ker_doubledShift`, `finrank_coker_doubledShift` |
| 2: `1 − T*T = 0 ⊕ Dₙ`, `1 − TT* = Dₙ ⊕ 0` | `doubledShift`, `adjoint_doubledShift`, `shiftOp_comp_backOp`, `initialDefect_eq`, `finalDefect_eq` |
| 3: both ranks `n` | `finrank_initialDefect`, `finrank_finalDefect` |
| 4: `ind Tₙ = 0` | `doubledIndex`, `doubledIndex_eq_zero` |
| 5: symbol `diag(zⁿ, z⁻ⁿ)` | `doubledSymbol` |
| 6: `det σ = 1`, class zero | `det_doubledSymbol`, `defectClass`, `defectClass_eq_zero`, `defectClass_eq_doubledIndex` |
| 7: `E(Tₙ) = 2n` | `defectEnergy`, `defectEnergy_eq` |
| 8: observer returns, energy diverges | `doubledObserver`, `doubledObserver_add`, `matrix_diagonal_one_one`, `doubledObserver_mul`, `defectEnergy_return_tendsto` |
| §3 abstract cancellation | `signedDefect`, `signedDefect_diag`, `signedDefect_diag_eq`, `unsigned_energy_of_diag`, `no_reconstruction_through_signedDefect` |
| capstone | `balanced_defect_zero_index_open_history` |

The abstract cancellation theorem is stated for an arbitrary additive commutative monoid `M`, an
arbitrary additive group `G`, and an arbitrary additive hom `φ : M →+ G`, so it is not tied to the
shift model at all; `no_reconstruction_through_signedDefect` says that **any** map applied after the
signed defect is constant on balanced pairs, which is exactly the card's "no invariant factoring
through `δ` can reconstruct positive defect energy".  It needs only `propext`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveBalancedDefectZeroIndex.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,428 jobs.  `#print axioms` on the
fifteen declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.  No
project axiom, placeholder, hypothesis interface, or computation proof is used.

## Scope, stated explicitly

As in ULF-TOEPLITZ-1, the `K₁(C(S¹))` and `K₀(𝒦)` packaging is **not** constructed — mathlib has no
C*-algebra K-theory, and the module does not build the Toeplitz extension or the six-term sequence.
What is certified is the computational content those classes evaluate: the symbol determinant is
identically `1`, and the rank-evaluated signed class `[Kₙ] − [Cₙ]` is zero and coincides with the
Fredholm index.  The Fredholm property is certified concretely — both defect spaces are exhibited as
`n`-dimensional — rather than abstractly.

## Exact field consequence

The falsification is complete and unconditional on one explicit family: index, determinant and net
winding all vanish identically, while the ordered defect pair `(Kₙ, Cₙ)` has unsigned size `2n` and
diverges along exactly the observations at which the boundary observer has returned to the identity.
Signed difference invariants cancel balanced positive defects; therefore no universal history field
built only on stable K-theory, determinant, or net winding can be complete for open-history
questions.  The survivor is the ordered pre-cancellation pair, which the module keeps as two separate
projections rather than as their difference.
