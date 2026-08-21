# Local law-history transgression, seven-term exactness, composite rigidity — Lean certification

- **ID:** ULF-LHSM-2
- **Paper card:** `local-law-history-transgression-seven-term-exactness-and-composite-rigidity-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveLawHistoryDifferential`,
  `GaloisForLFunctions.HTGeometry.LawHistoryTransgressionPages`
- **Supporting:** `GaloisForLFunctions.HTGeometry.ConstitutiveCarrierComposition`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveLawHistorySpectralMechanics`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## Certified declarations

### The five maps (LHT.2)–(LHT.3)

| Card | Lean |
|---|---|
| `∂_{f,g} : ker g → coker f` | `lawHistoryDifferential` |
| `i : K_f → K_{gf}` | `kernelToCompositeKernel` |
| `a : K_{gf} → K_g` | `compositeKernelToLaterKernel` |
| `b : C_f → C_{gf}` | `earlierCokerToCompositeCoker` |
| `c : C_{gf} → C_g` | `compositeToOuter` |

Well-definedness of `b` is `range_f_le_ker_earlierCokerToCompositeRaw`; well-definedness of `c` is
`compositeRange_le_outerRange`.

### Theorem 2.1 — seven-term exactness (LHT.4)

`lawHistory_sevenTerm_exact` bundles all six conditions:
`kernelToCompositeKernel_injective`, `range_kernelToCompositeKernel_eq_ker`,
`range_compositeKernelToLaterKernel_eq_ker`, `range_lawHistoryDifferential_eq_ker`,
`range_earlierCokerToCompositeCoker_eq_ker`, `compositeToOuter_surjective`.

### Theorem 3.1 — two-page reconstruction (LHT.5)–(LHT.7)

New in `LawHistoryTransgressionPages`:

* `kernelPageEquiv` is `(LHT.5)`: `ker (g ∘ f) / ker f ≃ ker ∂`, obtained from
  `range i = ker a` and the first isomorphism theorem for `a`, then transported along
  `range a = ker ∂`.  `kerEquivRangeKernelToCompositeKernel` identifies the divisor with `ker f`.
* `range_lawHistoryDifferential_eq_map` computes `ran ∂ = mkQ (ran f + ker g)`, and
  `cokernelPageEquiv` is `(LHT.6)`: `coker ∂ ≃ Y / (ran f + ker g)`, by the third isomorphism
  theorem `Submodule.quotientQuotientEquivQuotient`.
* `cokernelPageEquivKerOuter` is `(LHT.7)`: `coker ∂ ≃ ker c`, from `ran ∂ = ker b` and the first
  isomorphism theorem for `b`.
* `secondaryBirthEquivKerOuter` composes the last two: the secondary birth space of ULF-PSB-1 is
  literally the kernel of the outer cokernel comparison.

### Theorem 4.1 and Corollary 4.2 — composite rigidity (LHT.8)–(LHT.9)

`lawHistoryDifferential_bijective_of_comp` and `comp_bijective_of_lawHistoryDifferential` are the
two directions; `comp_bijective_iff_boundary_and_transgression` is `(LHT.8)`.
`lawHistoryDifferential_eq_splitKernelToCokernel` and `splitLawHistoryDifferentialEquiv` (with
`splitLawHistoryDifferentialEquiv_apply`) are `(LHT.9)`: in a split history the general
differential is the inverse of the split transgression of ULF-LHSM-1.

### Section 5 — finite-dimensional conservation (LHT.10)–(LHT.13)

* `lawHistory_alternating_sum_eq_zero` is `(LHT.10)`, the vanishing Euler characteristic of the
  six-term sequence, reduced to three instances of `finiteLawIndex_eq_finrank_sub`;
* `finiteLawIndex` and `finiteLawIndex_comp` are `(LHT.11)`, index additivity;
* `finrank_ker_comp_eq` is `(LHT.12)`, from `kernelPageEquiv` and
  `Submodule.finrank_quotient_add_finrank`;
* `finrank_quotient_range_comp_eq` is `(LHT.13)`, from `cokernelPageEquivKerOuter` and
  rank–nullity for the surjection `c`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveLawHistoryDifferential.lean
lake env lean GaloisForLFunctions/HTGeometry/LawHistoryTransgressionPages.lean
```

Both elaborate with no errors and no warnings.  `#print axioms` on the 16 declarations of the
first module and on all nine of the second (`kernelPageEquiv`,
`kerEquivRangeKernelToCompositeKernel`, `range_lawHistoryDifferential_eq_map`,
`cokernelPageEquiv`, `cokernelPageEquivKerOuter`, `secondaryBirthEquivKerOuter`,
`lawHistory_alternating_sum_eq_zero`, `finrank_ker_comp_eq`, `finrank_quotient_range_comp_eq`)
reports only `propext`, `Classical.choice`, `Quot.sound`.  Both modules are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`, which is imported by
`GaloisForLFunctions.HTGeometry`.

## Card Lean boundary (§8)

1. all five maps of `(LHT.3)` — table above;
2. left injectivity and right surjectivity — `kernelToCompositeKernel_injective`,
   `compositeToOuter_surjective`;
3. all four range–kernel equalities of `(LHT.4)` — `lawHistory_sevenTerm_exact`;
4. composite-bijectivity classification `(LHT.8)` —
   `comp_bijective_iff_boundary_and_transgression`;
5. split transgression `(LHT.9)` — `splitLawHistoryDifferentialEquiv`;
6. finite-dimensional conservation `(LHT.10)`–`(LHT.13)` — all four now proved, with no imports
   beyond the finrank lemmas already used by the differential module.

## Still open (not a proved theorem)

Hostile boundary 5 of the card: constructing the literal arithmetic law history whose
source-generated transgression pairs the complete later-erasure sector with the complete
earlier-nonattainment sector.  The card states this as a construction burden for a future RH
selector, not as a theorem of this card.
