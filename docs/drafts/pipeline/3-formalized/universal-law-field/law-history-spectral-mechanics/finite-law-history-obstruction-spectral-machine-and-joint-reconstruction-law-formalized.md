# Finite law-history obstruction spectral machine — Lean certification

- **ID:** ULF-LHSM-3
- **Paper card:** `finite-law-history-obstruction-spectral-machine-and-joint-reconstruction-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveLawHistoryHigherDifferential`,
  `GaloisForLFunctions.HTGeometry.FiniteLawHistoryMachine`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

A history is a family `V : ℕ → Type` with laws `a n : V n →ₗ V (n+1)`.  The card's `V_i` is
`V i`, the card's `a_i : V_{i-1} → V_i` is `a (i-1)`, and the card's `A_{i,j}` is
`transport a i j h`.

## Certified declarations

### Interval transports (LHS.2)–(LHS.3)

`transport a i j (h : i ≤ j) : V i →ₗ[k] V j` is defined by recursion on the upper endpoint, so
that the right extension is definitional.  Certified:

* `transport_self` — `A_{i,i} = id`;
* `transport_step` — `A_{i,j+1} = a_j ∘ A_{i,j}`;
* `transport_one` — `A_{i,i+1} = a_i`;
* `transport_left` — `A_{i,j} = A_{i+1,j} ∘ a_i`, the left extension;
* `transport_comp` — **strict interval composition** `A_{j,l} ∘ A_{i,j} = A_{i,l}`.

### Page subquotients (LHS.4)–(LHS.6)

`pageKernel a s n h = ker aₙ ⊓ range A_{s,n}` and
`pageCokerSubmodule a m t h = range aₘ ⊔ ker A_{m+1,t}`, with `pageKernel_eq`,
`pageCokerSubmodule_eq` giving the explicit lattice form.  Page one is
`pageKernel_self` (`K = ker aₙ`) and `pageCokerSubmodule_self` (`C = coker aₘ`).

### The higher differential (LHS.7), Theorem 4.1

`pageDifferential a m n h : pageKernel a (m+1) n h →ₗ V (m+1) ⧸ pageCokerSubmodule a m n h`.
It is the interval-form `higherLawHistoryDifferential` of the companion module, built as

```text
K → range P  --(quotKerEquivRange)⁻¹-->  V(m+1)/ker P  -->  V(m+1)/(range aₘ + ker P)
```

so no section of `P` is selected — exactly the card's proof of Theorem 4.1.

### Exact page derivation (LHS.10)–(LHS.12)

* `nextHigherKernelSource_eq_pageKernel` — the machine's next kernel source is
  `pageKernel a m n`, using `transport_left`;
* `secondaryCarrierSubmodule_eq_pageCokerSubmodule` — the machine's next cokernel denominator is
  `pageCokerSubmodule a m (n+1)`, using `transport_step`;
* `ker_pageDifferential` — `(LHS.10)`: the kernel is the next kernel survivor;
* `cokerPageDifferentialEquiv` — `(LHS.11)`: the cokernel is the next cokernel survivor.

Together these are `(LHS.12)`, "next page = (ker, coker) of the current transgression"; the
packaging identity `(LHS.13)` `d_r² = 0` holds because the differential lands in the cokernel row,
on which it is defined to be zero, so it carries no separate content.

### Three-law fusion (LHS.22)–(LHS.23)

`ker_higherLawHistoryDifferential` is the general kernel description; `ker_pageTwoDifferential`
is `(LHS.22)`, `ker d₁⁽²⁾ = ker h ⊓ range (g ∘ f)`, and `pageTwoCokerEquiv` is `(LHS.23)`,
`coker d₁⁽²⁾ ≃ Y / (range f + ker (h ∘ g))`.

### Stable kernel reconstruction (LHS.15)–(LHS.17)

`totalTransport a m = A_{0,m}`, `totalKernelFiltration a j = ker A_{0,j}` with
`totalKernelFiltration_zero` and `totalKernelFiltration_mono`;
`map_totalTransport_totalKernelFiltration` computes the image of the filtration step, and
`kernelGradedEquiv` is `(LHS.17)`:

```text
ker A_{0,j+1} / ker A_{0,j}  ≃  ker a_j ⊓ range A_{0,j}
```

### Stable cokernel reconstruction (LHS.18)–(LHS.20)

`totalCokernel a m = V m ⧸ range A_{0,m}`,
`totalCokerFiltration a m i h = π (range A_{i,m})`, with `totalCokerFiltration_zero`,
`totalCokerFiltration_top`, `totalCokerFiltration_mono` and the auxiliary
`range_totalTransport_le`.  `cokerGradedMap`, `range_cokerGradedMap` and `ker_cokerGradedMap`
compute the graded piece; `cokerGradedEquiv` and `cokerGradedSubquotientEquiv` are `(LHS.20)`:

```text
F_i / F_{i-1}  ≃  V_i / (range a_i + ker A_{i,m})
```

`subquotientEquivMapMkQ` is the reusable identification of a subquotient with an image in a
quotient.

### Finite index conservation (LHS.24) and (LHS.21)

* `finiteLawIndex_totalTransport` — `ind A_{0,m} = Σ_{j<m} ind a_j`, i.e. `χ(E₁) = ind A_{0,m}`;
* `pagewise_index_conservation` — `dim ker d − dim coker d = dim K − dim C` for every page
  differential, so `χ(E_{r+1}) = χ(E_r)` slotwise;
* `sum_finrank_pageKernel` — `Σ_j dim K_j^{(j)} = dim ker A_{0,m}`;
* `stableCokerRank`, `stableCokerRank_of_le`, `finrank_totalCokerFiltration`,
  `sum_stableCokerRank` — `Σ_i dim C_i^{(m-i+1)} = dim coker A_{0,m}`;
* `stable_page_index_eq` — the stable-page signed sum equals `Σ_j ind a_j`.

The last three are the dimension content of `(LHS.21)`; the associated-graded content itself is
`kernelGradedEquiv` and `cokerGradedEquiv`, and no splitting is asserted, matching hostile
boundary 4 of the card.

### Composite rigidity (LHS.25)

`pageKernel_mono`, `totalKernelFiltration_eq_bot_iff`, `totalCokerFiltration_eq_bot_iff` and

```text
totalTransport_bijective_iff :
  Function.Bijective (A_{0,m})
    ↔ (∀ j < m, pageKernel a 0 j = ⊥) ∧ (∀ m' (h : m'+1 ≤ m), pageCokerSubmodule a m' m = ⊤)
```

This is proved without any finite-dimensionality hypothesis.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveLawHistoryHigherDifferential.lean
lake env lean GaloisForLFunctions/HTGeometry/FiniteLawHistoryMachine.lean
```

Both elaborate with no errors and no warnings.  `#print axioms` on all 50 public declarations of
`FiniteLawHistoryMachine` and on the declarations of the higher-differential module reports only
`propext`, `Classical.choice`, `Quot.sound`.  Both modules are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`, which is imported by
`GaloisForLFunctions.HTGeometry`.

## Card Lean requirements (§16)

1. interval transports and strict composition — `transport`, `transport_comp`;
2. page kernel and cokernel subquotients — `pageKernel`, `pageCokerSubmodule`, page-one lemmas;
3. well-defined `d_i^{(r)}` without a selected section — `pageDifferential`;
4. `(LHS.10)` — `ker_pageDifferential`;
5. `(LHS.11)` — `cokerPageDifferentialEquiv`;
6. `(LHS.22)`–`(LHS.23)` — `ker_pageTwoDifferential`, `pageTwoCokerEquiv`;
7. `(LHS.17)` and `(LHS.20)` — `kernelGradedEquiv`, `cokerGradedSubquotientEquiv`;
8. `(LHS.24)` — `pagewise_index_conservation`, `finiteLawIndex_totalTransport`,
   `stable_page_index_eq`;
9. `(LHS.25)` — `totalTransport_bijective_iff`.

## Still open (not a proved theorem)

Hostile boundary 1: no literal arithmetic history with vanishing stable page is constructed.  The
card states this as the remaining RH construction burden, not as a theorem.
