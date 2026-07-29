# Return-density type-III conjecture

- **ID:** `return-density-type-iii-conjecture`
- **Stage:** 5-failed
- **Type:** FALSIFIED; KNOWN POSITIVE SURVIVOR
- **Source:** `../1-in-progress/observer-dependent-temporal-dimension.md`
- **Statement:** If scalars plus all centred atomless-modular-spectrum
  observables form a von Neumann algebra and every nonzero centred element of
  that algebra is atomless, then the algebra is a type-III₁ factor with
  trivial state centralizer.

## Goal

Replace pointwise mixing in black-hole information-loss arguments by the
strictly weaker operational statement that fixed positive-fidelity return
sets have zero asymptotic density, while still forcing type III₁.

## Gates

- [x] 0 → 1 in-progress: proof-route-blind conjecture stated with hard
      falsifiers
- [ ] 1 → 2 fully-proven: failed by finite-dimensional counterexample
- [ ] 2 → 3 formalized: not applicable to false statement
- [ ] 3 → 4 publication-ready: retired

## Approach

The conjecture was generated before a proof route was known. After freezing
its wording, test finite/type-I modular systems, type-II systems, and
type-IIIλ factors; then compare any survivor with mixing-algebra and
ergodic-state classification theorems.

## No-go closure

- **Exact killing theorem/mechanism:** Let
  \(\mathcal M=M_2(\mathbb C)\) carry any faithful normal state. Its modular
  representation is finite dimensional, hence every nonzero modular spectral
  measure is pure point. The centred atomless class is therefore
  \(\{0\}\), and adjoining scalars gives the von Neumann algebra
  \(\mathbb C1\). Its only centred element is zero, so the universal
  atomlessness clause holds vacuously. The conclusion fails because
  \(\mathbb C1\) is not type III₁.
- **Strongest positive survivor:** If one separately assumes that the
  modular-invariant atomless algebra is nontrivial, then every non-scalar
  element of its state centralizer would centre to a nonzero fixed element
  carrying a zero-frequency atom. Hence the centralizer is trivial. The
  classical forward ergodic-state theorem then makes the algebra a type-III₁
  factor. This is a known-corollary route, not a new theorem suitable as paper
  anchor.
- **New insight:** Zero-density nonreturn is too strong when required of
  every individual centred observable: it already encodes ergodicity of the
  modular state. A genuinely new black-hole criterion must aggregate
  operational return data without excluding fixed points one observable at a
  time.
- **Status:** Truth audit closed. Marrakchi--Vaes,
  *Ergodic states on type III₁ factors and ergodic actions* (2024), states
  that trivial centralizer implies type III₁ was known since early
  Tomita--Takesaki theory and proves the converse for separable predual.
  Furuya--Lashkari--Moosa--Ouseph, *Information loss, mixing and emergent type
  III₁ factors* (2023), already derives the physical mixing-algebra
  implication. No novel dependency-closed positive survivor remains to
  formalize.

## Log

- 2026-07-28 — generated as fifth abductive jump with no proof route.
- 2026-07-28 — falsified by the scalar-output algebra in every finite
  faithful modular system; repaired nontrivial version reduced to known
  ergodic-state classification and retired.
