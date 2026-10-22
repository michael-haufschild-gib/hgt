# The localization blindness law

**Status:** core Lean-closed (axiom-clean). Diagnosis complete; producer named, not built.
**Modules:** `RHTower/DivisorSliceFixedPart.lean`, `RHTower/DivisorSliceFreePart.lean`.
**Ledger:** CANNOT-407, MUST-408, MUST-409.

## The law

For a `ℤ/2`-set the Borel equivariant cohomology is

| orbit | `H*_{ℤ/2}` | `u`-torsion? |
|---|---|---|
| fixed point | `𝔽₂[u]` | no |
| free orbit | `𝔽₂` | **yes** |

So the free orbits are exactly the `u`-torsion, and inverting `u` annihilates them. That inversion
is the Atiyah–Segal–Quillen localization theorem, and it is what produces **every** invariant the
ledger has ever used for the reflection:

Tate cohomology · Smith theory · signature · Fredholm index · Toeplitz index · Krein inertia ·
Witt class · Hasse–Witt · spectral flow · Maslov index · rapidity · escape multiplicity.

**Every one of them computes the fixed part and nothing else** — and by `CANNOT-405` the fixed part
of a slice is a subsingleton, unconditionally. Hence:

> The corpus's universal blindness has a single named cause: **every route localizes.**

This subsumes and explains the earlier diagnoses. `CANNOT-399` said reflection-even real readers are
blind because `Hom(ℤ/2, ℝ) = 0`; that is the same phenomenon one level down — `ℝ` has no `2`-torsion,
and the localized theories have no `u`-torsion.

## The free part, made concrete (MUST-408)

The reflection sends `Re` to `1 − Re`, so each slice splits:

```
xiSlice_eq_union      : xiSlice t = xiSliceLeft t ∪ xiSliceFixed t ∪ xiSliceRight t
xiSliceRight_eq_image : xiSliceRight t = supportPartner '' (xiSliceLeft t)
```

subsingleton fixed part, free part with its two halves exchanged by the reflection. Therefore

```
riemannHypothesis_iff_xiSliceLeft_empty :
  RiemannHypothesis ↔ ∀ t : ℝ, xiSliceLeft t = ∅
```

**RH is the emptiness of every left half-slice.** That is the `u`-torsion, as a *set*. Failure is a
single divisor point strictly left of the critical line.

## The producer that is named but not built

RH ⟺ the action is **equivariantly formal** (`H*_G` free over `𝔽₂[u]`, i.e. no `u`-torsion). The
classical machines that *prove* equivariant formality are not localizations and so are not excluded:

- a **perfect Morse–Bott function** whose critical set is the fixed locus;
- **Kirwan's theorem** — a Hamiltonian action on a compact symplectic manifold is equivariantly
  formal, proved via the norm-square of the **moment map**;
- Hodge-theoretic degeneration arguments.

Corpus search confirms *equivariant formality*, *Borel construction*, *Kirwan* are **absent**; the
corpus's "moment map" occurrences are the power-sum moment map of secant geometry, unrelated.

## Falsifiers

1. **Degenerate carrier.** A slice is a finite set; a Morse–Bott argument needs a space. If no
   natural space with this `ℤ/2`-action exists, the named producers do not apply and the law is a
   diagnosis only.
2. **Proves too much.** Any construction using only the functional equation is killed by CANNOT-01.
3. **Circular formality.** "Assume equivariantly formal" is RH; the formality must be *derived* from
   a Morse function or moment map built pre-divisor.
4. **MUST-409.** Before developing any of the named producers, compute what it outputs here. That is
   the rule this cycle's retirement produced.
