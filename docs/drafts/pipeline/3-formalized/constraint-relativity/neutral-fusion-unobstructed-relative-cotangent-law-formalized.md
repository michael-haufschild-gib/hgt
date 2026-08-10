# Neutral fusion and unobstructed relative cotangent law — formalized

- **ID:** `neutral-fusion-unobstructed-relative-cotangent-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `neutral-fusion-unobstructed-relative-cotangent-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.NeutralFusionCotangent` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/NeutralFusionCotangent.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

The card's Lean-return note said formal work "would require differential polynomial algebra
infrastructure".  It already exists in the corpus and was **not** rebuilt:

- `GaloisForLFunctions.differentialAdjoin`, `differentialJet`, `DifferentialIndependent`,
  `derivationClosed_differentialAdjoin` (`HTGeometry.DifferentialIndependence`);
- `differentialIndependentAdjoinParametrization` — the canonical rational jet-field
  parametrization (`HTGeometry.DifferentialIndependentFieldUniversality`), which *is* card `(3)`;
- `adjoinLift`, `differentialIndependent_subfield`, `differentialAdjoin_adjoinLift_eq_top`
  (`HTGeometry.DifferentialSubfieldTransfer`) and
  `differentialTranscendenceDegree_eq_cardinalMk_of_differentialIndependent_of_adjoin_eq_top`.

From mathlib: `KaehlerDifferential.mvPolynomialBasis`, `KaehlerDifferential.isLocalizedModule_map`,
`Algebra.FormallySmooth.of_isLocalization`, `Algebra.FormallySmooth.of_equiv`.

## New infrastructure

Mathlib has the polynomial Kähler basis and the localization base change, but **no transport of
Kähler differentials along an algebra isomorphism**.  Built here:

- `algebraOfAlgEquiv` — the `S`-algebra structure on `T` carried by `e : S ≃ₐ[R] T`;
- `kaehlerBasisOfAlgEquiv` — a basis of `Ω[S⁄R]` over `S` gives a basis of `Ω[T⁄R]` over `T`,
  proved by observing that an isomorphism is formally étale and invoking
  `KaehlerDifferential.isBaseChange_of_formallyEtale`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `jetPolynomial C ι = MvPolynomial (ι × ℕ) C` — the differential polynomial algebra
   `K_n{X_z} = K_n[∂^j X_z]` of the card's proof.
2. `fusionJetParametrization` — **card `(3)`**: `L = Frac K_n[∂^j x_z]`, as an explicit
   `C`-algebra isomorphism `FractionRing (jetPolynomial C ι) ≃ₐ[C] differentialAdjoin C (range x)`.
3. `formallySmooth_fractionRing_jetPolynomial`, `formallySmooth_fusionField` — the extension is
   formally smooth: a polynomial algebra followed by a localization.
4. `subsingleton_h1Cotangent_fusionField` — **card `(4)`**: `H₁(𝕃_{L/K_n}) = 0`.  This is the
   positive-degree vanishing the card asserts, in the form mathlib's cotangent API supports.
5. `jetFieldKaehlerBasis` — the Kähler basis of the jet field, from the polynomial basis and the
   localization base change.
6. `fusionKaehlerBasis` — **card `(5)`**: `Ω_{L/K_n} = ⨁_{z,j} L d(∂^j x_z)`, an explicit basis
   indexed by `ι × ℕ`.
7. `free_kaehler_fusionField`, `rank_kaehler_fusionField` — the relative Kähler module is free of
   rank `#(ι × ℕ)`.
8. `differentialTranscendenceDegree_fusionField` — **card `(6)`**: `dtrdeg_{K_n} L = m`, so the
   extension is genuinely creative while carrying no positive-degree obstruction.
9. `jet_shift_injective` — the jet tower over each generator is infinite: the induced derivation
   `∂_Ω d(∂^j x_z) = d(∂^{j+1} x_z)` moves each basis vector one step up, so `(dx_z)` generate
   freely as a differential module of differential rank `m`.

10. `creation_without_obstruction` — the card's named **Consequence**: the two conclusions hold
    simultaneously, so a genuinely creative extension (differential transcendence degree the size
    of the fused family) coexists with a vanishing positive-degree cotangent obstruction.  This is
    the card's refutation of "obstruction ≃ successor law" when *obstruction* means a
    relation/anomaly class, stated as one checkable proposition rather than left as a reading of
    items 4 and 8.

## Scope

The card's items 1 and 2 of the "Setup" (`V_n(b_z) ⋆ V_0(1) = V_{n+1}(b_z)` and the differential
algebraic independence of the fused tuple) are the *inputs* supplied by the publication-ready
finite-fusion theorem; the theorem of this card takes differential independence as its hypothesis,
and so does the formalization — `DifferentialIndependent C x` is the card's item 2, verbatim.  The
"Consequence" and "Hostile audit" sections are commentary.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/NeutralFusionCotangent.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.NeutralFusionCotangent          # green
```
