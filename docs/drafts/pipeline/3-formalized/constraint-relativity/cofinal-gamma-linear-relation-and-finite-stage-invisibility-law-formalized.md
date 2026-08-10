# Cofinal Gamma linear relation and finite-stage invisibility law — formalized

- **ID:** `cofinal-gamma-linear-relation-and-finite-stage-invisibility-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `cofinal-gamma-linear-relation-and-finite-stage-invisibility-law.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.CofinalGammaRelation` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/CofinalGammaRelation.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Setup:

1. `PrimeSeq`, `summableSubspace`, `GammaTarget` — **card `(CGR.1)`**: `S = ℂ^𝒫`, `I = ℓ¹(𝒫)` as a
   *subspace* (not an ideal, as the card's hostile audit insists), `V = S/I`.
2. `radialMul`, `radialMul_apply`, `norm_radialMul` — **card `(CGR.2)`**: `(C_t a)_p = p^{-2t} a_p`.
3. `gammaRel`, `mem_gammaRel_iff` — **card `(CGR.3)`**: the canonical quotient relation, as a
   submodule of `V × V`.  No ideal-preservation premise is used, exactly as the card states.

Lemma A and the trichotomy:

4. `gammaRel_singleValued_iff` — **Lemma A**: the relation is single-valued iff `C(I) ⊆ I`.
5. `radialMul_mapsTo_iff` — **Lemma B, `(CGR.5)`**: `C_t(I) ⊆ I ↔ t ≥ 0`.  The `t < 0` half is the
   card's witness, in a form needing no enumeration of the primes: `b_p = p^{-2u}·p^{-1}` is
   summable because `∑ p^{-(1+2u)}` converges, while `C_t b_p = 1/p` is not, by
   `Nat.Primes.not_summable_one_div`.
6. `gammaRel_forward_iff`, `gammaRel_inverse_iff`, `gammaRel_both_iff`, `gammaRel_zero` —
   **Theorem C.1–C.4**: forward exactly on `t ≥ 0`, inverse exactly on `t ≤ 0`, both exactly at
   `t = 0`, and `Γ₀ = Δ_V`.

Finite-stage invisibility:

7. `finiteRadialMul` — **card `(CGR.7)`**.
8. `gammaRel_finite` — **Theorem D, `(CGR.8)` boxed**: `Γ_{t,K} = Δ_V` for every finite `K` and
   every real `t`, because the truncation defect has finite support and so is summable.

Source coinvariants:

9. `sourceCoinvariants` — **card `(CGR.9)`**.
10. `intertwiner_iff_vanishes`, `exists_factor_iff` — **Corollary E**: a map intertwines the source
    generators with the diagonal target relation exactly when it kills every generator defect,
    equivalently exactly when it factors through the coinvariants.

Kernel/multivalued defect exchange:

10b. `surjective_eval_iff_ne_zero` — **Corollary E, second half**: evaluation of coinvariant
    observers at a class, `P ↦ P([η])`, is surjective onto a nonzero target exactly when `[η] ≠ 0`.
    So prescribing `P([η]) = v` for every `v` needs the retained class to survive, which the card
    flags as a separate source-survival statement rather than a consequence of diagonality.

11. `mulPart`, `kerPart`, `mem_mulPart_iff`, `mem_kerPart_iff` — **card `(CGR.10)`**.
12. `mulPart_eq_bot_iff`, `kerPart_eq_bot_iff` — **card `(CGR.11)`**: the multivalued defect
    vanishes exactly on `t ≥ 0`, the kernel defect exactly on `t ≤ 0`.
13. `defectExchange` — **card `(CGR.12)`**: the canonical isomorphism
    `V/ker Γ_t ≅ V/mul Γ_t`, the precise conservation law of the card.

## Scope

The card's §6–§8 are consequences and audit: they say what a multiplicity-one theorem would have to
do, and that no RH consequence follows without a source-defined constitutive intertwiner.  Nothing
there is a theorem.  The two open gates the card lists (external priority verification,
relation-level cofinal equalizer) are unaffected by the formalization and remain open.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CofinalGammaRelation.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.CofinalGammaRelation          # green
```
