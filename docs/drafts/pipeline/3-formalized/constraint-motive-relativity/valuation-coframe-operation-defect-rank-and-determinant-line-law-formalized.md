# Valuation-coframe operation-defect rank and determinant-line law — Lean certificate

- **ID:** `cmr-valuation-coframe-operation-defect-rank-determinant-line-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `valuation-coframe-operation-defect-rank-and-determinant-line-law.md`
  (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CoframeAnomalyRank.lean`,
imported by the area umbrella `GaloisForLFunctions.HTGeometry`.
Namespace: `HTGeometry.ConstraintMotiveRelativity`.

## Formal statement chain

1. `coframeAnomaly T φ φhat` — `(VOD.3)`, the anomaly `x ↦ (ℓ ↦ φ̂_ℓ (T x) - φ_ℓ x)` as a linear
   map `C →ₗ[k] (F → k)`, with `coframeAnomaly_apply`.
2. **`coframeAnomaly_eq_zero_of_boundary`** — well-definedness on homology: if the source coframes
   kill the source boundaries, the chain map sends boundaries to boundaries, and the target
   coframes kill the target boundaries, then the anomaly kills boundaries.
3. `CoframeNormalized u φ` — `(VOD.2)`, `φ_ℓ (u_p) = -δ_{ℓ p}`; `coframeNormalized_sum` evaluates
   the coframes on a combination.
4. **`coframe_independent`** — Theorem 3.1 (1): a combination of the marked cycles lying in the
   boundaries has zero coefficients, i.e. the classes are independent in homology.
   `coframe_linearIndependent` is the corresponding `LinearIndependent k u`.
5. **`coframeAnomaly_marked`** — Theorem 3.1 (2), `(VOD.4)`: exactification turns the anomaly of
   `u_p` into the dual basis vector `e_p`.
6. **`coframeAnomaly_surjective_on_span`** — Theorem 3.1 (3): the anomaly maps the span of the
   marked cycles onto `k^F`, so its rank is `|F|`.
7. **`card_le_of_factorization`** — Theorem 3.1 (4): a factorization of the anomaly on that span
   through a finite-dimensional `P` forces `|F| ≤ finrank P`.
8. **`no_scalar_factorization`** — Corollary 3.2: for `2 ≤ |F|` no factorization through a single
   scalar line exists.
9. **`coframeAnomaly_eq_zero_of_preserved`** and **`transported_independent`** — Theorem 4.1:
   coframe preservation forces `A_T = 0` and keeps the marked span injective under `T`.
10. **`coframeAnomaly_comp`** — Theorem 4.2, `(VOD.5)`: `A_{S∘T} = A_T + A_S ∘ T`.
11. `coframeAnomalyMatrix`, **`coframeAnomalyMatrix_eq_id`**, **`det_coframeAnomalyMatrix`**
    (`= 1`) and **`exteriorPower_coframeAnomalyMatrix`** — Theorem 5.1, `(VOD.6)`: read in the
    matched ordered bases the anomaly is the identity, its determinant is `1`, and its top
    exterior power is the identity of the determinant line, in particular an isomorphism.
12. `traceDerCochain`, **`traceDerCochain_antisymm`**, `derDefect`,
    **`traceDerCochain_defect`** — `(VOD.7)`–`(VOD.9)` and Proposition 6.1: the trace-derivation
    cochain is antisymmetric when the trace kills the derivation, and the coframe defect of a
    trace-preserving algebra map is the trace pairing against its derivation-transport defect.
13. `arakelovL`, `arakelovB`, `arakelovTr`, `arakelovTr_comp_arakelovB`,
    **`arakelov_ker_eq_range`** (`(VOD.10b)` exactness), `arakelov_fst_comp_arakelovB` (split
    injectivity), `arakelovTr_comp_section` (split surjectivity) and
    **`arakelov_coframeAnomaly_eq_zero`** — §7, `(VOD.10)`–`(VOD.11)`: the prime–infinity graph is
    a split extension carrying no coframe anomaly.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CoframeAnomalyRank.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CoframeAnomalyRank
```

Green with no warnings.  `#print axioms` on all nineteen declarations listed above reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The Lean development keeps the card's degree-`n` data in the elementary form the proofs actually
use: a source module with a submodule of boundaries, a target module with a submodule of
boundaries, closed cochains (linear functionals annihilating the boundaries), and a linear map
carrying boundaries to boundaries.  All homological statements of the card are then literal, and
`coframeAnomaly_eq_zero_of_boundary` is exactly the well-definedness argument of `(VOD.3)`.

§8 of the paper card instantiates Theorems 3.1–5.1 at `n = 0` on the Hochschild presentation
complex, using the arithmetic parent's `φ_ℓ([u_p]) = -δ_{ℓ p}`.  Its three conclusions are direct
applications of `coframeAnomaly_eq_zero_of_preserved`/`transported_independent`,
`coframeAnomaly_surjective_on_span` and `no_scalar_factorization`; the parent card supplies the
normalization hypothesis, which is exactly `CoframeNormalized`.
