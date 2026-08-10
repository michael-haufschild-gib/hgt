# Source-soldering curved transport law and first-order law symbol — formalized

- **ID:** `source-soldering-transport-defect-cocycle-and-law-symbol-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `source-soldering-transport-defect-cocycle-and-law-symbol.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.SolderingTransportSymbol` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SolderingTransportSymbol.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorems 1 and 1b — the transport defect.  The category-theoretic `f_!` is absorbed into the
transport maps, exactly as the card's "canonical associators understood":

1. `bivariantDefect` — **card `(3)`**: `Q_f = T_f ∘ f_!(s_A) − s_B ∘ K_f`.
2. `transportCurvature` — **card `(5a)`**: `F^K_{g,f} = K_g ∘ g_!(K_f) − K_{gf}`.
3. `bivariantDefect_curved` — **card `(5b)`, boxed**: the exact curved Bianchi/transgression
   identity.  This is proved first, in full generality.
4. `bivariantDefect_cocycle` — **card `(4)`, boxed**: the strict cocycle law, derived from item 3
   as the flat special case `F^K = F^T = 0`.
5. `bivariantDefect_gauge` — **card `(5)`, boxed**: an additive change of soldering changes the
   defect by a coboundary.
6. `source_current_consistency` — **card `(7)`, boxed**: any source current realizing the defect
   obeys the same curved law.

The literal Route-R instance:

7. `depthMass`, `depthFreq`, `depthTheta` — **card `(5c)`**.
8. `depthTheta_01`, `depthTheta_12`, `depthTheta_02` — **card `(5d)`**: `3/4`, `1/2`, `11/8` times
   `log 2`.
9. `depthTheta_defect`, `depthTheta_defect_ne_zero` — **card `(5e)`, boxed**:
   `θ₀₁ + θ₁₂ − θ₀₂ = −(1/8) log 2 ≠ 0`.
10. `depthCurvature`, `hasDerivAt_depthCurvature`, `deriv_depthCurvature_ne_zero` — **cards
    `(5f)`, `(5g)`**: the scalar transport curvature has nonzero derivative at zero drift, so the
    strict theorem alone cannot model Route R.

Theorem 2 — the first-order law symbol, for a local `k`-algebra with a coefficient embedding:

11. `radLayer`, `headLayer` — **card `(8)`**: `S_M = mM` and `H_M = M/mM`.
12. `symbolRaw`, `symbol`, `symbol_mk` — **card `(9)`, boxed**: the multiplication symbol
    `σ_M : W ⊗_k H_M → S_M`, in the equivalent curried form `↥m → (H_M →ₗ[k] S_M)`, which avoids
    the tensor product without losing anything.
13. `symbol_eq_zero_of_mem_sq` — the symbol kills `m²`, i.e. it genuinely descends to `W = m/m²`.
14. `headMap`, `radMap`, `symbol_intertwine` — **card `(10)`, boxed**, necessity: a lift induces a
    radical-layer map intertwining the symbols.
15. `exists_lift_of_symbol_compat` — **card `(10)`**, sufficiency: conversely, such a map assembles
    an `A`-linear lift.  The proof is the card's: choose `k`-linear complements of the radical
    layers (`Submodule.exists_isCompl` over a field), define the lift by `f` on head lifts and `g`
    on the radical layer, and check `A`-linearity using `A = k ⊕ m` and `m² M = m² N = 0`.
16. `lawObstruction`, `lift_of_obstruction_eq` — **card `(11)`, boxed**: the obstruction is the
    composite symbol modulo precompositions, and its vanishing produces a lift.

## Scope

The card's "Concrete sharp model" (`A = R1 + aR^N`, `M = Ω`, `N = A^♯/A`) is an instantiation of
Theorem 2 in the concrete-model card
`congruence-order-trace-kahler-exterior-square-nonmetricity-law`, and is now formalized there:
`ConstraintRelativity/CongruenceOrderFirstOrder.lean` proves `𝔪²Ω = 0` and `𝔪²L = 0`
(`maximalIdealSq_smul_kaehler`, `maximalIdealSq_smul_traceDefect`), that the reduction
`Hom_A(Ω,L) → Hom(H_Ω,H_L)` is identically zero (`headReduction_eq_zero`), that only the zero head
map lifts (`headMap_eq_zero_of_lifts`), and that the resulting obstruction space is
`Mat_{m×m}(k)` (`solderingObstructionEquiv`).  The abstract Theorem 2 of this card is what the
concrete instance realizes; the literal identification of that instance with `lawObstruction`
additionally needs a coefficient field `k → R` (the card's `R = ℂ[[a]]`) and is not carried out.  The card states plainly that no RH conclusion follows and that
carrying arithmetic weight requires instantiating `C, K, T, s, J` from a literal source; nothing of
that kind is claimed.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/SolderingTransportSymbol.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.SolderingTransportSymbol          # green
```
