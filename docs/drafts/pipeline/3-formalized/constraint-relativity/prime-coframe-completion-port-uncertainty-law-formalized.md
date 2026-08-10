# Prime-coframe completion-port uncertainty law — formalized

- **ID:** `prime-coframe-completion-port-uncertainty-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `prime-coframe-completion-port-uncertainty-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.CoframePortUncertainty` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/CoframePortUncertainty.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Setup and the algebraic port:

1. `augmentation`, `augmentation_single`, `meanZero` — **card `(1)`**: `V = c₀₀(I)` as `I →₀ ℂ`,
   `ε₀` the total charge, `A_∞ = ker ε₀`.
2. `augmentation_surjective`, `portEquiv` — **card `(14)`**: `V / A_∞ ≅ ℂ`.

Theorem 1, the exact one-port dichotomy, for an arbitrary Hausdorff locally convex `X` with a dense
linear realization `j` — the card's setup `(2)` verbatim:

3. `closedCoframe`, `map_meanZero_le_closedCoframe` — the closure `Ā` of the realized coframe.
4. `closedCoframe_le_ker`, `ker_le_closedCoframe`, `closedCoframe_eq_ker` — **card `(3)`**:
   with a continuous augmentation, `Ā = ker ε`.  The hard inclusion is proved without nets, by
   observing that `y ↦ y − ε(y)·j(u)` is continuous, fixes `ker ε`, and carries `range j` into
   `j(A_∞)`.
5. `portQuotientEquiv` — **card `(3)`**: `X/Ā ≅ ℂ`.
6. `exists_continuous_augmentation` — **card `(4)`**, the converse: if `Ā` is proper, Hahn–Banach
   separation (`RCLike.geometric_hahn_banach_closed_point`) produces a nonzero continuous
   functional annihilating `Ā`, and comparing kernels on the dense subspace rescales it to a
   continuous extension of `ε₀`.
7. `one_port_dichotomy` — the two alternatives, exhaustively.

Theorem 3, the raw radial drift:

8. `radialVector`, `augmentation_radialVector` — **cards `(10)`, `(11)`**.
9. `not_bddAbove_partialSums` — **card `(9)`**: a weight family bounded below by a positive
   constant on an infinite index set has unbounded partial charge.
10. `log_prime_ge`, `log_two_pos` — **card `(12)`**: `w_p = log p ≥ log 2 > 0`.
11. `radial_coefficient_ge`, `radial_coefficient_pos` — **card `(13)`**: for every real `a ≠ 0`,
    `|1 − p^{2a}| ≥ |1 − 2^{2a}| > 0`, proved by splitting on the sign of `a`.
12. `no_convergent_radial_net` — **Theorem 3**: no Hausdorff locally convex dense realization both
    retains the port and carries a convergent net of raw radial vectors.

Theorem 2, the Banach phase transition:

13. `lpSingleLM`, `jLp`, `jLp_single`, `coeFn_jLp` — the canonical realization `c₀₀(I) → ℓ^p(I)`.
14. `norm_block` — the norm of a uniform finite block: `‖∑_{k ∈ s} e_k‖_p = (card s)^{1/p}`.
15. `uniformWitness`, `uniformWitness_mem_meanZero` — **card `(7)`**: `a_N = e_i − N⁻¹ ∑ e_{i_k}`
    lies in `A_∞`.
16. `norm_basis_sub_witness` — **card `(8)`**: `‖a_N − e_i‖_p = N^{1/p − 1}`.
17. `basis_mem_closedCoframe` — **card `(15)`**: for `p > 1` every basis vector lies in the closure
    of the realized mean-zero coframe, so the algebraic port has zero quotient seminorm.
18. `closedCoframe_lp_eq_top` — **card `(6)`**: hence `ℓ^p / Ā = 0` for `p > 1`.
19. `summable_lp_one`, `norm_tsum_le_norm_lp_one`, `ellOneAugmentation`,
    `ellOneAugmentation_jLp` — **card `(5)`**: on `ℓ¹` the augmentation *is* continuous, so by
    item 5 the port is `ℂ`.

## Scope

The `c₀` half of card `(6)` is the same computation with the sup norm and is not separately
formalized; the `ℓ^p`, `p > 1` case above already exhibits the phase transition against `ℓ¹`, which
is the content of Theorem 2.  The "Strongest positive survivor" and "Corpus consequence" sections
are commentary listing what a successful construction would have to use; nothing there is a
theorem.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CoframePortUncertainty.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.CoframePortUncertainty          # green
```
