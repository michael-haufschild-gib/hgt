# ULF-RITM-2 — Lean formalization record

**Card:** `finite-split-recovery-index-reconstruction-renyi-conservation-and-cofinal-no-go.md`
**Module:** `formal/GaloisForLFunctions/HTGeometry/SplitRecoveryIndexTower.lean`
**Namespace:** `GaloisForLFunctions.HTGeometry`
**Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Card result → Lean declaration

| Card | Lean |
|---|---|
| the recovery kernel, (RIT.1) | `SplitRecovery` (fields `kernel`, `pos`, `row`) |
| `E_κ`, (RIT.4) | `SplitRecovery.expect` (unital, positive, faithful: `expect_one`, `expect_nonneg`, `eq_zero_of_expect_eq_zero`) |
| `u_h`, (RIT.5) | `SplitRecovery.qbasis` |
| **Theorem 2.1**, (RIT.6) | `SplitRecovery.quasiBasis` |
| **(RIT.7)** | `SplitRecovery.index`, `SplitRecovery.index_eq` |
| **(RIT.8)** | `SplitRecovery.kernel_eq_index_inv` |
| **(RIT.9)** | `SplitRecovery.exists_index_eq` |
| `K_κ`, (RIT.10) | `SplitRecovery.pimsnerPopa` |
| **Theorem 3.1**, (RIT.11) | `SplitRecovery.pimsnerPopa_least` |
| **(RIT.12)** and its equality case | `SplitRecovery.card_le_pimsnerPopa`, `SplitRecovery.pimsnerPopa_eq_card_iff` |
| `H_α`, (RIT.14) | corpus `finiteRenyiEntropy` |
| `D_α`, (RIT.15) | `finiteRenyiDiv` |
| **Theorem 4.1**, (RIT.16) | `finiteRenyiEntropy_eq_index_moment` |
| **(RIT.17)** | `finiteRenyiDiv_add_finiteRenyiEntropy` |
| **(RIT.18)** | `shannon_index_conservation` |
| `κ^{(n)}`, (RIT.19) | `SplitRecovery.depth` |
| **(RIT.20)** | `SplitRecovery.depth_index` |
| **(RIT.21)** | `SplitRecovery.pimsnerPopa_depth` |
| `P_{μ,n}`, `U_{μ,n}`, (RIT.22) | `SplitRecovery.formedPacket`, `uniformPacket` |
| **Theorem 5.1**, (RIT.23) | `SplitRecovery.formation_equation_of_state` |
| **(RIT.25)** | `SplitRecovery.finiteKL_formedPacket_uniformPacket`, `SplitRecovery.sum_formedPacket_mul_log_index` |
| **§6**, (RIT.26) | `SplitRecovery.finiteKL_formedPacket` |
| **Theorem 8.1**, (RIT.28) | `SplitRecovery.bddAbove_pimsnerPopa_depth_iff` |
| **(RIT.29)** | `SplitRecovery.card_pow_le_pimsnerPopa_depth` |

## Method notes

* The whole card is finite and commutative, so the quasi-basis identity, the index profile and the
  Pimsner--Popa constant are proved by direct `Finset` computation; no operator-algebra
  infrastructure is needed.
* The tensor law `(RIT.21)` is an exact `sup'` identity: the upper bound is factorwise and the
  lower bound is realized by repeating a maximizing latent letter, extracted with
  `Finset.exists_mem_eq_sup'`.
* `(RIT.23)`/`(RIT.25)`/`(RIT.26)` rest on two combinatorial lemmas proved here:
  `sum_prod_eq_one` and `sum_prod_mul_sum` (the exact first-order expansion of an iterated product
  weight), both from `Fintype.prod_sum`.
* `(RIT.26)` needs no positivity of the second observer law: the shared latent factor cancels in
  the likelihood ratio, and vanishing weights contribute zero on both sides.

## Verification

* `lake env lean` on the module: 0 errors, 0 warnings.
* Axiom audit: 31 public declarations, only `propext`, `Classical.choice`, `Quot.sound`.
