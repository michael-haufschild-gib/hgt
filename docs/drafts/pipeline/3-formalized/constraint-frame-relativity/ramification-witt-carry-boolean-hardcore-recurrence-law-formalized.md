# Ramification binary Kummer carry, Boolean collision boundary, three-storey holonomy — formalized

- **ID:** `cfr-ramification-witt-carry-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-witt-carry-boolean-hardcore-recurrence-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.WittCarryBoolean` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.RamificationBooleanSupport` | shared |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs` | shared |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EscortLogit` | shared |

All wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — Boolean meet is the Kummer carry, card `(WC.1)`–`(WC.6a)`:

1. `digitSection` — the least-digit section `σ : 𝒫(F) → (ℤ/4)^F`.
2. `digitSection_add` — the boxed identity `(WC.3)`: `σ(S)+σ(T) = σ(S △ T) + 2σ(S ∩ T)`, so the
   carry `κ₂(S,T)` of `(WC.4)` is `S ∩ T`.
3. `witt_add` — the boxed length-two Witt addition law `(WC.5)`, which is `(WC.6)`: the additive
   group of `(ℤ/4)^F` is the length-two Witt ring of the Boolean `𝔽₂`-algebra.
4. `carry_cocycle` — the boxed cocycle identity `(WC.6a)`.
5. `carry_self` — `κ₂(S,S) = S`, the nonvanishing of the class.
6. `no_group_section` — the extension is nonsplit: no additive section of the mod-two reduction
   exists, because a lift of a nonzero mod-two basis vector has order four.

Theorem 2.1 — shell activity is zero carry, card `(WC.7)`–`(WC.8a)`:

7. `unitalShellIndicator_mul_pow_eq_one_iff` — the boxed equivalence `(WC.8)`: for squarefree
   `k, l`, `ã_m((kl)^m) = 1` exactly when the supports are disjoint, i.e. the carry is empty.
8. `pow_mul_pow_eq` — the boxed integer identity `(WC.8a)`, exhibiting the discarded
   repeat-occupancy factor `g^{2m}`.

Theorem 3.1 — Gibbs carry statistics, card `(WC.9)`–`(WC.11b)`:

9. `jointExp` — the joint law of two independent Boolean gases.
10. `prod_split_mem`, `jointExp_prod` — the per-site product law for the joint gas.
11. `jointExp_sum_prod` — factorisation of coordinatewise sums.
12. `jointExp_carry_card` — the boxed `(WC.10)`: `E|Κ| = ∑ q_p u_p`.
13. `jointExp_empty_carry` — the boxed `(WC.11)`: `P(Κ = ∅) = ∏ (1 - q_p u_p)`.
14. `jointExp_carry_card_self`, `jointExp_empty_carry_self`, `one_sub_sq_oddsToProb` — the boxed
    replica specialisation `(WC.11a)`.
15. `conditional_carry_eq_escort` — `(WC.11b)`: conditioned on zero outer residue, the carry
    probability is the second escort transform.

Theorem 4.1 — marked three-storey holonomy, card `(WC.12)`/`(WC.13)`:

16. `markedHistory` — the marked integral history `n · 1_S`.
17. `markedHistory_mod_two` — the mod-two observer closes after two steps.
18. `markedHistory_mod_four_two` — the boxed `(WC.13)`: the mod-four lift lands on the kernel
    point `2σ(S)` after two steps.
19. `two_digitSection_ne_zero` — that kernel point is nonzero for a nonempty configuration.
20. `markedHistory_mod_four_four` — the mod-four lift closes after four steps.
21. `sum_sq_markedHistory` — the integral history has squared norm `n²|S|`, so it never closes.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/WittCarryBoolean.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
