# Polarized incidence–Stokes and Route-E/Mass capacity-phase law — formalized

- **ID:** `polarized-incidence-stokes-and-e-mass-capacity-phase-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `polarized-incidence-stokes-and-e-mass-capacity-phase-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PolarizedIncidenceStokes` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/PolarizedIncidenceStokes.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.  Declarations live in namespace
`HTGeometry.ConstraintRelativity`.  The generic graph layer, the finite Abel path layer and the
ordered-prime instantiation are three separate sections, as the card's Lean-return note asked.

## Corpus reuse

- `RHTower/RouteEForbiddenSupportStability.lean` —
  `RHTower.ForbiddenSupport.tendsto_logRpow_div_sqrt`: every polylogarithmic quantity is negligible
  against the square root.  At exponent one this is `log p / √p → 0`, the analytic input of
  Theorem D.
- From mathlib: `Nat.nth`, `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`,
  `Nat.infinite_setOf_prime`, `Real.tendsto_log_atTop`, `Filter.Tendsto.inv_tendsto_nhdsGT_zero`,
  `Filter.Tendsto.const_mul_atTop`, `tendsto_atTop_mono`, `Finset.sum_range_sub`,
  `Finset.sum_ite_eq'`, `Relation.ReflTransGen`.

## Formal theorem chain

### Theorem A — polarization is a chain identification, cards `(1)`, `(2)`

1. `signlessIncidence`, `orientedBoundary`, `polarization` — card `(1)`, as linear maps on
   `ℂ^E` and `ℂ^V`.
2. `polarization_comp_signlessIncidence` — **`(2)` boxed**: `S_ε B⁺ = ∂`, from the hypothesis that
   every edge runs from a `+1` vertex to a `−1` vertex.
3. `norm_polarization_apply` — polarization is unimodular, so it preserves every absolute vertex
   coordinate; it is the identity on `ℂ^E`, hence preserves every edge capacity and every absolute
   edge-work functional `W_c` by definition.
4. `polarization_restrict` — the marked-port identity `π_A S_ε = S_{ε|A} π_A`.

### Theorem B — polarized discrete Stokes, cards `(4)`–`(7)`, `(9)`

5. `capacityResidual` — card `(4)`.
6. `polarized_stokes` — **`(5)` boxed**: `S_ε w = ∂q + S_ε r`.
7. `sum_orientedBoundary`, `polarized_charge` — **`(6)`**: augmentation kills oriented boundaries,
   so the polarized source charge equals the polarized residual charge.
8. `sum_orientedBoundary_mul`, `polarized_cut_flux` — **`(7)` boxed**: polarized source charge is
   signed cut flux plus unmatched residual.
9. `abs_polarized_charge_le` — **`(9)`**: under the capacity hypotheses `(4a)` the polarized charge
   is bounded by the total unused capacity `‖r‖₁`.

### The connected degree-zero quotient, card `(8)`

10. `augmentation`, `edgeRel`, `orientedBoundary_single`,
    `indicator_sub_mem_range_of_edgeRel`, `indicator_sub_mem_range_of_reachable`,
    `range_orientedBoundary_eq_ker_augmentation` — **`(8)`**: on a connected multigraph the
    boundaries are exactly the augmentation kernel, so `C_0 / im ∂ ≅ ℂ`; conjugating with `S_ε`
    gives `C_0 / im B⁺ ≅ ℂ` with class map `[w] ↦ ∑_v ε(v)w(v)`, which is `polarized_charge`.

### Theorem C — the finite Abel decomposition, cards `(10)`–`(13)`

11. `prefixSum`, `prefixSum_succ_sub`, `sum_indicator_range`, `sum_indicator_shift`.
12. `abel_boundary_decomposition` — **`(12)` boxed**: `z_N = ∂q_N + b_N`, written in vertex
    coordinates on the finite path, valid at every vertex.
13. `abel_pairing` — **`(13)` boxed**: the finite Abel summation identity for an arbitrary vertex
    profile.

### Theorem D — capacity-phase separation, cards `(14)`–`(17a)`

14. `realPrefix`, `capacity_le_realPrefix`, `inv_capacity_tendsto_atTop`.
15. `tendsto_prefix_div_capacity_atTop` — **`(16)` boxed**, abstract form: for any positive local
    capacity tending to zero the prefix/capacity ratio tends to infinity.
16. `tendsto_logGapWork_atTop` — **`(17)` boxed**, abstract form: the log-gap work diverges,
    by the telescoping lower bound `t_0(λ_N − λ_0)`.
17. `not_bounded_local_capacity` — **`(17a)` boxed**, abstract form: the prefix primitive lies in
    no fixed local-capacity ball `K_M(M)`.
18. `primeAt`, `primeAt_prime`, `primeAt_strictMono`, `primeLog`, `primeMassCapacity`,
    `primeMassCapacity_pos`, `primeLog_monotone`, `tendsto_primeAt_atTop`,
    `tendsto_primeLog_atTop`, `tendsto_primeMassCapacity_zero` — the ordered-prime data of card
    `(10)`: `λ_n = log p_n`, `t_n = log p_n / √p_n`.
19. `tendsto_primePrefix_div_capacity_atTop`, `tendsto_primeLogGapWork_atTop`,
    `not_bounded_prime_local_capacity` — **`(16)`, `(17)`, `(17a)` boxed, at the primes**.

## Scope

Card `(15)` (the C39 Lipschitz/telescoping bound `∑ t_{n+1}(λ_{n+1} − λ_n) ≤ 16e^{−λ_0/4}`) is
quoted by the card from a separate formalized result and is *not* re-proved here; Theorem D does
not use it, and the divergence `(17)` concerns the prefix primitive `T_{n+1}`, not the local
capacity `t_{n+1}`.  Section 4's Route-E dictionary (Möbius sign, Gibbs capacity, Hall cuts) is a
naming of the generic hypotheses; §7's filling profile `(18)` is a definition plus commentary; §8's
items 1, 5 are explicitly `NOT CLAIMED` and `OPEN`, and item 6 records that no RH consequence
follows.  None of that is formalized or claimed.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/PolarizedIncidenceStokes.lean  # clean, no warnings
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.PolarizedIncidenceStokes          # green
```

`#print axioms` on `polarization_comp_signlessIncidence`, `norm_polarization_apply`,
`polarization_restrict`, `polarized_stokes`, `polarized_charge`, `polarized_cut_flux`,
`abs_polarized_charge_le`, `range_orientedBoundary_eq_ker_augmentation`,
`abel_boundary_decomposition`, `abel_pairing`, `tendsto_prefix_div_capacity_atTop`,
`tendsto_logGapWork_atTop`, `not_bounded_local_capacity`,
`tendsto_primePrefix_div_capacity_atTop`, `tendsto_primeLogGapWork_atTop` and
`not_bounded_prime_local_capacity` returns only `[propext, Classical.choice, Quot.sound]`.
