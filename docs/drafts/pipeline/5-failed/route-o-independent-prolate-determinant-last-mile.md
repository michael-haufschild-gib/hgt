# Route O independent prolate/determinant last mile

- **ID:** `route-o-independent-prolate-determinant-last-mile`
- **Stage:** 5-failed
- **Type:** FAILED SUBMECHANISM / NO-INDEPENDENT-LAST-MILE
- **Scientific status:** `[SUBMECHANISM RETIRED] [ROUTE O OPEN] [NOT AN RH PROOF]`
- **Positive survivor:**
  `../3-formalized/not_new_scientific_knowledge/route-o-prolate-rayleigh-ground-lock.md`

## Retired claim

The Connes/CCM determinant lane was proposed as

```text
explicit constrained-prolate seed
-> true restricted-Weil ground vector
-> selfadjoint finite spectral triples
-> locally uniform determinant convergence to Xi
-> RH.
```

It is retired **as an independent last mile**. This does not disprove the proposed convergence and
does not prove or disprove RH. In particular, it does not rule out a source-derived proof of the
ground comparison, a direct cofinal restricted-Weil positivity proof, or another construction in
Connes's program.

## Exact obstruction

Let `r_n` be the explicit normalized prolate-seed Rayleigh value, `epsilon_n` the true nested
restricted-Weil floor, and `Delta_n=r_n-epsilon_n`. Once the source theorem `r_n->0` is available,

```text
Delta_n -> 0  <->  RH.
```

If RH is false, `Delta_n` is eventually bounded below by one fixed positive constant. Therefore
the ground-vector comparison required to transfer the prolate determinant is not a lower-cost
analytic preliminary. It is the RH-bearing cofinal Weil-floor theorem itself.

The earlier stronger target

```text
Delta_n / Gap_n = O(lambda_n^(-1))
```

already implies `Delta_n->0` after the two vanishing fixed-depth trial levels are inserted, hence
already proves RH without a determinant limit. A lower bound
`epsilon_n >= -o(1)` collapses in the same way.

## Exhausted mechanisms

1. **Arbitrary real-zero approximants:** circular; under RH constant Xi-based sequences witness
   the target.
2. **Finite simple-evenness:** no longer a blocker for existence of a real-rooted finite
   source-or-response completion. Identifying the selected branch with the original CCM
   eta-channel ground-vector determinant remains open, but cannot bypass the cofinal floor lock.
3. **Determinant/resolvent algebra:** closed exactly for the source-locked finite matrix; it does
   not control the cofinal floor.
4. **Normalized Rayleigh-excess/gap transfer:** stronger than needed and already RH-sufficient.
5. **Vanishing negative allowance for the floor:** already the cofinal Weil criterion.
6. **Non-nested spectral evacuation:** impossible; a negative compactly supported Weil witness
   persists in every larger aperture.

## Strongest positive survivor

The formalized survivor is the **persistent false-RH Rayleigh-gap law**:

```text
not RH -> exists delta>0, eventually Delta_n>=delta.
```

Lean module:
`formal/GaloisForLFunctions/RHTower/CCMProlateRayleighGroundLock.lean`.

Finite source infrastructure survivor:
`formal/GaloisForLFunctions/RHTower/CCMPublishedRestrictedWeilMatrix.lean` formalizes the literal
restricted-Weil functional, exact CCM matrix, rank-two displacement, reflection, automatic ground
shift, and real-rooted source/response completion.

## Surviving whole-route theorem

Prove from literal prime/Gamma/prolate source, without an RH-equivalent spectral premise,

```text
epsilon_n -> 0
```

for one cofinal nested restricted-Weil family. This directly proves RH by Weil positivity. Any
claimed progress on this surviving branch must identify a source inequality capable of proving this
theorem; determinant normalization, zero transfer, finite real-rootedness, or relabeling `Delta_n`
is insufficient. This branch never closed, so no "reopening" claim is made.

## Closure gates

- [x] negative mechanism classified
- [x] strongest positive survivor dependency-closed on paper
- [x] positive survivor formalized unconditionally
- [x] literal finite source matrix and completion formalized
- [x] exact reopening theorem recorded
- [x] no claim that RH or the proposed convergence is false
- [x] scope restricted to determinant-after-comparison submechanism
- [ ] Connes/CCM program classified as a whole
