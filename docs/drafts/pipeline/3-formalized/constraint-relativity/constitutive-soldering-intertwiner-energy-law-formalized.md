# Constitutive soldering intertwiner-energy law — formalized

- **ID:** `constitutive-soldering-intertwiner-energy-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `constitutive-soldering-intertwiner-energy-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConstitutiveSoldering` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ConstitutiveSoldering.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ReynoldsEnergy` | abstract averaging energy, same result on any inner product space |

Both wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

The Hilbert–Schmidt pairing `⟪A,B⟫ = Tr[Aᴴ B]` was **not** rebuilt: the corpus already owns it in
the vendored `GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt` (`hsInner`, conjugate symmetry,
sesquilinearity, sum rules, `hsInner_self_re_nonneg`), which this module imports.  Mathlib has no
`InnerProductSpace` instance on `Matrix` — only scoped Frobenius *norm* instances — so the energy
identity is proved directly from `hsInner`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Hilbert–Schmidt energy:

1. `hsNormSq`, `hsNormSq_nonneg`, `hsNormSq_sub`, `hsNormSq_eq_sum`, `hsNormSq_eq_zero_iff`.
2. `hsInner_left_unitary`, `hsInner_right_unitary`, `hsNormSq_right_unitary` — unitary invariance.

Transport defect and cocycle:

3. `solderDefect` — card `(3)`, `Q_s(g) = ρ_T(g) s − s ρ_K(g)`.
4. `solderDefect_mul` — **card `(4)`**: `Q_s(gh) = ρ_T(g) Q_s(h) + Q_s(g) ρ_K(h)`.

Reynolds projection and curvature energy:

5. `solderAction` — the unitary conjugation action `U_g(s) = ρ_T(g) s ρ_K(g)⁻¹`.
6. `reynoldsProj` — **card `(5)`**.
7. `curvatureEnergy` — the left side of **card `(6)`**.
8. `solderDefect_eq_solderAction`, `hsNormSq_solderDefect` — `‖Q_s(g)‖ = ‖U_g s − s‖`.
9. `hsInner_solderAction`, `hsNormSq_solderAction` — the action is unitary for the HS pairing.
10. `solderAction_reynoldsProj` — the Reynolds projection is fixed by the action.
11. `curvatureEnergy_eq` — **card `(6)`**: `E(s) = ‖s‖² − ‖Π(s)‖²`.

Zero-curvature classification (card items 1–3):

12. `curvatureEnergy_eq_zero_iff` — `E(s) = 0` exactly when `s` intertwines the two
    representations.
13. `exists_unitary_curvatureEnergy_eq_zero_iff` — some constitutive soldering is flat exactly when
    some unitary intertwines them, i.e. exactly when the two representations are unitarily
    equivalent.

The positive gap:

14. `solderingSet`, `isClosed_solderingSet`, `norm_le_one_of_mem_solderingSet`,
    `isCompact_solderingSet` — the soldering set is compact.
15. `continuous_curvatureEnergy` — the energy is continuous.
16. `exists_positive_gap` — **card `(7)`**: if no soldering intertwines, the energy has a strictly
    positive minimum on the soldering set.

The minimal nonflat source history (card `(8)`):

17. `C2`, `c2Gen`, `c2_cases`, `c2_univ`, `c2Trivial`, `c2Sign` with unitarity and multiplicativity.
18. `c2_reynoldsProj` — `Π(s) = 0`.
19. `c2_curvatureEnergy` — every constitutive soldering has energy exactly `1`.
20. `c2_no_flat_soldering` — hence there is no flat soldering at all.

`ReynoldsEnergy` proves the same energy identity abstractly for any unitary action of a finite
group on a complex inner product space (`reynolds`, `reynolds_fixed`, `inner_reynolds_self`,
`reynolds_energy`, `reynolds_energy_eq_zero_iff`), which is the coordinate-free form of item 11 and
records that the identity does not depend on the matrix realization.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ConstitutiveSoldering.lean  # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ReynoldsEnergy.lean         # clean
lake build GaloisForLFunctions.HTGeometry                                                     # green
```
