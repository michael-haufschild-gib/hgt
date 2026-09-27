# Prime-height commutator has a noncompact Calkin ghost — Lean certificate

- **Paper card:** `stc-prime-height-commutator-calkin-ghost.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCPrimeHeightCalkinGhost`,
  `GaloisForLFunctions.RHTower.DeningerGammaAllPrimeStokesPairBridge`, `GaloisForLFunctions.RHTower.STCPrimeWindowPackets`
  (uses corpus `LpReindexCompactDichotomy`, `BoundedDiagonalOperatorLp`, `SoninEulerCornerNoncompact`, `SoninCalkinNormBound`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`H` = multiplication by `h_p = xiGammaEulerBoundaryHalfHeight p e` on its natural domain `stcHeightDomain e`.

| Card item | Lean theorem |
|-|-|
| (1) `S_pq = -(h_p - h_q) Q_pq`; two-channel `Q` | `source_pair_commutator_identity`, `source_pair_symmetric_kernel_two_channel` |
| finite packets: `S = -[H, Q]` | `sourcePacket_sylvester` |
| PNT: disjoint cofinal pairs with vanishing gap | `exists_prime_swap_pairs`, `exists_prime_pair_ratio_lt` |
| (2) `X` bounded, selfadjoint, norm one, not compact; `X(D(H)) ⊆ D(H)`; `[H,X] = K` on `D(H)` with `K` compact | `stc_prime_height_commutator_calkin_ghost` |
| nonzero Calkin class: `essentialNorm X ≥ 1`, `essentialNorm K = 0` | `stc_prime_height_commutator_calkin_ghost` |
| no Calkin lower bound `‖[X]‖ ≤ C ‖[[H,X]]‖` | `no_calkin_lower_bound_prime_height_commutator` |
| critical amplitudes not square summable on the full carrier (survivor remark) | `summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_iff` |
