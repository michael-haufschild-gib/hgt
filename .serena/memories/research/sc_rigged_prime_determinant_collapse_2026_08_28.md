# SC rigged-prime determinant collapse (2026-08-28)

Formalized in `formal/GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinDeterminantCollapse.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/sc-rigged-prime-determinant-collapse.md`. Frontier map remained read-only.

Key results:
- Exact shared-reservoir determinant: `det = orientation^m * (1-m) * ∏ weight`.
- `tendsto_preDivisorRiggedPrimePacketDeterminant_zero`: raw cofinal finite SC Gram determinants tend to zero throughout open critical strip; wall packets are identically zero.
- Orientation times absolute weight equals signed Gamma-Bockstein. `tendsto_preDivisorRiggedPrimeNeutralPacketDeterminant_div_pow`: packet of `m+2` primes has exact neutral order `m+2`, with nonzero leading coefficient `(1-(m+2))*∏[-2 Fisher(p_i) log p_i]`.
- `tendsto_fixedPole_mul_preDivisorRiggedPrimeNeutralPacketDeterminant_zero`: any renormalizer with fixed finite pole order `k` still collapses whenever `k < m+2`.
- `no_realProfile_normalizedXiC`: no scalar profile depending only on horizontal real coordinate can equal normalized Xi; holomorphic small-period rigidity forces constancy, contradicting strict central Xi curvature.

RH burden delta: raw ordinary determinant landing, all fixed-order wall regularizations, and arbitrary horizontal-only scalar normalizations are closed as no-gos. Surviving SC landing must use packet-growing singular regularization before wall specialization and add genuine vertical complex/operator-valued data.

Verification: `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinDeterminantCollapse.lean` PASS; exact `lake build GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinDeterminantCollapse` PASS; capstones depend only on `[propext, Classical.choice, Quot.sound]`. Global `scripts/formal_tools.py lint` failed only on unrelated concurrent unreachable-module errors; new module was reachable. No forbidden declarations in new module.