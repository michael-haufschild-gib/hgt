# BVI prime-tail calibration and literal Möbius defect — 2026-10-18

Canonical leaf: formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean. Wired into BVI umbrella. Card: docs/drafts/pipeline/3-formalized/bvi-prime-tail-calibration-and-mobius-defect-2026-10-18.md.

Let P={p prime: N<2p≤2N}, H=Σ_{p∈P}1/p, E=Q_Sel−Q_Bez, A=Σ_{p∈P}c(p)^2/p, R=Σ_{p∈P}s(p)^2/p. Exact terminal coordinates Y(p)=c(p)/p and responses s(p)=c(1)+c(p) give E≥A and
(1−t)E+tR−t(1−t)c(1)^2H=(1−t)(E−A)+Σ_{p∈P}(c(p)+t c(1))²/p.
Hence t(1−t)c(1)^2H≤(1−t)E+tR for N≥1 and EVERY real t≤1. The initial t≥0 premise was unnecessary; wider paper proof was audited before certification. Explicit weights c(1)=a, c(p)=−ta on P, zero elsewhere attain E=t²a²H and R=(1−t)²a²H. This sharp attained law is the positive survivor.

For literal μ, N≥2 and 1≤M≤N, combined signed defect D(N,M)=D_LCM+R_Bez=M E(μ)−1≥M H−1. At M=N, D≥#P−1. Existing unconditional prime-window theorem gives eventually D(2n,2n)≥n/(2 log n)−1. For every α<1 and real C, eventually C(2n)^α<D(2n,2n). Thus no eventual bound D(N,N)≤C N^α exists. Capstones: sievePrimeTail_calibration_bound, sievePrimeTailCalibrationWeight_reserves, sievePrimeTail_calibration_attained, moebiusCombinedPrefixDefect_eq, eventually_moebiusCombinedPrefixDefect_gt_rpow, not_eventually_moebiusCombinedPrefixDefect_le_rpow.

Scope: raw combined signed remainder for literal μ through the sieve horizon. Does NOT rule out cancellation with the diagonal main term, other horizons, or modified sources with their explicit cost. BVI and RH remain open.

Verification: canonical lake --old env lean -j 1 with -o/-i exited 0, no diagnostics, Lean 4.32.2. Separate /tmp/hgt_bvi_prime_axioms.lean exited 0; ALL 22 public declarations (7 definitions, 15 theorems) use only propext, Classical.choice, Quot.sound. Seven capstone types inspected. Source SHA256 e9e97c648cc82d37ea8aeec58d3dbae8029ecd1f91931fb1159c0b503c33f7b9. Manifest: /tmp/hgt-bvi-prime-audit-manifest.json; final/axiom/index/lint logs retained. Temporary owned cache, setup maps and failed prototypes removed after processes exited; external caches/builds untouched.

Index refreshed. Final lint --check-generated EXIT 1 solely for unrelated unreachable BVI module DilatedCellScalingAndSecondOctaveFermiJumpBridge (plus existing large-file warnings). Do not claim global lint passed. This finding may change as concurrent work finishes.

Rotation now RW → TH → MSC → RB → SZ → BVI. Next fresh research unit must use another family; see `mem:research/route-rotation-bvi-2026-10-18`. RH goal remains active.