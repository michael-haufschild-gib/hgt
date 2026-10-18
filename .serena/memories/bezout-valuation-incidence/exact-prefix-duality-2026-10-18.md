# Exact finite-prefix discrepancy duality — contribution 004

Verified 2026-10-18. One connected contribution; current root ledger total 4/250.

Source: formal/GaloisForLFunctions/BezoutValuationIncidence/ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean
Card: docs/drafts/pipeline/3-formalized/bvi-finite-prefix-discrepancy-dual-energy-2026-10-18.md
Ledger: logs/bvi-root-2026-10-18-knowledge.md
Raw axiom audit: logs/bvi-root-2026-10-18-prefix-duality-axioms.txt

For all natural N,M and all real weights c:
- sievePrefixDiscrepancy N M c = finiteFloorSum N c M - M*finiteHarmonicSum N c.
- It equals -sievedFractSum N c M and the literal divisor-sequence prefix minus harmonic drift.
- Exact coordinate identity: L = sum over e in Icc 2 N of Re(pmRamanujanPrimitive e M)*selbergMultiplesCoord N c e.
- sievePrefixDualEnergy N M = sum Re(R_e(M))²/phi(e).
- Sharp bound L² <= sieveVariance N c * sievePrefixDualEnergy N M.
- sievePrefixExtremizer is the existing finite Ramanujan inverse applied to y(1)=0 and y(e)=Re(R_e(M))/phi(e) otherwise. It attains H=0, V=A, L=A.
- Universal constants: (forall c, L² <= K*V) iff N<=1 OR A<=K. The empty-level branch and A=0 case are essential.
- A=0 iff every d in Icc 1 N divides M. This includes M=0 and N=0,1.

Main APIs:
sievePrefixDiscrepancy_eq_ramanujan_diagonal
sievePrefixDiscrepancy_sq_le_variance_mul_dualEnergy
sievePrefixExtremizer_attains_dualEnergy
universal_sievePrefixDiscrepancy_constant_iff
sievePrefixDualEnergy_eq_zero_iff_common_return

Reusable bridges:
selbergMultiplesCoord_sub N e c b
ramanujan_inverse_selbergCoords_eq N c d hd
sievedFractSum_eq_residueCombination N M c
sieveVariance_ramanujan_inverse N y

12 public theorems, 3 definitions, 4 private helpers. All compiled with no warnings under the named original source check. All 12 public axiom closures were exactly propext, Classical.choice, Quot.sound. All 19 declarations were compared against the research index; all 10 current field modules are in the umbrella.

Global lint exited 1 on eight unrelated BiScaleUncertainty umbrella omissions, listed on the card; no field findings or proof-debt violations. Do not claim global lint passed or modify those other-agent modules.

Reused prior work: pmRamanujan_sum_primitive_eq_residue; pmRamanujanResidueCoeff; weighted Cauchy and the fractional-part/mod identity from this mathlib. The M=1 centered Cauchy specialization and the complete-period second-moment identity already exist and are NOT new contributions.

A shared long-running Lake build was replacing inherited artifacts. Verification used an APFS-cloned compiled-import snapshot and a temporary Lake workspace, with original source path and --root=/Users/michael/Documents/code/hgt/formal. After verification, the .olean was installed into the actual build directory; hash/freshness checked. All 25 owned /tmp/bvi4-* paths were removed by a guarded cleanup. No owned Lean process remains. Checks took 7–10 minutes each under shared memory pressure; retain one running handle instead of starting duplicate checks.

Next uncounted candidate: docs/drafts/pipeline/0-backlog/bvi-sharp-initial-prefix-observability-2026-10-18.md. It records initial-prefix kernel/reconstruction, sharp horizon, and a determinant/Gram refinement. Complete its corpus and paper audits before new Lean.