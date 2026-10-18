# Contribution 005 — sharp initial-prefix observability

Verified total is now 5 / 250. One connected contribution, not one count per theorem.

Source: `formal/GaloisForLFunctions/BezoutValuationIncidence/SharpInitialPrefixObservabilityAndExactGramDeterminants.lean`.
Card: `docs/drafts/pipeline/3-formalized/bvi-sharp-initial-prefix-observability-2026-10-18.md`.
Ledger: `logs/bvi-root-2026-10-18-knowledge.md`.
Namespace: `GaloisForLFunctions.BezoutValuationIncidence`.

## Exact results

For all natural N,T and all real weights c, with S=min(T,N), all discrepancies L_N,c(M) at 1≤M≤T vanish iff T=0 or both c_d=0 on 2≤d≤S and Σ_{d=S+1}^N c_d/d=0. The first N−1 prefixes determine every c_d for 2≤d≤N, modulo c_1, and their simultaneous vanishing is equivalent to sieveVariance N c=0. All empty/degenerate cases are included.

`sievePrefixDataIncrement`, `sievePrefixMobiusLift`, and `sievePrefixInterpolatingWeight` implement arbitrary-data reconstruction. The last uses the existing kerPEndpointWeight on the Möbius lift. `sievePrefixInterpolatingWeight_realizes` gives harmonic sum zero and exactly the prescribed first n observations at level n+1, without an a(0) premise. `sievePrefixInterpolatingWeight_recovers_tail` recovers all nonconstant coefficients of any actual source.

`sievePrefixLastPairWeight_sharp_horizon` uses coefficients n+1 and −(n+2) at n+1,n+2: all first n prefixes vanish, the next equals n+1, and variance is positive. This sharp obstruction has a positive survivor: the exact hidden-tail law and explicit reconstruction.

On Fin n, rows M=i+1 and columns d=j+2:
- `sievePrefixObservationMatrix` A has entry cast(Nat(M/d))−M/d and determinant (−1)^n/(n+1).
- `sievePrefixRamanujanMatrix` R has entry Re(pmRamanujanPrimitive (j+2) (i+1)).
- `sieveTailMultiplesMatrix` T has entry 1/d when e∣d, otherwise zero.
- A=R*T, det T=1/(n+1)!, det R=(−1)^n*n!.
- `sievePrefixGramMatrix` K=R*diag(1/φ(e))*Rᵀ has K_ii=sievePrefixDualEnergy (n+1) (i+1), determinant (n!)²/∏φ(e), and is positive definite, including n=0.

Useful public bridges: `sievePrefixDiscrepancy_zero`, `sievePrefixDiscrepancy_succ_sub`, `sievePrefixDiscrepancy_sub`, `sievePrefix_single_response`, `sieveVariance_eq_zero_iff_tail_zero`. The entire package is unconditional. It gives finite rank/volume/reconstruction, not uniform conditioning or asymptotic cancellation.

## Verification

21 public theorems, 8 public definitions, 10 private theorem helpers, 1 private definition = 40 declarations. API probes, minimal determinant prototype, full scratch proof, and named original-source check passed. Named source was warning-free. All 21 public axiom closures (including the simp-tagged zero theorem) are exactly propext, Classical.choice, Quot.sound. Raw audit: `logs/bvi-root-2026-10-18-prefix-observability-axioms.txt`.

All 40 declaration names/kinds/lines/modules/paths matched the lexical corpus across two pages. All 11 current field modules are wired. Artifact installed atomically and freshness/hash verified. SHA-256: 0d69a22b5f02dc1b3dabd5ac264fe10bd27e89ac6cca8eaaa27d0e3fdf2e8baa. Source SHA-256: 3c0716b0b04f4239363ed29ff78c193d90a56c7295d41a2100fa863123c1733b.

Global lint exited 1 only for unrelated umbrella omissions: RHTower.SuzukiCriticalBetaKernel; BiScaleUncertainty.ClampedRampLatticeSum; FactorialMuntzBoundaryPole; FactorialMuntzBoundaryRepair; StationaryResolventMarkovPositivityAndNodalDefectProducer. No field or proof-debt findings. Do not call global lint passing or modify those agents' files.

Another agent's Lake build was replacing compiled dependencies. Verification used an APFS compiled-import snapshot with all 9,355 inherited project modules, original source, and explicit --root=/Users/michael/Documents/code/hgt/formal. Appending a fallback LEAN_PATH does not fix missing modules in the first package root. One owned foreground Lean process at a time. No umbrella/full build. All owned processes terminated; guarded cleanup removed all 34 /tmp/bvi5-* paths and preserved installed artifact/source.

## Next uncounted question

`docs/drafts/pipeline/0-backlog/bvi-integral-prefix-lattice-and-prime-rank-defect-2026-10-18.md` proposes integral equivalence of actual R to diag(1,…,n), cokernel classification, prime rank loss floor(n/p), and canonical Smith factors lcm(1,…,floor(n/(n−j))). None is counted or formalized yet. Card records symbolic factorization candidates and partial-search limitations. Reuse existing SmithNormalFormMatrix/DVR and `HTGeometry.ConstraintRelativity.nonempty_coker_equiv_pi_of_smith` in SimpleHorizonTransmutation; general Smith/cokernel theory is prior work.
