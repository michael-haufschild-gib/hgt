# Calibrated trans-horizon recovery from active sawtooth samples

- **ID:** thim-active-sawtooth-calibrated-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Scope:** Exact kernel and finite recovery of the active sawtooth observation map;
  determine whether one scalar calibration restores every prefix defect.

## Plan

1. Audit corpus inversion/recovery tools and current observation-period APIs.
2. Prove finite sample sufficiency at arbitrarily large common-power observations, exact
   kernel, and calibrated all-prefix defect recovery on paper.
3. Formalize a new leaf, audit actual source and all axiom closures, wire umbrella.
4. Index/lint, persist crisp ledger and memory, remove scratch files.

`update_plan` is unavailable. This card tracks work; README is read-only.

## Selected mechanism

At a self endpoint, twice the active sawtooth is the divisor sum of
`b(d)=c(d)-c(d)/d`, whose unit coefficient vanishes. For squarefree-supported weights,
power invariance permits observations at `d^m` with one exponent m placing every
nonunit sample arbitrarily far beyond N. This uses the radical structure directly;
no full-period wait is necessary. Möbius inversion recovers every coefficient `c(d)`
for `2<=d<=N`. The remaining visible coefficient is `c(1)`, equivalently the finite
harmonic sum once the nonunit coefficients are known. The affine law then recovers every
prefix defect, with no zero-mean restriction.

## Gates

- [x] Corpus frontier and exact theorem selection.
- [x] Dependency-closed paper proof and novelty audit.
- [x] Actual-source Lean and all-declaration axiom audit.
- [x] Umbrella/index/lint, ledger, artifact audit, cleanup.

## Boundary

Coefficients outside `[1,N]`, including zero, are invisible to fixed-horizon observables.
No recovery of those coefficients is claimed. No global sign theorem for fixed
Möbius or damped weights is assumed. No computations, added axioms, or full builds.

## Corpus audit

Hybrid BVI search returned the existing initial-prefix discrepancy inverse, Selberg
coordinate inverse, and lag-schedule recovery, but none for active sawtooth samples.
Lexical `activeCenteredSawtoothSum inversion` and `activeCenteredSawtoothSum recover`
returned no declarations. The Mathlib Möbius inversion theorem and BVI active self
endpoint formula supply the constituents. No external/global novelty claim.

## Paper proof [PROVED HERE]

Write `A_N(c,j)=activeCenteredSawtoothSum N c j j` and
`f_N(d)=1_{d<=N}*(c(d)-c(d)/d)`. For every positive j, the endpoint identity gives
`2A_N(c,j)=sum_{d|j} f_N(d)`. Möbius inversion yields, for `2<=d<=N`,
`c(d)=2d/(d-1) * sum_{ab=d} mu(a)*A_N(c,b)`.
For squarefree-supported c, replace each `A_N(c,b)` by `A_N(c,b^m)` for any m>=1.
The b=1 term vanishes. Thus N-1 observations determine all nonunit coefficients;
conversely those coefficients determine the entire active sawtooth profile at N,
since the unit-divisor sawtooth vanishes. This identifies the exact fixed-horizon
kernel, including invisible coefficients outside the horizon.

For two weights with equal nonunit coefficients, the unit-shift law and finite-sum
locality give `s_c(k)-s_b(k)=H_c-H_b` at every k and
`D_c(M)-D_b(M)=(H_c-H_b)*(s_b(M+1)-s_b(1))` at every prefix M. Hence equality of
power samples plus equality of finite harmonic sums is equivalent to equality of all
visible coefficients and forces equality of every prefix defect.
The constant response difference also cancels from every additive jump, so power
samples alone determine every Dirichlet-energy window, with no harmonic calibration.

Since d>=2, choosing a sufficiently large common m makes every d^m exceed any
prescribed scale. No sub-horizon bound on observation positions or defect prefixes
remains. Finally, `|mu(a)|<=1` and `2d/(d-1)<=4` give the inverse stability bound
`|c(d)-b(d)|<=4*sum_{uv=d}|A_N(c,v^m)-A_N(b,v^m)|`, independent of N and m.
The factor four multiplies a divisor-indexed l1 error sum; no divisor-count-independent
sup-norm estimate is asserted.

## Squarefree sampling reduction [PROVED HERE]

The N-1 generic samples can be reduced within the assigned squarefree weight class:
only squarefree bases `2<=j<=N` are needed. To recover a squarefree target d, every
divisor v appearing in its Möbius inverse is squarefree, so all nonunit terms are
measured. Nonsquarefree target coefficients vanish by support. Hence the reduced
power sample vector still has exactly the same coefficient kernel and determines
all additive energies; harmonic calibration still recovers every prefix defect.

## Formal verification

- Leaf: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ActiveSawtoothPowerSamplingAndCalibratedRecovery.lean`.
- 20 public theorems, one public definition, one private helper. Actual-source
  `lake --old env lean -o ... ActiveSawtoothPowerSamplingAndCalibratedRecovery.lean`
  exited 0 without warnings. Scratch axiom audit exited 0; all 22 declaration
  closures contain exactly `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA-256: `3f9d54ec171a4708fdbcd6db8b30335459f7e635ffc8ef042afc61feae975391`.
- Single umbrella import, MainTheorems reachability, fresh compiled artifact,
  all 21 public generated API entries, source hygiene, and whitespace verified.
- Index exited 0. Final authoritative `scripts/formal_tools.py lint --check-generated`
  exited 1 on eight unrelated unwired leaves and the existing THIM field-umbrella
  registration issue. No finding names this leaf; no stale generated file remained
  after one refresh. First-run logs preserve the transient stale-index findings.
- Evidence: `logs/thim-recovery-{lean,axioms,index,lint}.txt`,
  `logs/thim-recovery-audit.json`. Knowledge: `logs/thim-radical-sawtooth-knowledge.md`.
- Seven owned scratch files removed; all owned jobs terminated. No README edits,
  numerical experiments, full builds, added axioms, or heartbeat changes.
- Fourth connected contribution completed; the open-ended research goal stays active.
