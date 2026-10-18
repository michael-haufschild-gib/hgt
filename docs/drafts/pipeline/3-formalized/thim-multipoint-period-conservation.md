# Multi-point defect averaging and period conservation

- **ID:** thim-multipoint-period-conservation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A full-period Dirichlet energy controls exact affine defect drift along every phase, and full-period moving averages remove all phase fluctuations.

## Requirements and plan
- [x] Read the current field README completely; inspect relevant memories and corpus. README is read-only. Architecture/testing documents are absent.
- [x] Prove the exact period-shift law with the requested interval energy and its nonpositive sign.
- [x] Prove exact drift for all period multiples, monotonicity, and linear convergence to negative infinity for nonconstant responses.
- [x] Classify zero period energy and formalize full-period moving-window averaging as the connected strengthening.
- [x] Audit original leaf using `lake --old env lean`, inspect every axiom closure, wire umbrella without building it, refresh index, run formal lint, remove owned scratch, save knowledge.

## Corpus inputs and dependency-closed paper proof
Let L be `horizonObservationModulus N`, s(k)=`sieveSeq N c k`, and D(M)=`sieveRenormalizedPrefixDefect N M c`. The positive modulus and `horizonObservationState_add_modulus` give s(k+L)=s(k). Thus the squared difference e(k)=(s(k+1)-s(k))² is periodic. Its sum E over any L consecutive indices is independent of starting phase: shifting the interval one step removes e(a) and adds e(a+L)=e(a).

Subtract the existing polarization identities at M and M+L. The endpoint response squares cancel by periodicity, leaving 2(D(M+L)-D(M))=-E, with E equal to the requested sum over M+1 through M+L. Iteration gives D(M+qL)=D(M)-qE/2. Since E is a sum of squares, E≥0 and every phase subsequence is nonincreasing. E=0 forces each difference over one period to vanish, hence periodicity and induction force s constant globally. Conversely a constant response has E=0 and D=0. Every nonconstant response therefore has E>0 and exact linear escape to negative infinity.

The unrestricted period-shift statement includes M=0: the empty defect vanishes, the positive modulus permits polarization at L, and s(L+1)=s(1) cancels its boundary. No endpoint hypothesis remains in `two_mul_sieveRenormalizedPrefixDefect_period_sub_all`. The requested monotonicity and limit laws retain their stated M≥1 domain.

For W(M)=sum_{j=0}^{L-1}D(M+j), the moving-window difference telescopes to D(M+L)-D(M)=-E/2. Therefore W(M+t)=W(M)-tE/2: averaging a full observation period removes every boundary fluctuation, even for unit shifts. This is the additional multi-point conservation law; the normalized average has slope -E/(2L).

The exact obstruction to identifying prefix defects by response phase is E>0: returning to the same phase preserves D if and only if the response is constant. The positive replacement retains the traversal count through the exact affine law. This corrects a potential interpretation of the README's phase prose without editing the README or weakening the future-response phase theorem.

## Evidence and boundaries
Hybrid corpus search found equal-response endpoint energy subtraction in `AllHorizonRadicalSawtoothAndDefectReduction`, the exact polarization identity, and the two-point averaging/Poincaré tools. Search reports partial=false but older-generation coverage snapshot and unavailable semantic coverage; candidate applicability must be compiled. BVI already classifies exact response periods; do not count response periodicity itself as new.

Only structural domain conditions and the explicitly requested nonconstancy classification are allowed; no unproved analytic premises, numerical experiments, added axioms, heartbeat changes, full builds, or RH work. The target leaf and its one umbrella import are the code write scope. Other agents' work is read-only. `update_plan` is unavailable; this card persists the plan. Serena ignores Lean paths (verified in this session), so source reads and patches are the available fallback.

## Verification boundary
- Target: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/MultiPointDefectAveragingAndPeriodConservation.lean`.
- Original source audited with `lake --old env lean -o ... -i ...`: exit 0, no diagnostics. Required Pillar XIV dependency also compiled cleanly without source edits.
- All 18 public theorems, 2 definitions, and 3 private helpers passed scratch-file `#print axioms`: exactly `propext`, `Classical.choice`, `Quot.sound`. Corrected current-toolchain name checks also passed.
- All 20 public declarations appear exactly once in `LEAN_API.md`; all private helpers are corpus-searchable. The unique leaf import is reachable through the field umbrella and `MainTheorems`; no umbrella build was run.
- Final `scripts/formal_tools.py lint --check-generated` exits 1 on four unrelated BiScaleUncertainty leaves and existing field-umbrella registration. No target-leaf, prohibited-declaration, or stale-generated-file error. Global lint is not claimed clean.
- Exact source/artifact hashes, requirement mapping, command outcomes, and lint errors: `logs/thim-period-audit.json`. Compiler: `logs/thim-period-lean-audit.txt`; all axiom closures: `logs/thim-period-axioms.txt`; knowledge ledger: `logs/thim-period-knowledge.md`.
- Owned scratch files removed after terminal audits. README remained read-only; no full builds, heartbeat changes, commits, or push. This is one connected contribution; external novelty/publication readiness is not asserted.
