# Finite-window spectroscopic continuous-circuit occupation law

- **ID:** QREC-FW-SPEC-CIRCUIT
- **Stage:** 4-publication-ready
- **Type:** THEOREM
- **Source:** corpus-wide recurrence/circuit audit and Aug-2026 literature audit
- **Statement:** One static nearest-neighbour qubit field can have every literal prefix obey a quantitative finite-window upper bound on time spent within fixed operator distance of every sub-Hilbert continuous two-qubit circuit; finite-time error is controlled by an explicit minimum among finitely many low-height spectral detunings and vanishes as laboratory duration grows.

## Goal
Upgrade the same-field asymptotic continuous-circuit occupation theorem to a finite-laboratory-time law whose only system-specific input is a finite, spectroscopically calibratable detuning floor. Preserve arbitrary continuous `SU(4)` gates, operator norm modulo global phase, static one-dimensional nearest-neighbour locality, and one compatible infinite field for every literal prefix.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `RHTower.exists_thermodynamicSameFieldFiniteWindowContinuousCircuitOccupationLaw`, targeted `lake build` green, exact declaration axiom audit clean
- [x] 3 → 4  publication-ready: standalone paper theorem and proof, literature boundary checked

## Frozen conjecture

Let `S_{N,d}` be the nonconstant tensor-Fejér packet at resolution `N`, and define

`Delta_{N}(omega) = min_{k in S_{N,d}} |packetFreq omega k|`, with value `1` when the packet is empty.

For every rationally independent `omega`, `Delta_N(omega) > 0`. For every translated time window of length `T > 0`, every centre, and every tensor-Fejér majorant, its normalized mean is at most its exact Haar constant plus an explicit Fourier coefficient cost times `2/(T Delta_N(omega))`.

After a fixed `1/20` operator net of all circuits with at most `s` arbitrary two-qubit gates, this yields a finite-window upper bound for operator-norm circuit capture at tolerance `1/20`. The target-to-cube radius is chosen strictly above the exact chord-to-arc radius forced by net error plus capture error. At the budget `s = floor(2^n/(64(n+1)))`, the geometric term tends to zero with `n`; for each fixed prefix, the detuning error tends to zero with `T`.

## Approach
1. Build fixed `1/20` exact- and at-most-gate circuit nets from existing quantitative `SU(4)` operator nets; prove their entropy remains below `2^(2^n-1)` eventually.
2. Select one phase centre for every nonempty operator tube. Convert the pairwise operator chord `<= 2/5` to a strict radian cube using the exact circle chord-to-arc law.
3. Define `Delta_N` as the finite nonconstant packet minimum. Rational independence proves positivity without `VWMA`, randomness, genericity, or an unproved Diophantine premise.
4. Prove finite-packet upper discrepancy, tensor-majorant upper law, and finite-union occupation law with error `O(1/(T Delta_N))`.
5. Reindex the finite circuit net by `Fin net.card`; transfer the physical phase flow to angular time and cap cardinality by the explicit circuit entropy.
6. Apply to every canonical spectrum of the existing thermodynamic same-field lifecycle.

## Literature boundary
As of the Aug-2026 audit, nearby results treat random local circuits/stochastic Hamiltonians, general finite-dimensional simultaneous recurrence, or arithmetic Floquet recurrence. No located result combines one deterministic static bounded-degree local Hamiltonian family, every literal thermodynamic prefix, a complete uncountable continuous two-qubit circuit class, operator-norm capture, and a finite-window occupation error controlled by finite spectroscopic detunings. Novelty claim remains limited to this conjunction and will be rechecked before publication.

## Failure pivots
- If the sharp operator-tube-to-cube transfer loses the entropy exponent, reduce net radius while preserving capture tolerance and reprove the entropy envelope.
- If explicit `Delta_N` bookkeeping blocks the tensor theorem, first prove the theorem under a positive separation parameter and then identify `Delta_N` in a separate closed lemma.
- Do not replace maximal projectivity by `not VWMA`; that would weaken the same-field theorem and make the experimental premise uncheckable.

## Log
- 2026-08-27 — created in 1-in-progress after literature-first and corpus-wide audits; conjecture frozen before proof attack.
- 2026-08-28 — paper proof closed.  A fixed `1/20` circuit net, exact chord-to-arc transfer, finite Fejér packet and positive retained detuning floor give a quantitative upper occupation envelope on every translated finite window.
- 2026-08-28 — formalized in `FiniteDetuningTensorMajorantWindowLaw.lean`, `TwentiethContinuousCircuitEntropyLaw.lean`, `FiniteWindowContinuousCircuitOccupationLaw.lean`, and `ThermodynamicSameFieldFiniteWindowContinuousCircuitOccupationLaw.lean`.  Targeted capstone build passed.  Axiom audit of detuning positivity, finite-cube window law, circuit finite-window law and same-field capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.  New files contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.  Project lint still fails on unrelated pre-existing umbrella-reachability errors; all four new modules are umbrella-reachable.
- 2026-08-28 — integrated into standalone recurrence manuscript as general finite-aperture theorem, same-field clause, dependency-closed appendix proof, scoped novelty comparison, limitations, and finite spectroscopic falsification protocol.  PDF rebuilt and visually checked.
