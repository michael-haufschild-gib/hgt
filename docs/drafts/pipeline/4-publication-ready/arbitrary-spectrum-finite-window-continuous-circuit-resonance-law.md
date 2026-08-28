# Arbitrary-spectrum finite-window continuous-circuit resonance law

- **ID:** QREC-ARBITRARY-SPECTRUM-FW-CIRCUIT
- **Stage:** 4-publication-ready
- **Type:** THEOREM
- **Source:** finite-detuning circuit law, arbitrary-spectrum collision resolution, and Aug-2026 literature audit

## Frontier

- `[CORPUS]` `finiteSpectralSurvivalFidelityMean_eq_collisionMass_add_remainder` and `norm_fidelityReplicaFiniteWindowRemainder_le` give an exact resonant/nonresonant decomposition with inverse finite-detuning error for scalar replica statistics (`FiniteWindowReplicaCollisionResolution.lean`).
- `[CORPUS]` `recurrenceWall_singularCompletionLaw` gives exact sinc crossover and singular completed-time wall indicator (`RecurrenceWallSingularCompletionLaw.lean`).
- `[CORPUS]` `maximallyProjective_continuousCircuitCapture_finiteWindow_le` gives finite-window complete continuous-circuit occupation only after global maximal-projectivity/rational-independence (`FiniteWindowContinuousCircuitOccupationLaw.lean`).
- `[LITERATURE]` Short--Farrelly, *Quantum equilibration in finite time*, arXiv:1110.5759, bound arbitrary gap degeneracy using a gap-density function and inverse finite-time spectral resolution; minimum spacing between distinct gaps gives a `1/(T epsilon_min)` correction.
- `[LITERATURE]` Mark et al., *Maximum Entropy Principle in Deep Thermalization and in Hilbert-Space Ergodicity*, Phys. Rev. X 14, 041051 (2024), analyze finite-time temporal-ensemble convergence and identify `1/T` decay from sinc suppression at finite minimum higher-order gap.
- `[LITERATURE]` Riddell--Pagliaroli--Alhambra, arXiv:2206.07541 / SciPost Phys. 15, 165 (2023), derive recurrence rarity from generic spectral-moment concentration, not deterministic finite-window complete-circuit target occupation.
- `[LITERATURE]` Oszmaniec--Kotowski--Horodecki--Hunter-Jones, arXiv:2205.09734 / Phys. Rev. X 14, 041068 (2024), prove complexity saturation and recurrence for random circuits and stochastic local Hamiltonians, not arbitrary deterministic static spectra.

## Failed conjecture 1

`[CONJECTURE]` At fixed Fejér resolution, positivity of the retained finite detuning floor suffices for the existing finite-window continuous-circuit bound; full rational independence is unnecessary.

`[BRIDGE]` True by inspection of the Fourier proof, but inverse minimum-detuning control after finite spectral truncation is established finite-time equilibration machinery. Replacing a global premise by its finite proof input improves experimental phrasing but is not a sufficient scientific delta.

**Relentless-interrogation lesson:** exact resonances, not merely small nonzero detunings, are the missing structural case. A universal law should retain them rather than exclude them.

## Frozen conjecture 2

`[CONJECTURE]` For every finite spectrum, with no simplicity, genericity, rational-independence, chaos, randomness, locality, or Diophantine assumption, every translated finite window obeys a complete continuous-two-qubit-circuit occupation bound of form

`2^d E20(n,s) [ b_N^d + R_N A_N^d + Q_N A_N^d * 2/(T Delta_N^nz) ]`,

where:

- `R_N` is number of nonconstant tensor-Fejér packet sheets with exactly zero spectral action;
- `Q_N` is number with nonzero spectral action;
- `Delta_N^nz` is minimum absolute nonzero packet action, assigned `1` if no nonzero sheet exists;
- `A_N = (N+1)^(-1) b_N`;
- `E20(n,s)` covers complete uncountable arbitrary-`SU(4)` two-qubit circuit family at operator tolerance `1/20`.

Every term is finite and spectroscopically determined. Exact resonances survive as persistent baseline; all nonresonant sheets decay at `1/(T Delta_N^nz)`. Under maximal projectivity `R_N=0`, recovering and sharpening existing finite-window theorem.

## Hostile attack

- Fourier resonant/nonresonant split is `[BRIDGE]`, not itself novel.
- Scientific residue is exact conjunction: arbitrary deterministic finite spectrum (including degeneracies and integrable resonance), every translated window, physical operator norm modulo global phase, complete uncountable continuous two-qubit circuit class, and explicit finite-resolution resonance census.
- Search found no source stating this conjunction. Priority remains provisional pending expert audit.
- Bound may be vacuous when resonance census is large; that is structural information, not proof failure.
- No pointwise hardness, mixing, efficient compilation, thermodynamic uniformity, or exact circuit-complexity evaluation follows.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Open core

`[OPEN CORE]` Prove one tensor-Fejér window theorem that partitions packet sheets into zero and nonzero action, controls zero sheets by count times coefficient envelope, and controls nonzero sheets by a universally positive finite minimum. Transfer through tube geometry and twentieth-net entropy without reintroducing a spectral premise.

## Gates

- [x] 0 → 1: corpus and literature frontier, failed bridge, frozen stronger conjecture, hostile verdict
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: exact unconditional Lean theorem, targeted build, axiom audit
- [x] 3 → 4: standalone manuscript integration and final novelty audit

## Constraints

- No numerical computation.
- No custom axioms or placeholders.
- One foreground Lean process.
- Targeted module checks/build only; wire umbrellas without building them.

## Dependency-closed paper proof

`[PAPER-PROVED]` Fix dimension `d`, Fejér resolution `N`, frequency vector `omega`, width `rho`, centre `c`, and positive window length `T`. Let `S` be finite nonconstant tensor-Fejér packet. Partition it disjointly as

`Z = {k in S : packetFreq omega k = 0}` and
`Q = {k in S : packetFreq omega k != 0}`.

Define `Delta_N^nz(omega)=1` if `Q` is empty and otherwise minimum of finite set `{|packetFreq omega k| : k in Q}`. In nonempty case every member is strictly positive by definition of `Q`; minimum of finite nonempty positive set is positive. Empty case is immediate. Thus `Delta_N^nz(omega)>0` for every frequency vector, with no arithmetic hypothesis, and `Delta_N^nz(omega) <= |packetFreq omega k|` for every `k in Q`.

Exact tensor-Fejér expansion is

`F(t)=mu + sum_{k in S} a_k exp(i t xi_k)`,

where `mu=(rho/(2pi)+e_N(rho))^d`, `xi_k=packetFreq omega k`, and `|a_k|<=A=((N+1)^(-1)(rho/(2pi)+e_N(rho)))^d`. Partitioning `S=Z disjoint_union Q` gives

`F(t)=M_res + sum_{k in Q} a_k exp(i t xi_k)`,

with exact resonant mass `M_res=mu+sum_{k in Z}a_k`, independent of time. Direct integration over arbitrary translated window gives

`|(1/T) integral_u^(u+T) exp(i t xi) dt| <= 2/(T |xi|)`

for every nonzero `xi`. Triangle inequality, coefficient bound, and definition of `Delta_N^nz` yield

`|(1/T) integral F - M_res| <= |Q| A * 2/(T Delta_N^nz)`.

Taking real parts and bounding resonant sum by triangle inequality yields unconditional scalar envelope

`(1/T) integral F <= mu + |Z| A + |Q| A * 2/(T Delta_N^nz)`.

Periodic product tent of width `rho` is pointwise bounded by `F`. For cube radius `r`, use width `2r`; standard scaled-tent indicator inequality gives indicator of union of `m` cubes at most `2^d` times sum of `m` product tents. Integrating and applying preceding bound to every centre gives

`volume(cubeVisit intersect (u,u+T]) <= 2^d T m [mu + |Z| A + |Q| A * 2/(T Delta_N^nz)]`.

For circuit targets, take fixed operator-norm `1/20` net of every circuit using at most `s` arbitrary continuous two-qubit gates. Net cardinality is at most `E20(n,s)`. Any physical capture within `1/20` lies in projective spectral tube of radius `1/10` around one net point. Exact chord-to-arc transfer places each tube in angular cube of radius `rho_*=asin(1/5)+pi/8`, with `2 asin(1/5)<rho_*` and `2rho_*<=pi`. Apply cube law with `m<=E20(n,s)`, `d=2^n-1`, physical relative-frequency vector, `mu=b_N^d`, and `A=((N+1)^(-1)b_N)^d`. This is frozen conjecture's displayed bound for every finite spectrum and every translated positive-length window.

No step assumes rational independence. If spectrum is maximally projective, `Z` is empty because every nonzero packet character has nonzero action; old theorem is recovered with `Q=S`. If all packet sheets are resonant, `Q` is empty, assigned detuning is harmless, and correction vanishes exactly. These endpoint checks close both arithmetic extremes.

### Hostile proof audit

- Packet sheets may represent duplicate integer characters. Counting sheets overestimates but cannot invalidate inequality.
- Resonant amplitudes can interfere destructively. Replacing exact resonant mass by sum of coefficient norms weakens but preserves upper bound.
- Empty `Z` and empty `Q` cases are covered explicitly; no minimum of empty set is used.
- Window translation contributes only unit phase and disappears under norm, so bound is uniform in `u`.
- Circuit-net reduction covers all continuous gate parameters by compactness before union bound; it is not a discretized gate-alphabet claim.
- Physical event is exactly spectral capture modulo global phase by spectral decomposition, independently of degeneracy choice of eigenbasis.

`[OPEN CORE]` closed. Exact theorem is dependency-complete on paper.

## Formalization closure

- `finitePacketNonzeroDetuningFloor_pos`: unconditional positivity, including empty nonresonant packet.
- `finitePacketNonzeroDetuningFloor_le`: every retained nonzero action dominates finite floor.
- `resonantPacketIndexSet_card_add_nonresonantPacketIndexSet_card`: exact finite partition.
- `resonantPacketIndexSet_eq_empty_of_rationallyIndependent`: prior nonresonant regime is exact specialization.
- `nonresonantPacketIndexSet_eq_nonconstant_of_rationallyIndependent`: every retained nonconstant sheet is recovered there.
- `arbitrarySpectrum_periodicProductFejerMajorant_windowMean_le`: translated-window resonant/nonresonant Fejér law.
- `arbitrarySpectrum_finiteCubeVisit_tensorMajorantWindowUpper`: finite union-of-cubes occupation law.
- `arbitrarySpectrum_continuousCircuitCapture_finiteWindow_le`: physical projective operator-norm capture law for full continuous two-qubit circuit class.

Files:

- `formal/GaloisForLFunctions/HTGeometry/ArbitrarySpectrumFiniteDetuningTensorWindowLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/ArbitrarySpectrumFiniteWindowContinuousCircuitOccupationLaw.lean`

Verification:

- Direct `lake env lean` checks passed for both modules.
- Targeted builds passed; no umbrella or full build was run.
- Axiom audit for four principal declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
- New files contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Modules are imported by `GaloisForLFunctions.HTGeometry` umbrella.
- Project lint still fails only on unrelated pre-existing umbrella reachability errors; neither new module appears in error list.

## Publication closure

- Integrated as Theorem 24, `Arbitrary-spectrum finite-aperture circuit law`, without removing prior four-law framework or earlier results.
- Added standalone first-principles proof and arbitrary-spectrum experimental falsification protocol.
- Added and primary-source-verified Short--Farrelly (2012) and Mark et al. (2024) comparisons; novelty scoped to exact conjunction beyond those ingredients.
- Updated claim trace, novelty audit, hostile review and reference audit.
- Standalone scan found no references to formal tooling, internal project, RH or black holes.
- Tectonic build passed: 41 pages, no undefined references/citations, no overfull or underfull boxes.
- Visually inspected theorem, experiment, proof and architecture-figure pages; no overlaps or broken placement.
- Published PDFs are byte-identical to built `main.pdf`.
