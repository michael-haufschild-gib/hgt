# Physical first-return horizon-instability law

- **ID:** QREC-HORIZON-EXPONENT-INSTABILITY
- **Stage:** 4-publication-ready
- **Type:** THEOREM (Lean)
- **Source:** corpus synthesis: `EternityHorizonCapstone`, `OrbitFidelityRecurrenceExponent`, `SortedGapRatioGlobalExtremality`
- **Statement:** Every finite-time operator-norm tube around every finite Hermitian Hamiltonian of dimension at least three contains two commuting simple-spectrum Hamiltonians with one common orthonormal eigenbasis such that every normalized state cyclic in that basis has recurrence exponent zero for one Hamiltonian and the maximal physical survival-fidelity first-return exponent for the other.

## Goal

Prove a physical identifiability no-go stronger than exact periodic-versus-aperiodic instability:
no finite-duration experiment, even one controlling the full propagator in operator norm and keeping
the prepared cyclic state fixed, can determine the asymptotic survival-fidelity first-return exponent.

## Gates

- [x] 0 → 1 in-progress: well-posed; corpus ingredients located; exact literature searches found recurrence bounds and experimental proposals but no same-state finite-horizon exponent-instability theorem
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake env lean`, targeted `lake build`, axiom audit
- [x] 3 → 4 publication-ready: integrated as one central law and one flagship falsification protocol

## Exact conjecture

Let `D=e+3`, let `A` be any Hermitian `D×D` matrix, and let `T,η,t₀>0`. There exist Hermitian
matrices `Bper,Bmax`, real spectra `Eper,Emax`, and one orthonormal basis `b` such that:

1. `Bper` and `Bmax` commute with `A` and with each other;
2. both spectra are simple and `b` is an eigenbasis for both;
3. both propagators remain within `η` of `exp(-itA)` for every `|t|≤T`;
4. `Eper` has a positive exact projective period;
5. the sorted projective gap-ratio packet of `Emax` is not very well approximable;
6. for every normalized `Ω` with nonzero overlap against every vector of `b`,
   `log τ_per(δ)/log(1/δ)→0` and
   `log τ_max(δ)/log(1/δ)→(D-2)/2` as `δ↓0`, where `τ` is the first time after `t₀` at which
   survival-fidelity deficit is below `δ`.

## Approach

1. Periodic branch: dense simple rank-one gap packets.
2. Maximal branch: global nullity of the VWA sorted-gap-ratio locus for the full real diagonal
   spectral family; every positive-radius ball contains a simple non-VWA spectrum.
3. Transport both spectra through the same eigenvector unitary of `A`; this makes all three
   Hamiltonians simultaneously diagonal in one basis and turns spectral closeness into uniform
   finite-horizon propagator closeness.
4. Exact projective periodicity bounds every sufficiently accurate first return by one fixed
   positive period, while the cutoff bounds it below by `t₀`; logarithmic squeezing gives exponent
   zero.
5. Apply the proved cyclic-orbit fidelity exponent theorem to the non-VWA branch.

## Hostile attacks

- **Known Diophantine filling-time theory:** kills novelty of a mere finite-resolution calibration
  certificate, but does not state local non-identifiability of the physical first-hitting exponent.
- **Measured first-detection recurrence:** different process; repeated projective detection changes
  dynamics and its quantized mean return law does not imply this unmeasured survival-fidelity law.
- **State drift loophole:** closed by one shared eigenbasis and universal quantification over the
  same cyclic state.
- **Only pointwise finite-time agreement:** closed by uniform operator-norm agreement on the whole
  interval `[-T,T]`.
- **Aperiodic does not imply maximal exponent:** closed by selecting outside the VWA null set, not
  merely outside rational rank one.

## Preliminary novelty audit

- Gupta--Short (2026) gives fixed-system Dirichlet recurrence bounds.
- Campos Venuti (2015) gives generic crossing-density recurrence scales.
- Karimi--Wu--Cleland--Pekola (2026) proposes finite multiqubit recurrence experiments.
- Grünbaum--Velázquez--Werner--Werner and later first-detection work studies a monitored protocol.
- Dumas--Fischler gives optimal torus filling bounds under truncated Diophantine conditions.

No located source states the same-state, full-propagator finite-horizon non-identifiability of the
actual survival-fidelity first-return exponent. Novelty remains provisional until final
source-by-source theorem comparison.

## Paper proof `[PROVED HERE]`

Fix `D=e+3`, a Hermitian matrix `A`, and `T,η>0`. By the finite-dimensional spectral theorem,
choose one unitary eigenvector matrix `U` for `A`; write `λ` for the corresponding ordered real
eigenvalue tuple. Every real tuple `E` defines the transported Hamiltonian
`B(E)=U diag(E) U*`. All such matrices are Hermitian, commute with `A`, commute pairwise, and have
the same explicit orthonormal eigenbasis, namely the columns of `U`. Injectivity of `E` is exactly
simplicity of this displayed spectrum.

Choose radius `r=η/T`. Simple projectively periodic spectra are dense: approximate `λ` by a tuple
whose gaps are distinct integer multiples of one sufficiently small positive frequency. This gives
an injective tuple `Eper` inside the open `r`-ball and a positive time at which all its phases agree.
For the other branch, the full diagonal coefficient family escapes every nonzero balanced real
spectral relation. The global sorted-gap-ratio extremality theorem therefore says that, inside the
simple locus, spectra whose sorted anchored gap-ratio packet is very well approximable form a null
set. The simple locus is open and has full measure locally, so every positive-radius ball around
`λ` contains an injective tuple `Emax` outside that null set. Thus both selected spectra lie within
`r` of `λ`, while `Eper` is exactly projectively periodic and `Emax` has the sharp non-VWA packet.

Set `Bper=B(Eper)` and `Bmax=B(Emax)`. Spectral transport preserves the coordinatewise sup norm:
`‖B(E)-A‖=max_j |E_j-λ_j|`. Duhamel's bound for two Hermitian generators gives
`‖exp(-itB(E))-exp(-itA)‖≤|t|‖B(E)-A‖`. Hence for every `|t|≤T`, both differences are strictly
smaller than `T r=η`. This controls the complete propagator throughout the observation window, not
only finitely many samples or one prepared state.

Now fix any normalized state having nonzero overlap with every vector of the shared eigenbasis and
any cutoff `t₀>0`. On the periodic branch, let `R>0` be an exact projective period. Some integer
multiple `mR` lies beyond `t₀`, and survival-fidelity deficit at every such multiple is exactly
zero. Consequently its first return at any positive deficit threshold is bounded between `t₀` and
the fixed number `mR`. Dividing logarithms by `log(1/δ)→∞` squeezes the first-return exponent to
zero.

On the maximal branch, cyclicity makes every spectral weight strictly positive. The exact
cyclic-orbit comparison identifies small survival-fidelity deficit with squared projective phase
distance up to fixed positive constants. The non-VWA sorted gap-ratio theorem then gives projective
first-hit exponent `(D-2)` in phase resolution and therefore `(D-2)/2` in fidelity-deficit
resolution. Both conclusions hold for the same fixed state and the same shared eigenbasis. This
proves all clauses.

## Formalization

- Module: `GaloisForLFunctions.HTGeometry.PhysicalFirstReturnHorizonInstabilityLaw`
- Capstone: `exists_sameEigenbasis_periodic_and_maximalPhysicalReturn_uniform_horizon`
- Targeted source check: `lake env lean GaloisForLFunctions/HTGeometry/PhysicalFirstReturnHorizonInstabilityLaw.lean` passed without diagnostics.
- Targeted final build: `lake build GaloisForLFunctions.HTGeometry.PhysicalFirstReturnHorizonInstabilityLaw` passed.
- Axiom audit for capstone and three principal bridge theorems: only `propext`, `Classical.choice`,
  and `Quot.sound`; no project axioms or placeholders.
- Wired into `GaloisForLFunctions/HTGeometry.lean`; umbrella deliberately not built.
- Integrated as Theorem `Physical first-return horizon instability`, full appendix proof,
  abstract-level headline result, source-by-source literature comparison and full-process
  experimental stress test in `geometry-complexity-quantum-recurrence`.
- Publication PDF compiled to 49 pages without LaTeX warnings; title, architecture figure, theorem,
  experimental protocol, proof and references visually inspected without defects.

## Log

- 2026-08-28 — created in 1-in-progress after corpus-first and preliminary literature audit.
- 2026-08-28 — finite-resolution certificate candidate downgraded to `[BRIDGE]`; stronger same-state
  exponent-instability conjecture survives preliminary hostile attack.
- 2026-08-28 — complete paper proof closed; Lean capstone, targeted source check, targeted build and
  axiom audit pass; card promoted to 3-formalized.
- 2026-08-28 — theorem integrated as central Law IV boundary with full proof and experiment;
  publication artifact rebuilt and visually verified; card promoted to 4-publication-ready.
