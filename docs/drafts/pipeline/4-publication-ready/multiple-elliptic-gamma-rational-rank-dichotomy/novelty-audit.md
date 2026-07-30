# Novelty audit: universal quantum-recurrence information law

Cutoff: 30 July 2026.

## Audit rule

Scientific novelty is measured exclusively against externally available
literature.  This repository is not a priority comparator.  Internal overlap
is used only to recover dependencies, avoid repeating failed work, and check
that the final theorem is proved.  An internally unprecedented statement may
be externally known; an internally established statement may still be
externally new.  These are separate audits:

- **internal closure:** every manuscript claim follows from completed proofs;
- **external priority:** no earlier public source contains the same theorem
  or a theorem that immediately subsumes it.

No novelty verdict below may cite absence from, or presence in, the internal
corpus as evidence.

## Candidate contribution

Novelty cannot rest on any of these ingredients separately:

- survival probability is the Fourier transform of the energy
  autocorrelation;
- survival probability is even in time;
- a random clock filters energy gaps by its characteristic function;
- uniform windows produce sinc factors;
- characteristic functions determine probability measures;
- moments determine probability measures supported on `[0,1]`;
- long-time survival moments are zero-sum energy-collision probabilities.

Each is known or classical. The candidate contribution is the exact joined
classification:

1. arbitrary probability energy laws and arbitrary probability clock laws
   obey one all-order Fourier reciprocity;
2. the full moment hierarchy determines the complete sampled-return law;
3. the energy autocorrelation is the exact maximal system quotient seen by
   all probability clocks;
4. clock symmetrization is the exact maximal clock quotient seen by all
   probability spectra;
5. universal equivalence of complete return laws collapses to deterministic
   first moments on the system side and balanced two-level first moments on
   the clock side;
6. countable dense rational schedules already suffice for both complete
   universal equivalence tests;
7. pure-point aliases, temporal rank, analytic wall crossing, local
   visibility, and long-time collision laws are derived as refinements of the
   same pairing.

## Closest known results

- Wiener–Khinchin theory and the survival-probability literature identify the
  fixed-time cosine-transform relation between survival probability and
  energy autocorrelation.
- Ramírez Jiménez and Kelkar, *Phys. Rev. A* **104**, 022214 (2021), state
  this survival/autocorrelation transform explicitly.
- Xuereb et al., *Phys. Rev. Lett.* **131**, 160204 (2023), use the
  characteristic function of an arbitrary tick distribution to describe
  imperfect-timekeeping dephasing of energy gaps.
- Xu et al., *Phys. Rev. A* **103**, 032207 (2021), treat decoherence from
  realistic clocks.
- Friedman, Kessler and Barkai, *Phys. Rev. E* **95**, 032141 (2017), study
  fixed-period detection resonances.
- Mark et al., *Phys. Rev. X* **14**, 041051 (2024), use finite temporal
  ensembles and sinc-filtered energy combinations.
- Riddell and Pagliaroli, *J. Stat. Phys.* **191**, 144 (2024), analyze
  finite-order no-resonance conditions and pseudo-resonances.
- Mark et al., *Phys. Rev. Lett.* **131**, 110601 (2023), derive
  sample-efficient benchmarking from universal late-time fluctuations under
  a `k`th no-resonance assumption.  They say the assumption is expected for
  generic ergodic Hamiltonians; they do not prove it for a tensor-local
  Hamiltonian family.
- Mark et al., *Phys. Rev. X* **14**, 041051 (2024), identify the infinite
  temporal ensemble with the random-phase ensemble under all finite
  no-resonance conditions modulo degeneracies.  They describe generic
  validity and resonance breaking by small perturbations as a belief.  A
  proof for almost every bounded-range static chain would discharge the
  load-bearing premise of that theorem.
- Classical phase retrieval and diffraction theory identify autocorrelation
  or homometry as the information retained by Fourier magnitudes.
- Classical probability supplies characteristic-function uniqueness and
  compact moment determinacy.
- Campos Venuti, *The recurrence time in quantum mechanics* (2015),
  already obtains generic doubly-exponential recurrence scaling in system
  volume and exponential scaling for integrable quasi-free models.  Any
  headline based only on recurrence scarcity or double-exponential time is
  therefore unavailable.
- Kotowski and Oszmaniec, *Tight bounds on recurrence time in closed quantum
  systems* (accepted in *Physical Review Letters*, 23 June 2026), prove
  dimension-dependent upper bounds of the form
  `t_rec ≲ t_exit(ε)(1/ε)^d` and generic saturation for random Hamiltonians.
  A new paper must distinguish a structural locality mechanism from their
  quantitative recurrence-time bounds.
- The connectivity and two-component parity law for categorical/Kronecker
  graph products is classical, going back at least to Weichsel (1962).
  Connectivity of the interaction lift is an input, not a novelty claim.

## Exact difference claimed

The manuscript does not claim those parents as new. It claims one maximal
two-sided inverse theorem for the complete return distribution:

- sufficiency and necessity of the system gap law after quantifying over all
  clocks;
- sufficiency and necessity of the clock orientation quotient after
  quantifying over all spectra;
- balanced two-level and deterministic first-moment probe completeness;
- all-orders/full-law extension for arbitrary spectral type and arbitrary
  probability clocks.

Targeted searches did not locate this exact double maximal quotient or its
minimal-probe collapse. Search absence is not proof of priority.

## Kill tests

The novelty claim is killed if prior work proves an equivalent statement
containing either:

1. equality of energy autocorrelations iff equality of complete
   survival-return distributions under every random clock; or
2. equality of symmetrized clock laws iff equality of complete
   survival-return distributions for every probability spectrum, with
   balanced two-level first moments sufficient.

The broad “universal law” framing is also killed if the pure-point, local,
and infinite sections are merely juxtaposed rather than logically derived
from the same quotient/pairing.

## Present verdict

**Priority: plausible but not certified.**

**Mathematical originality risk: high.** The double maximality proof is short
because it composes classical Fourier uniqueness, time-reversal evenness, and
compact moment determinacy. A referee may reasonably judge the result an
elegant synthesis rather than new mathematical depth.

**Physics originality risk: high.** Qubit noise spectroscopy and Ramsey
interferometry already reconstruct characteristic functions. The paper must
show that complete-return equivalence and the exact information boundary
change a live inference problem, not merely rename cosine-transform
tomography.

The stronger local-interaction theorem under internal development—generic
nearest-neighbour coupling opens `q^n - 1` projective temporal directions and
minimizes every replica collision moment—would materially change the
manuscript's scientific content.  Whether it is novel depends only on the
external-priority audit.  It is not authorized for the manuscript until its
physical local-Hamiltonian generator is fully formalized.

## Revised candidate after hostile audit

The only candidate that survives the comparisons above is not a new
recurrence-time estimate.  It is an exact relation-kernel mechanism:

1. one projective character relation space controls operational temporal
   dimension, indistinguishable phase histories, and every replica-collision
   correction to return statistics;
2. arbitrary observer action quotients that same relation space and thereby
   determines every finite return moment, not only the quadratic mean;
3. local interaction changes the relation space through an exact response
   kernel whose quotient by the trace direction is reduced `H^0` of the
   interaction lift;
4. when that reduced cohomology vanishes, the interaction removes every
   nontrace spectral relation and forces simultaneous all-order collision
   extremality.

The graph theorem and the collision floor are known ingredients.  Candidate
novelty is the proved chain

`local spectral response kernel = reduced H^0`
`→ projective relation erasure`
`→ observer-dependent temporal dimension`
`→ complete all-order recurrence law`.

This chain is not yet authorized as the paper's claim.  It still requires:

- the all-order observer-action recurrence projection;
- a fully formal local-Hamiltonian genericity theorem rather than an abstract
  transition-graph hypothesis;
- a finite-horizon observable that separates the resulting universality
  classes;
- a fresh priority search aimed at equivalent relation-kernel formulations,
  not only recurrence-time literature.

**Revised verdict: potentially deep, presently incomplete.**  Calling the
existing manuscript a universal law would still overstate the result.

## External-priority update: live premise discharge

The nearest-neighbour maximal-rank theorem has a more direct external target
than the earlier recurrence framing.  Current quantum-dynamics papers use
the hierarchy
\[
 \sum_{a=1}^{k}E_{i_a}=\sum_{a=1}^{k}E_{j_a}
 \Longrightarrow
 \{i_1,\ldots,i_k\}=\{j_1,\ldots,j_k\}
\]
as a premise for random-phase temporal ensembles, Porter--Thomas
fluctuations, deep thermalization, and fidelity benchmarking.  External
sources characterize it as expected, believed, numerically observed, or
assumed for generic ergodic Hamiltonians.  The targeted local theorem would
instead prove, simultaneously for every finite `k`, that the premise holds
for Lebesgue-almost every inhomogeneous nearest-neighbour qudit chain.

This comparison changes the significance test:

- **not new:** consequences obtained after assuming no resonance;
- **candidate new:** tensor-local interaction is proved to generate all-order
  no resonance generically despite only polynomially many local controls and
  exponentially many many-body energies;
- **direct physics advance:** several existing temporal-ensemble and
  benchmarking theorems become unconditional on this broad physical
  Hamiltonian class;
- **remaining limitation:** exact nonresonance is asymptotic and does not
  bound finite-time near-resonance resolution.

Targeted searches have not yet found an external proof of generic maximal
projective rational rank for the same nearest-neighbour qudit family.
Search absence is not priority certification; references cited by the
benchmarking and temporal-ensemble papers must still be chased individually.

## 30 July 2026 external-priority checkpoint

The latest targeted external search reinforces, but does not certify, the
premise-discharge gap:

- Riddell--Pagliaroli explicitly describe higher no-resonance as usually
  assumed for quantum-chaotic models, study numerical/random-matrix
  statistics and near violations, and weaken downstream equilibration bounds
  when violations occur. They do not prove all-order nonresonance for a
  bounded-range local family.
- Mark et al. prove random-phase temporal-ensemble conclusions under all
  finite no-resonance conditions modulo degeneracy and describe generic
  resonance breaking as a belief. Their theorem makes the premise important;
  it does not discharge it for local chains.
- Keating--Linden--Wells prove Gaussian limiting spectral density and
  eigenstate statements for broad nearest-neighbour spin-chain classes. Their
  theorems concern density of states and entanglement, not exact rational
  independence of the complete finite-size spectrum.

No internal repository fact enters those comparisons.

Formal progress now proves a stronger abstract extension statement than the
earlier one-relation result: one real Hermitian tensor-local extension
simultaneously eliminates every nonzero balanced integer spectral relation
and yields a simple maximally projective real spectrum. This is proof status,
not novelty evidence.

The finite-observable locality mismatch is now formally closed.  Given any
finite Hermitian endpoint-observable family whose union transition graph has
connected interaction lift, one real linear combination preserves every
detected transition edge.  Its energy-basis matrix is therefore the single
Hermitian channel consumed by the tensor-local extension theorem, while the
operator itself remains endpoint-local.  This is proof status, not novelty
evidence.

The remaining mathematical authorization gap is the full path theorem: the
endpoint-observable witness must be carried through every chain length and
local alphabet, and the exceptional set must be proved null and nowhere
dense in the complete nearest-neighbour Hamiltonian parameter space.  Until
that is closed, the manuscript may not claim generic nearest-neighbour
maximal rank.

External comparison also found two sharper boundary markers:

- a 29 August 2024 research talk at `quantumstat.es` explicitly asks
  “Are eigenenergies of generic 2-body Hamiltonians rationally independent?”
  and restates the question as whether hidden energy resonances occur in
  every two-body Hamiltonian.  This is evidence that the target answers a
  live community question, not evidence of priority by itself;
- Poláčik--Valdebenito (2019) prove generic rational independence for bound
  eigenvalues of radial Schrödinger operators.  Their infinite-dimensional
  potential class is an important mathematical predecessor, but it neither
  proves nor implies the finite tensor-product, bounded-range many-body
  result;
- Riddell--Bertini (2024) construct rationally independent
  **single-particle** free-fermion energies using special local hopping.
  The additive many-body spectrum retains free-model structure, so this is
  not the claimed full interacting many-body projective-rank theorem.

Priority remains unverified until searches and citation chains are exhausted.
