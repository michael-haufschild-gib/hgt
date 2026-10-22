# Observer-action visibility-cone law

- **ID:** `observer-action-visibility-cone-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / FILTERED SPECTRAL GEOMETRY / QUANTUM RECURRENCE
- **Source:** observer-time ensemble cascade, local connected-packet laws,
  recurrence distribution, and replica-height corpus
- **Statement:** A spectral relation is observable exactly through the
  dimensionless action accumulated along that relation; analytic activation,
  spatial locality, temporal dimension, and recurrence-replica order are
  projections of one filtered projective-character geometry.

## Goal

Replace the recurrence-paper collage by one canonical object and one
necessary-and-sufficient law.

For a spectrum \(\omega_x\), observation clock \(T_x\), and projective
character \(k\), define the observer action
\[
  A_k(x)=T_x\langle k,\omega_x\rangle .
\]
The time-sampled phase law exists exactly when
\(\operatorname{sinc} A_k(x)\) converges for every finite spectral character.
Those limits uniquely determine the complete probability law. All retained
results must be derived from this character transform.

The new filtered object has two coordinates on the same character:

1. **activation valuation** \(v(k)\): first weak-interaction order at which
   \(\langle k,\omega_g\rangle\) is nonzero;
2. **replica height** \(h(k)=\sum_i(k_i)_+\): first fidelity-moment order in
   which \(k\) can occur.

At inverse-power observation order \(r\) and replica order \(m\), the
observable character region is the visibility cone
\[
  v(k)\le r,\qquad h(k)\le m.
\]
Local connected-cluster geometry supplies the causal lower face
\[
  v(k)\ge \operatorname{SteinerCost}(k).
\]
For a nondegenerate Boolean relation on \(s\) genuinely changed sites, the
second coordinate is explicit:
\[
  h(k_S)=2^{s-1}.
\]
Hence every such active local relation has the attained corner
\[
  \bigl(v(k_S),2^{s-1}\bigr),\qquad
  v(k_S)\ge \operatorname{SteinerCost}(S).
\]

## The jump

Prior work treated recurrence time, spectral form factors, perturbative
resonance breaking, observer-dependent temporal dimension, and local
connected-cluster cancellation as separate questions. They use the same
projective spectral character without identifying it:

```text
local interaction graph
        |
        v
activation valuation v(k) ---- observation clock ----> action A_k
        |                                                |
        |                                                v
        +---- zero-action constraints ------------> phase law
                                                         |
                         +-------------------------------+------------------+
                         |                               |                  |
                         v                               v                  v
                 temporal dimension             recurrence/SFF      target geometry
                 (quotient rank)               (Fourier polynomial) (information)
```

The missing object is the filtered projective-character lattice. Observation
time is dual to its activation filtration; recurrence order is dual to its
replica-height filtration. Failures of finite history, finite perturbation
theory, or low-order spectral form factors are attempts to infer characters
outside the accessible cone.

## Exact theorem surface already closed

Unconditionally proved internally:

1. finite and countably infinite phase-law existence is equivalent to
   convergence of every sinc-transformed observer action;
2. the limit law is unique and determines every continuous phase statistic;
3. zero-action characters are exactly the almost-sure phase constraints;
4. temporal dimension plus zero-action constraint rank equals total
   projective rank;
5. analytic paths produce a complete Fourier--valuation atlas, and the atlas
   reconstructs every active character's exact birth order;
6. every finite weighted return/SFF statistic is a polynomial projection of
   the same action profile;
7. a balanced character's exact minimum recurrence-replica order is its
   positive coefficient mass;
8. Hermitian local interaction forces each site-Möbius character to remain
   constrained below every certified weighted connected-spanning cost;
9. contractive scalar semigroup modes obey the corresponding complex-action
   kernel law;
10. weak-coupling and long-observation limits do not commute, while their
    joint scaling yields the full boundary profile.
11. a nondegenerate Boolean site relation on \(s\) changed sites has exact
    minimum fidelity-replica height \(2^{s-1}\), so the local visibility cone
    has an explicit exponential detector coordinate.

## Open core

1. Extend replica-height language from finite spectra to arbitrary
   finite-support characters on countable spectra.
2. Derive terminal target-volume/rate-distortion results from the same phase
   law rather than citing them beside it.
3. Decide the maximal honest open-system scope: scalar contractive modes,
   finite contractions, or a full probability-law theorem for normal
   semigroups.
4. Audit whether the action/visibility-cone formulation is absent from
   singular perturbation, spectral-form-factor, dynamical-systems, and
   compact-group literature.

## Falsifiers

Reject the master-law claim if any occurs:

1. recurrence or information result cannot be written as a continuous
   statistic or target of the same limiting phase law;
2. locality applies to a contrast only analogous to, rather than identical
   with, the projective character in the action law;
3. replica height does not characterize the first moment order containing
   that character;
4. a literature theorem already gives the same complete arbitrary-clock
   action criterion plus valuation, locality, rank, and replica consequences;
5. continuous spectrum, thermodynamic limits, gravity, or nonlinear open
   dynamics are claimed without an exact extension theorem.

## Gates

- [x] 0 → 1: well-posed canonical object, exact falsifiers, attack route
- [x] exact visibility-corner theorem proved
- [x] local space--time--replica visibility-cone theorem proved
- [x] exact \(2^{s-1}\) Boolean replica-height law proved
- [ ] 1 → 2: dependency-closed integration with terminal information law
- [ ] 2 → 3: new modules compile, axiom audit, formal lint
- [ ] 3 → 4: one-law manuscript, priority audit, hostile Nature review

## Approach

1. Define projective-character replica height.
2. Combine phase-atlas tomography with the exact minimum-replica theorem.
3. Transfer the local weighted Steiner lower bound to the same character.
4. Express recurrence polynomials and terminal target information as
   functionals of the action-selected phase measure.
5. Keep arbitrary clocks as the master theorem; use analytic valuation only
   as the calculable local-Hamiltonian chart.

## Hostile boundary

- The harmonic-analysis existence equivalence alone is too elementary for a
  major journal.
- Noncommuting weak/long-time limits alone are also elementary.
- Scientific content must be the exact causal composition: local interaction
  geometry fixes activation valuation; observer time selects a quotient;
  replica order selects detector complexity; recurrence and information are
  forced projections.
- “Temporal dimension” is phase-hull rank, never spacetime dimension.
- No black-hole or cosmological claim is permitted without an instantiated
  physical Hamiltonian or field-theory theorem.

## Log

- 2026-07-30 — arbitrary-clock necessary-and-sufficient observer-action law,
  rank conservation, recurrence projection, contractive-mode extension, and
  singular boundary proved.
- 2026-07-30 — filtered-character visibility cone identified as candidate
  master invariant replacing the earlier recurrence anatomy.
- 2026-07-30 — proved exact Boolean local replica height \(2^{s-1}\) and
  integrated it with the connected-spanning temporal floor into an attained
  explicit space--time--detector corner.
- 2026-08-01 — closed finite-dimensional deterministic open-system escape:
  an explicit normalized reset-noise Kraus channel approximates every finite
  unitary history below arbitrary operational tolerance yet drives every
  pair of initial states to zero operational distance.  Combined with the
  angular perturbation theorem, one common finite diagonal reference admits
  this total-forgetting completion and unitary completions of every exact
  temporal rank \(1\le k\le d\).  Formal sources:
  `FiniteKrausRecurrenceFutureFanLaw.lean` and
  `OperationalQuantumRecurrenceFutureFanLaw.lean`; capstone axiom audit uses
  only `propext`, `Classical.choice`, and `Quot.sound`.
