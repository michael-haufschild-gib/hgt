# Preliminary novelty audit

Date: 14 August 2026. Status: external priority audit incomplete. No `first`, `unprecedented`, or `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` claim is authorized yet.

## Closest literature

1. Bocchieri--Loinger proves finite-dimensional quantum recurrence existence, not local-network temporal rank, graph reconstruction or circuit capacity.
2. Campos Venuti (2015), Kotowski--Oszmaniec (arXiv:2601.10409v3) and Gupta--Short (PRA 114, 012208; arXiv:2604.14995) study quantitative recurrence times. They do not supply the arbitrary-graph rank atlas, all-order factorization law, static Choi plateau or hard recurrence polygons.
3. Riddell--Bertini (PRE 110, 064101; arXiv:2404.12100) constructs rationally independent local free fermions and studies form-factor moments. This is closest to spectral arithmetic, but remains a special free-fermion family and retains many-body additive relations. Current graph theorem covers generic interacting onsite-plus-edge Hamiltonians on arbitrary finite graphs and eliminates all nontrivial balanced relations in each connected component.
4. Oszmaniec--Kotowski--Horodecki--Hunter-Jones (PRX 14, 041068; arXiv:2205.09734) proves complexity saturation and recurrence for random circuits and stochastic local Hamiltonian evolution. Current completed-time plateau concerns one deterministic time-independent local Hamiltonian after generic spectral maximality; it does not provide their finite stochastic mixing bounds.
5. Brown--Susskind (PRD 97, 086015; arXiv:1701.01107) motivates growth--plateau--recurrence. Current paper proves completed-time plateau, hard late cycles and return reflection, not initial linear growth or first recurrence time.
6. Cui--Schuster--Mao--Huang--Brandao (arXiv:2510.08434) proves constant-local time-independent Hamiltonian ensembles remain efficiently distinguishable from Haar and fail to form a 2-design. Permanent non-Haar separator in this manuscript is attributed to that work; novelty, if any, is coexistence with internally proved hard polygons and completed-time capacity, not the separator.
7. Nayak--Sen (QIC 7, 103--110; quant-ph/0605041) supplies the classical CPTP-inverse classification used by exact Markovian rigidity.
8. Jia--Wolf (CMP 402, 141--156; arXiv:2205.06977) constructs explicit constant-description families with exponential exact complexity and approximate hardness for most family parameters. It does not place the hard state at a common autonomous time on a bounded nearest-neighbour orbit from one fixed product input.
9. Ippoliti (arXiv:2606.30635) proves a random-matrix spectral ramp for a static geometrically local clock embedding. Current component theorem is instead an exact completed-time collision/factorization law; no finite-time ramp is claimed.

## Candidate priority residues

### A. Arbitrary-graph temporal curvature

Exact residue: generic formula
`tau(H)=sum_C(prod_{v in C} q_v - 1)` for arbitrary onsite-plus-edge local Hamiltonians, plus simultaneous subsystem atlas and reconstruction `edge iff kappa(u,v)>0`.

Preliminary verdict: `SURVIVES PRELIMINARY ATTACK`; `[LEAN-PROVED] [NOVELTY UNVERIFIED]`.

Remaining audit: inverse spectral graph reconstruction, generic nonresonance for interacting local Hamiltonians, algebraic spectral independence, quantum-control transition-graph criteria, and citation descendants of Riddell--Bertini.

### B. Interaction/factorization collision equivalence

Exact residue: joining components creates `(A-1)(B-1)` projective phase directions and, at every replica order, replaces equality of marginal histograms by equality of the joint histogram. Fixed-component form factor tends to product of exponentials.

Preliminary verdict: torus factorization is `[BRIDGE]`; exact all-order collision interpretation is `[LEAN-PROVED] [NOVELTY UNVERIFIED]`.

### C. Deterministic static-local completed-time Choi plateau

Exact residue: generic connected arbitrary-graph local Hamiltonians, no Haar eigenbasis/design/mixing, upper completed density of short-circuit Choi endpoints bounded by target count times explicit phase-tube mass.

Preliminary verdict: `SURVIVES PRELIMINARY ATTACK`; exact arbitrary-graph composition currently `[PAPER-PROVED]`, ingredients `[LEAN-PROVED]`.

Distinction from PRX 2024: deterministic completed-time occupation rather than stochastic finite-time mixing. Distinction from Cui et al.: complexity lower bound coexists with permanent non-Haar structure.

### D. Prime-torsion hard return polygons

Exact residue: one fixed ordinary local Hamiltonian shadows all `p-1` circuit-avoiding vertices and returns near identity at the `p`th slice, with syndetic base times and arbitrary finite normalized-ray targets under explicit replica budget.

Preliminary verdict: `SURVIVES PRELIMINARY ATTACK`; `[LEAN-PROVED] [NOVELTY UNVERIFIED]`.

Remaining audit: fractional revival, perfect state transfer, cyclic/Floquet recurrences, complexity recurrence, finite-grid spherical codes and torsion-orbit avoidance.

### E. Return reflection and Markovian recovery

Exact residue: robust shell-by-shell circuit incidence reflection and simultaneous intermediate-time recovery with a common endpoint defect.

Preliminary verdict: group/semigroup identities are `[BRIDGE]`; exact quantitative composition `[PAPER-PROVED] [NOVELTY UNVERIFIED]`. Do not headline until formalization and priority audit close.

### F. Fixed-input common-time static complexity

Exact residue: for an ordinary Gaussian nearest-neighbour two-local path and one fixed product input, a positive ensemble fraction is exponentially hard at an unbounded sequence of common deterministic times; strict margins yield rational Hamiltonian--time witnesses selected by one total algorithm.

Preliminary verdict: `SURVIVES PRELIMINARY ATTACK`; `[PAPER-PROVED] [NOVELTY UNVERIFIED]`. The result is an existence/common-time theorem, not a first-onset bound, efficient construction, typical late-time tail, or Brown ramp.

Remaining audit: autonomous state-complexity lower bounds, explicit local Hamiltonian constructions, non-fast-forwarding, computable versus efficiently constructible circuit lower bounds, and citation descendants of Jia--Wolf and PRX 2024.

## Novelty killed or downgraded

- Compact-hull equidistribution: classical bridge.
- Target union bound: elementary bridge.
- Trace-monoid heap enumeration: classical mechanism; quantum-capacity application provisional.
- Permanent constant-local Haar separation: literature result of Cui et al.
- Exact CPTP recurrence implies unitarity: classical inverse-channel consequence.
- Global static-ensemble Haar coverage no-go: strictly subsumed as headline by Cui et al.; retain only as supporting quantitative geometry.

## Required before submission

1. Complete two-database search and citation ancestry/descendancy for candidates A--E.
2. Normalize terminology against inverse spectral, controllability, fractional revival and complexity literature.
3. Obtain independent specialist review of arbitrary-graph proof and prime-polygon budget.
4. Formalize exact manuscript composition for static arbitrary-graph plateau and all paper-only Law IV theorems.
5. Formalize the fixed-input incidence and computable-witness theorem.
6. Recheck every bibliography item against final published metadata.
