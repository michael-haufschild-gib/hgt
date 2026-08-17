# What this paper says in plain language

Quantum systems do not simply “forget” their beginnings. In a finite isolated
system, motion can eventually return close to an earlier state. What controls
those returns is not only energy scale or system size, but exact arithmetic
relations among energy levels.

Paper identifies one common structure behind several apparently different
questions:

- Loss decides which part of a system survives long enough to recur.
- Exact spectral relations decide how many independent phases govern its
  long-time motion.
- Measurement decides which of those phases are visible.
- Finite observations cannot, in general, determine complete long-time
  recurrence geometry.

This explains a counterintuitive effect. An interaction can be so weak that no
bounded-duration experiment can distinguish it from zero, yet it can remove
exact energy relations and completely reorganize system's infinite-time
behavior.

## Main new results

For generic static one-dimensional nearest-neighbour qudit chains, paper proves
all projective phase directions allowed by Hilbert space are present. Their
global return density is then known exactly and vanishes doubly exponentially
with chain length when long-time averaging is completed at each finite size
before size is increased.

For any finite Hermitian Hamiltonian and any chosen finite collection of
physical measurement probabilities, paper proves a direct observed-record
law. Either record never leaves chosen tolerance band, or same record later
returns after a witnessed exit. Deadline is compressed according to
coherences measurements can actually see.

Paper also gives one explicit static nearest-neighbour qubit chain whose
two-qubit-gate complexity lies between linear bounds over a controlled time
window, returns exactly to identity, and has a reflected complexity history.
It disproves literal point-by-point monotonicity: complexity can drop between
two nearby increasing times even inside linear-envelope window.

Finally, one explicit infinite diagonal l-bit field has a well-defined
self-adjoint Hilbert-space Hamiltonian, strongly continuous unitary dynamics,
uniform finite-volume completion, and phase structures appearing at every
spatial scale.

## Scientific contribution

Known recurrence theorems establish that returns occur and recent work bounds
state recurrence times. This paper adds structural laws connecting recurrence
to loss, interaction topology, chosen observers, circuit targets,
thermodynamic scaling and limits of prediction. Its most defensible new
contributions are joined theorems:

1. full projective recurrence rank inside ordinary static bounded-degree local
   many-body Hamiltonian families;
2. same-observer Born-record escape and return with an observer-specific
   certified deadline;
3. exact finite-size-to-thermodynamic return-density law;
4. explicit static local complexity ramp, return, reflection and certified
   nonmonotonicity.

## What paper does not claim

It does not give first-return time from inverse return density. It does not
claim Haar randomness, universal monotone complexity, microscopic
many-body localization, or global recurrence of an infinite system.
Thermodynamic density result takes long-time limit first at each finite size.
