# Global QFI failure at infinity

- **ID:** `qfi-global-failure-at-infinity`
- **Stage:** 5 — retired after corpus collision
- **Type:** FALSIFIED NOVELTY CLAIM / VALID RECEIVER
- **RH status:** exact reformulation only; no zero-support theorem

## Retired proposal

Use the direct integer amplitudes `n^(-s)` and reflected amplitudes `n^(s-1)`.  Require square
summability of each amplitude and its vertical logarithmic tangent.  The direct process is admitted
for `Re(s) > 1/2`, the reflected process for `Re(s) < 1/2`, and both fail exactly on the critical
line.  Every finite cutoff is admitted everywhere.  The intended RH bridge was to prove that
analytic-normalization failures occur only on this common infinite-process failure wall.

The elementary topology and its Lean implementation were correct.  They are removed because they
duplicate stronger existing corpus results and do not supply the missing bridge.

## Exact killing mechanism

1. `PrimeCoShiftModel` already proves the direct `n^(-s)` Hilbert threshold at `Re(s)=1/2`.
2. `PrimeClockScaleFactor` already proves the prime-coherent QFI threshold, its reflected
   double-failure formulation, and the exact RH equivalence obtained by quantifying that formulation
   over zeta zeros.
3. `ZetaFisherHorizon` already places the relevant boundary at infinite Fisher distance.
4. `ProjectiveFisherBlindness` and `PrimeFisherSuperspaceBlindness` prove that normalized Fisher
   data lose phase/divisor information.

Thus the proposed construction is an admission receiver.  Naming its summability condition “QFI
admission” does not create a new zero-occurrence mechanism.  Its open statement—every zeta zero lies
on the common wall—is RH itself with no independent source law.

## Hostile pivots and their outcomes

- **Competing decay-rate ends:** rejected.  The corpus already contains logistic completion laws,
  shrinking-source Fisher boundary limits, and soft/hard Fisher synchronization.  A rate tie selects
  the line but does not cause zeros.
- **Projective exceptional fibers of several outputs:** rejected when outputs share one analytic
  factor.  Homogeneous normalization removes that factor, so its zeros cannot change the resulting
  projective state away from the undefined point.
- **Reflected split-versus-collided failures:** rejected.  Arithmetic constraint hyperdescent and
  the oriented reflection quotient already formulate off-line failures as split reflected fibers.
- **Infinite prime-product sectors:** rejected.  The prime Hellinger/Kakutani sector fracture and
  its orientation refinement are already fully developed in the corpus.
- **Several periodic zero-mean dilation streams:** rejected.  Their transforms all contain the same
  zeta factor, so homogeneous normalization removes the purported joint failure.  The corpus also
  already computes common-factor Koszul homology.
- **Finite analytic projective punctures:** rejected.  Removing the least common vanishing order
  extends the projective map through the common zero.
- **A local full-rank hit on a mixed-state boundary:** rejected.  A boundary coordinate has an
  interior extremum at such a hit, forcing differential-rank loss; assuming full QFI rank would
  assume away the event.
- **Generic failure nerve:** rejected.  Existing failure-nerve constructions already own this
  incidence mechanism, and no generic nerve supplies zero occurrence.
- **Gauss--Bonnet defect counting:** rejected.  A global defect count cannot distinguish an
  off-line reflected pair from two fixed-line defects, and it still lacks a source occurrence law.

Each failure has the same route-level meaning: infinity, reflection, or QFI can classify the
critical wall without explaining why arithmetic zero occurrence is confined to it.

## Strongest survivor

A new information-geometric RH route must satisfy all three conditions before further formal work:

1. **Source independence:** its multiple processes are not scalar multiples, reflected copies, or
   invertible reconstructions of one record.
2. **QFI-essential topology:** deleting QFI changes the global topological obstruction; ordinary
   summability, projectivization, or a rate comparison cannot already prove the same statement.
3. **Pre-divisor coupling:** a source theorem, stated before selecting a zeta zero, forces actual
   analytic-normalization failure to land in the joint process-failure locus.

No surviving construction currently meets all three.  This is a closed no-go, not evidence against
RH or against every possible information-geometric approach.

A distinct survivor is now tracked in
[Failed quantum Fisher multi-law end topology for RH](quantum-fisher-multilaw-end-topology-rh.md).
It does not reuse the retired admission wall.  Exact finite convolution now splits the raw gluing
defect into complete rectangle overflow and continuation--recovery interaction.  Their total tends
to `-1` at every nontrivial zero, unconditionally in Lean.  Every fixed finite logarithmic jet
repair also fails.  Strict-left simultaneous source escape is now Lean-proved and occurs in every
off-critical zero orbit.  The next attempted inference also failed: cofinal spikes do not fill an
antidiagonal circle, and the finite mixed-qubit QFI completion has ordinary closed-disk topology.
The only survivor is a possible QFI metric on the canonical cutoff history whose completion can be
proved to differ from trace-norm or radial completion.  Compactifying endpoint values alone would
repeat this retired route's error.

## Formal cleanup

The duplicate module `RHTower/DirichletQFIGlobalFailureTopology.lean` and its umbrella import were
removed.  Existing stronger modules retain every mathematical fact used in the collision audit, so
the cleanup loses no frontier theorem.
