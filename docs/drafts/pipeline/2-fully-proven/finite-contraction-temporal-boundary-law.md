# Finite-contraction temporal-boundary law

- **ID:** `finite-contraction-temporal-boundary-law`
- **Stage:** 2-fully-proven
- **Type:** OPEN-DYNAMICS THEOREM / OPERATIONAL MEMORY LAW
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [EXTERNAL PRIORITY OPEN]`
- **Parent conjecture:**
  `../1-in-progress/temporal-atlas-relativity-conjecture.md`

## Exact theorem

Let \(H\) be a finite-dimensional complex Hilbert space and
\(T:H\to H\) a contraction. Let \(P_{\mathrm{per}}\) be the orthogonal
projection onto the direct sum of eigenspaces whose eigenvalues have modulus
one. Then, for every \(x\in H\),
\[
 \left\|
   T^n x-T^nP_{\mathrm{per}}x
 \right\|
 \longrightarrow0.                                  \tag{1}
\]
For every \(n\),
\[
 \left\|T^nP_{\mathrm{per}}x\right\|
 =
 \left\|P_{\mathrm{per}}x\right\|.                   \tag{2}
\]
For every pair \(x,y\in H\),
\[
 \|T^nx-T^ny\|\longrightarrow0
 \quad\Longleftrightarrow\quad
 P_{\mathrm{per}}(x-y)=0.                           \tag{3}
\]

Thus every orbit approaches a canonical norm-preserving peripheral orbit,
and the kernel of \(P_{\mathrm{per}}\) is exactly the information forgotten
asymptotically.

## Dependency-closed proof

The peripheral eigenspaces of a finite contraction are mutually orthogonal,
reducing, and have semisimple unit-modulus eigenvalues. Their orthogonal
complement is invariant. The spectrum of the restriction of \(T\) to that
complement lies strictly inside the unit disk, so its powers converge to
zero in operator norm.

Write
\[
 x=P_{\mathrm{per}}x+(I-P_{\mathrm{per}})x.
\]
Applying \(T^n\) gives
\[
 T^nx-T^nP_{\mathrm{per}}x
 =
 T^n(I-P_{\mathrm{per}})x.
\]
The right-hand side tends to zero, proving `(1)`.

On each peripheral eigenspace, \(T^n\) multiplies by a scalar of modulus
one. Orthogonality of distinct peripheral eigenspaces therefore preserves
the sum of squared component norms and proves `(2)`.

Apply the norm convergence law to \(x-y\):
\[
 \|T^nx-T^ny\|
 =
 \|T^n(x-y)\|
 \longrightarrow
 \|P_{\mathrm{per}}(x-y)\|.
\]
The limit is zero exactly when its projected vector is zero, proving `(3)`.

## Physical interpretation permitted by the theorem

For a finite contractive discrete-time model:

- the transient part is a one-way approach direction;
- the peripheral part is the exact non-decaying asymptotic motion;
- asymptotic operational memory is precisely peripheral memory; and
- complete forgetting is an exact kernel property, not merely small late
  signal.

Calling the peripheral orbit a **recurrent future boundary** is an
interpretation of `(1)`--`(2)`. The theorem does not yet identify its orbit
closure, topological dimension, invariant measure or return distribution.

## Hostile boundary

1. This is finite-dimensional and discrete-time.
2. A contraction on Hilbert space includes useful open-system
   representations but is not itself every quantum channel.
3. Peripheral/transient decompositions and decoherence-free asymptotic
   sectors are established literature. Novelty cannot be claimed for that
   decomposition alone.
4. The theorem does not define an operational horizon between spatial
   observers.
5. A small nonzero late signal is not distinguished here from a permanent
   nonzero signal at finite resource.
6. No black-hole, gravity, thermodynamic-limit or arrow-of-cosmological-time
   consequence follows without an explicit model and comparison map.

## Formal proof status

File:
`formal/GaloisForLFunctions/RHTower/FiniteContractionTemporalBoundaryLaw.lean`.

Unconditional theorems:

- `tendsto_finiteContraction_orbit_sub_peripheralOrbit_zero`;
- `tendsto_norm_finiteContraction_orbit_sub_peripheralOrbit_zero`; and
- `finiteContraction_temporalBoundary_core`.

Foreground verification passed with
`lake env lean
GaloisForLFunctions/RHTower/FiniteContractionTemporalBoundaryLaw.lean`.

The scratch axiom audit reports only `propext`, `Classical.choice` and
`Quot.sound`.

## Promotion gates

- [x] dependency-closed proof
- [x] unconditional Lean proof
- [x] exact asymptotic information kernel
- [ ] orbit-closure group and dimension identification
- [ ] observer comparison map
- [ ] weak-link versus permanent-kernel theorem
- [ ] continuous-time quantum-channel specialization
- [ ] infinite-dimensional extension or exact obstruction
- [ ] external priority audit
- [ ] device-feasible protocol
- [ ] hostile Nature review

