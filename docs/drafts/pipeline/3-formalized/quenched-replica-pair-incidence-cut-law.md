# Quenched replica pair-incidence cut law

- **ID:** `quenched-replica-pair-incidence-cut-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** frontier representation theorem / exact recurrence cut
- **Parent:** `quenched-replica-incidence-covariance-law.md`
- **Status:** `[LEAN-PROVED] [FRONTIER ADVANCE] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-07

## Open core attacked

The previous incidence--covariance law reduced complete shallow-circuit capture to one compressed
covariance collision,

```text
a^(2r) mu(E_a)^2 <= h_r K_(r,Z).
```

That statement retained source sheets and occupied target image, but `K_(r,Z)` was still an opaque
matrix norm.  A source-only replacement by the ordinary replica frame potential is too lossy: it
reintroduces all near-diagonal source pairs, including pairs irrelevant to the occupied circuit image.
The required next invariant must expose source pairs without discarding target occupancy.

## Conjecturing protocol

### C5 -- source-only global replica purity

Conjecture:

```text
K_(r,Z) <= integral integral |<psi(x),psi(y)>|^(2r) dmu(x)dmu(y).
```

**Verdict:** `[TRUE BUT REJECTED AS FRONTIER TOOL]`.  This is Hilbert--Schmidt contraction under
orthogonal compression.  Its right side is the standard replica frame potential.  Hostile attack:
it contains unavoidable source self-collisions and close coefficient pairs, so it can be large even
when the occupied shallow-circuit image captures negligible mass.  It erases precisely the target
geometry introduced to survive the complete circuit union.

### C6 -- occupied-image compressed pair action

Conjecture: the compressed covariance collision itself is an exact pair integral rather than merely
being bounded by a global frame potential.

**Verdict:** `[LEAN-PROVED SURVIVOR]`.  Let `b_1,...,b_h` be an orthonormal basis of the occupied
return-removed replica span `S_r(Z)`, put

```text
a_i(x) = <b_i, psi(x)^(tensor r)>,
k_(r,Z)(x,y) = |sum_i conjugate(a_i(x)) a_i(y)|^2.
```

For every sigma-finite source measure for which the coordinate fields are measurable and
square-integrable,

```text
K_(r,Z) = integral_(X x X) k_(r,Z)(x,y) d(mu x mu)(x,y).       (PIC1)
```

Thus the hard object is a target-compressed frame potential: both endpoints are first compressed to
the occupied replica image.  No source fibre, circuit endpoint, or replica coordinate is selected.

### C7 -- isolate common recurrence mass once

Conjecture: every measurable source-pair return relation `R` can be removed once, before any
anti-concentration estimate.

**Verdict:** `[LEAN-PROVED SURVIVOR]`.  The kernel is integrable and nonnegative, hence

```text
K_(r,Z)
  = integral_R k_(r,Z) d(mu x mu)
  + integral_(R^c) k_(r,Z) d(mu x mu).                        (PIC2)
```

Combining `(PIC1)`--`(PIC2)` with complete incidence gives

```text
a^(2r) mu(E_a)^2
  <= h_r [integral_R k_(r,Z) + integral_(R^c) k_(r,Z)].       (PIC3)
```

`R` can contain the common exact/approximate recurrence sector.  Its complement is the sole domain
on which local-Hamiltonian anti-concentration must be proved.  This is an exact decomposition, not a
probabilistic hypothesis.

## Dependency-closed paper proof

Write `C_ij = integral conjugate(a_i(x)) a_j(x) dmu(x)`.  Square-integrability of every `a_i`
implies integrability of all products by Holder.  Complex conjugation commutes with the Bochner
integral, and product-measure Fubini gives

```text
|C_ij|^2
  = integral_(X x X)
      a_i(x) conjugate(a_j(x)) conjugate(a_i(y)) a_j(y)
    d(mu x mu)(x,y).
```

Finite summation over `i,j` can therefore pass through the integral.  Inside the integral,

```text
sum_(i,j) a_i(x) conjugate(a_j(x)) conjugate(a_i(y)) a_j(y)
  = |sum_i conjugate(a_i(x)) a_i(y)|^2.
```

This proves `(PIC1)` and simultaneously proves integrability of `k_(r,Z)`.  Applying the exact
integral decomposition over a measurable set and its complement proves `(PIC2)`.  Substitution into
the existing complete incidence--covariance law proves `(PIC3)`.

## Invariances and retained information

1. **Fibre-sheet multiplicity retained.**  Pair integration is over `X x X`; equal endpoints from
   distinct source points remain distinct weighted pairs.
2. **Occupied endpoint image retained.**  The kernel uses the orthogonal projection to `S_r(Z)`, not
   the uncompressed global frame potential.
3. **Duplicate target labels removed.**  Reparameterizations with the same replica span give the
   same pair kernel.
4. **Exact returns removed once.**  For `r>0`, adjoining the exact-return zero residual leaves the
   replica span and pair kernel unchanged.
5. **Complete circuit union retained.**  Capture by any target is absorbed before the square and no
   targetwise probability union occurs.
6. **Near-return mass isolated once.**  Every measurable relation `R` has one exact contribution;
   all further decay work is confined to `R^c`.

## Hostile review

- The identity between a global frame potential and moment-operator Hilbert--Schmidt norm is
  classical.  It is not claimed as novelty.
- The searched design/frame-potential literature studies global ensemble moments or subsystem
  projected ensembles.  The exact composition used here -- compression to the occupied
  return-removed circuit image, complete-capture incidence, and arbitrary recurrence-pair cut -- was
  not located in the primary-source search.  External novelty remains unverified until a dedicated
  systematic review; no priority claim is authorized yet.
- `(PIC3)` does not prove Brown--Susskind complexity growth.  It changes the remaining task from an
  opaque covariance estimate to two explicit pair estimates.
- No minimum spectral gap, raw observer determinant, target selector, or circuit-label union appears.

## Lean realization

- Module: `GaloisForLFunctions.HTGeometry.QuenchedReplicaPairIncidenceLaw`
- Pair identity: `replicaTargetIncidenceCollision_eq_integral_pairKernel`
- Exact cut: `integral_replicaTargetPairIncidenceKernel_add_compl`
- Capstone: `quenchedReplica_pairIncidenceCut_bound`
- Return removal: `replicaTargetPairIncidenceKernel_withZero`
- Duplicate invariance: `replicaTargetPairIncidenceKernel_duplicated`

## Honest frontier after proof

Representation-level incidence-normalized coarea problem is now closed in pair form.  Remaining
local-physics theorem is quantitative: for ordinary fixed-`q` Gaussian static local Hamiltonians,
choose a physically correct recurrence relation `R`, bound its mass sharply, and prove growing-replica
decay of the occupied-image compressed kernel on `R^c` strongly enough to beat `h_r`.  Global replica
purity is retired as the wrong upper-bound invariant because it restores source pairs the occupied
compression was designed to discard.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/QuenchedReplicaPairIncidenceLaw.lean`: PASS.
- `lake build GaloisForLFunctions.HTGeometry.QuenchedReplicaPairIncidenceLaw`: PASS, 8658 jobs.
- Axiom audit of pair identity, exact cut, capstone, and return-removal theorem: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Formal forbidden-token scan: PASS.
- Area umbrella import: wired through `GaloisForLFunctions.HTGeometry`.
- Global lint reports no error in this module.  Repository lint remains red on unrelated concurrently
  added, unwired `RHTower` Prolate modules.
