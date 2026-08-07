# Return-excised replica coarea-incidence law

- **ID:** `return-excised-replica-coarea-incidence-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Parent:** `../3-formalized/quenched-replica-pair-incidence-cut-law.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-07
- **Statement:** Removing a measurable recurrence set before forming the occupied-image replica covariance bounds all remaining shortcut coarea mass by the pair action on the return-free square, while the removed recurrence mass is paid exactly once.

## Goal

Close a defect in the existing pair-incidence cut.  Cutting an arbitrary relation in `X x X`
decomposes the total collision, but a relation containing return pairs can still leave mixed
return/nonreturn pairs on its complement.  The local-Hamiltonian estimate then remains contaminated
by the recurrence sector it was meant to avoid.

The required operation is source excision, not pair partition: restrict the quenched source measure
to the complement of a physically defined return set before forming either covariance.  This must
retain every surviving source fibre sheet, the complete occupied circuit endpoint image, duplicate
invariance, and exact-return removal.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack sequence and Door passport fixed
- [x] 1 -> 2 fully-proven: dependency-closed paper proof below
- [x] 2 -> 3 formalized: Lean theorem `quenchedReplica_returnExcisedCoareaIncidence_bound`
- [ ] 3 -> 4 publication-ready: only after ordinary-local-Hamiltonian decay and external novelty audit

## Frozen notation

Let `mu` be a finite measure on a source space `X`, `R` a measurable recurrence set, and

```text
nu_R = mu restricted to R^c.
```

Let `state : X -> H` be the endpoint map, `Z` the occupied return-removed target image, `r >= 1`
the replica order, and `a > 0` the squared-fidelity threshold.  Write

```text
E_a = {x : exists z in Z, a <= |<state(x),z>|^2},
S_r(Z) = span {z^(tensor r) : z in Z},
h_r(Z) = dim S_r(Z),
k_(r,Z)(x,y) = |<Proj_(S_r(Z)) state(x)^(tensor r),
                     Proj_(S_r(Z)) state(y)^(tensor r)>|^2.
```

The return-excised occupied-image action is

```text
A_(r,Z)(mu;R)
  = integral_(R^c x R^c) k_(r,Z)(x,y) dmu(x)dmu(y)
  = integral k_(r,Z) d(nu_R x nu_R).                         (REA)
```

## Conjecturing protocol

### C0 -- cut a return relation after the covariance is formed

Conjecture: choosing a measurable pair relation `Q` and splitting the complete collision into its
`Q` and `Q^c` integrals isolates recurrence.

**Verdict:** `[PROVED EARLIER / INSUFFICIENT]`.

The split is exact, but it is not an excision.  If `R subset X` is the recurrence sector and one
chooses `Q = R x R`, then `Q^c` still contains `R x R^c` and `R^c x R`.  If instead `Q` contains
every pair having a return endpoint, its contribution pays return/nonreturn cross-collision rather
than the one-copy recurrence mass.  Neither form gives a clean off-return local-Hamiltonian core.

**Positive survivor:** restrict the source measure to `R^c` before taking its second moment.

### C1 -- remove return points after the complete shortcut event is measured

Conjecture:

```text
mu(E_a) <= mu(R) + nu_R(E_a).                                (CUT1)
```

**Verdict:** `[PROVED HERE]`.

This pays the return set once, independently of target labels and replica order.  It is sharp: the
two terms are the masses of the two disjoint source sectors when `R subset E_a`.

### C2 -- form the occupied covariance only on the surviving source

Conjecture:

```text
(a^r nu_R(E_a))^2
  <= h_r(Z) A_(r,Z)(mu;R).                                   (CUT2)
```

**Verdict:** `[PROVED HERE]`.

Unlike C0, every pair on the right has two nonreturn endpoints.  Unlike a targetwise union, the
target family enters only through its occupied replica image.  Unlike a quotient or normalized
pushforward, every distinct surviving point of every source fibre remains in `nu_R x nu_R`.

### C3 -- arbitrary optimization over return sets

Conjecture: minimize the resulting right side over all measurable `R`.

**Verdict:** `[FALSIFIED AS A NONCIRCULAR LAW]`.

If arbitrary target-dependent sets are admitted, `R = E_a` makes the residual action zero and the
bound merely restates `mu(E_a) <= mu(E_a)`.  Optimization is meaningful only over a return
filtration fixed independently of the circuit target image, for example level sets of one physical
recurrence observable.  No unrestricted infimum is claimed.

**Positive survivor:** `(CUT1)--(CUT2)` hold simultaneously for every member of any independently
fixed measurable return filtration.  Physics may choose the level after proving its return tail and
off-return collision bounds; the theorem itself never selects a target-dependent cut.

## Dependency-closed paper proof

Put `E = E_a` and `nu = mu|R^c`.  Set theory gives

```text
E subset R union (E intersect R^c).
```

Monotonicity and finite subadditivity of the real-valued finite measure give

```text
mu(E) <= mu(R) + mu(E intersect R^c).
```

Measurability of `R` gives `nu(E) = mu(E intersect R^c)`, proving `(CUT1)`.  No measurability of
`E` is needed for this outer-measure inequality.

Now apply the already proved complete replica incidence--covariance theorem to the finite measure
`nu`.  Capture by any target is absorbed before squaring, hence

```text
(a^r nu(E))^2 <= h_r(Z) ||C_(r,Z)(nu)||_HS^2.                (1)
```

The occupied-image pair identity, again applied to `nu`, is

```text
||C_(r,Z)(nu)||_HS^2
  = integral k_(r,Z)(x,y) d(nu x nu)(x,y).                  (2)
```

Product restriction is exact:

```text
nu x nu = (mu x mu)|_(R^c x R^c).                           (3)
```

Substituting `(2)--(3)` into `(1)` proves `(CUT2)` and `(REA)`.  This proof uses no independence,
spectral-gap, transversality, random-matrix, or locality premise.

Since `nu_R(E_a) a^r >= 0`, taking the nonnegative square root of `(CUT2)` and using `(CUT1)` gives
the scalar return-cut law

```text
mu(E_a) <= mu(R) +
  sqrt(h_r(Z) A_(r,Z)(mu;R)) / a^r.                         (CUT3)
```

Thus recurrence mass appears with coefficient one: it is not squared, paired with off-return
points, or multiplied by occupied-image rank.

## Information retained

1. **Fibre-sheet multiplicity.**  Restriction deletes precisely points in `R`; it never quotients
   equal endpoints.  Every remaining preimage sheet occurs separately in both measure factors.
2. **Occupied endpoint image.**  `k_(r,Z)` compresses to `S_r(Z)`, not to the full replica sector and
   not to circuit-label coordinates.
3. **Complete circuit union.**  The existential target event is handled before any moment or square.
4. **Duplicate invariance.**  Repeating target labels changes neither `S_r(Z)`, `h_r(Z)`, nor the
   action.
5. **Exact-return removal.**  At positive replica order, adjoining the zero residual changes neither
   occupied span nor action.  Source returns in `R` are removed before covariance and paid once by
   `mu(R)`.
6. **Approximate returns.**  Any measurable return level set can be used; no exact-zero assumption is
   required for source excision.

## Why this advances the frontier

The prior pair cut asked for estimates on a complement that could still contain a return endpoint.
The new law changes the hard local theorem to the genuinely off-return quantity

```text
integral_(R^c x R^c) k_(r,Z).
```

Thus a proof may separately establish one one-source return tail `mu(R)` and one growing-replica
anti-concentration estimate with both endpoints off return.  No mixed term survives and recurrence
mass is not multiplied by target entropy or occupied-image rank.

This is a representation advance, not Brown--Susskind closure.  The still-open physics theorem is a
quantitative choice of target-independent return level for the ordinary fixed-`q` Gaussian static
local-Hamiltonian ensemble such that both terms beat shallow-circuit occupied-image growth.

## Hostile novelty audit

- Measure restriction, product restriction, covariance/frame-potential identities, and
  Cauchy--Schwarz are classical and are not claimed as new separately.
- The candidate application-level contribution is their selector-free composition with the
  return-removed occupied Veronese circuit image and a one-source recurrence excision before the
  replica covariance is formed.
- Searches around quantum frame potentials, local-Hamiltonian complexity recurrence, coarea, and
  return excision found no theorem with this exact composition.  This is not enough for a priority
  claim; status remains `[APPLICATION NOVELTY UNVERIFIED]`.
- A hostile reviewer must reject any statement that `(CUT1)--(CUT2)` proves local-Hamiltonian decay.
  It isolates the exact quantity whose decay remains to be proved.

## Door passport

- **Door 0:** finite-dimensional Hilbert-space and finite-measure theorem; no unproved premise.
- **Door 1:** complete target union, arbitrary source sheets, arbitrary measurable target-independent
  return cut.
- **Door 2:** external comparison required before publication novelty claim.
- **Door 3:** formalize mass cut, restricted pair identity, duplicate invariance, zero invariance,
  and capstone.

## Lean realization

- Module: `GaloisForLFunctions.HTGeometry.QuenchedReplicaReturnExcisionLaw`
- Definition: `returnExcisedReplicaIncidenceAction`
- Mass cut: `measureReal_capture_le_return_add_restrict_compl`
- Product action: `returnExcisedReplicaIncidenceAction_eq_restrictProduct`
- Capstone: `quenchedReplica_returnExcisedCoareaIncidence_bound`
- Scalar capstone: `measureReal_capture_le_return_add_sqrt_action`
- Invariances: duplicate target labels and exact-return zero residue

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/QuenchedReplicaReturnExcisionLaw.lean`: PASS.
- `lake build GaloisForLFunctions.HTGeometry.QuenchedReplicaReturnExcisionLaw`: PASS, 8659 jobs.
- Axiom audit of product restriction, mass cut, squared capstone, scalar capstone, duplicate
  invariance, and zero invariance: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired through `GaloisForLFunctions.HTGeometry`.
- Global formal lint reaches this module and reports no error in it.  Repository lint remains red on
  unrelated concurrently added, unwired `RHTower` Prolate modules and unrelated `HTGeometry`
  modules.

## Log

- 2026-08-07 -- C0 pair-relation cut attacked; mixed return/nonreturn pairs identified as the exact
  defect.  C1--C2 dependency-closed proof completed.  C3 arbitrary min-cut rejected as circular;
  target-independent return-filtration survivor frozen for formalization.
- 2026-08-07 -- Return-free product action, one-time recurrence payment, complete squared law,
  scalar square-root law, duplicate invariance, and exact-return zero invariance formalized and
  audited; promoted to Stage 3.
