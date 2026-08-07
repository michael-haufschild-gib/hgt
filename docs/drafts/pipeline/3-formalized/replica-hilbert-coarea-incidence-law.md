# Replica--Hilbert coarea incidence law

- **ID:** replica-hilbert-coarea-incidence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** static-local-complexity-law.md; quenched-observer-spectral-action-law.md
- **Statement:** After exact returns are removed, the complete approximate-circuit incidence mass is bounded by one growing-replica projection moment, while the projector rank is exactly the homogeneous Hilbert function of the occupied projective endpoint image.

## Goal

Replace the cardinality union over circuit descriptions by an image-sensitive invariant that
simultaneously:

1. retains every source fibre sheet through the quenched source measure;
2. forgets duplicate circuit labels but retains the occupied endpoint image;
3. removes the common exact-return sector once;
4. converts the nonlinear complete shortcut union into one linear replica-moment pairing that can
   be attacked by the existing spectral-action, Hall, and cavity infrastructure.

This is the live fixed-time frontier behind the proposed incidence-normalized coarea action.  Raw
coarea mass is not itself a new invariant: by the coarea formula it is exactly the pushforward event
probability, including fibre multiplicity.  A useful law must upper-bound that mass by independently
controllable geometry rather than rename it.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `replicaHilbert_completeIncidence_bound`, `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: integrated into universal quantum-recurrence master paper after external novelty audit

## Frozen conjecture

Let `H` be a finite-dimensional complex Hilbert space, `X` a quenched probability space,
`psi : X → H` a unit-state endpoint map, and `Z` the set of return-removed circuit target vectors.
Targets may be repeated and may be zero; zero is the exact-return residue.  For `r ≥ 1`, put

```text
S_r(Z) = span_C { z^(⊗r) : z ∈ Z },
q_r(x) = ||Proj_{S_r(Z)} psi(x)^(⊗r)||²,
h_Z(r) = dim_C S_r(Z).
```

If `||z|| ≤ 1` for every target and

```text
E_a = {x : there exists z ∈ Z with |<psi(x),z>|² ≥ a},   0 < a ≤ 1,
```

then

```text
1_{E_a}(x) a^r ≤ q_r(x),
P(E_a) ≤ a^(-r) ∫ q_r dP.                                  (RHCI)
```

For Haar-distributed `psi`, because `S_r(Z)` lies in the symmetric replica sector,

```text
∫ q_r dHaar = h_Z(r) / binom(dim(H)+r-1,r).                 (HAAR)
```

For a finite projective endpoint image, `h_Z(r)` is its homogeneous coordinate-ring Hilbert
function and stabilizes at the number of distinct occupied projective endpoints no later than
degree `N-1` after choosing a nonvanishing homogenizing coordinate.

## Conjecturing protocol

### C0 — raw incidence-normalized coarea mass is the missing invariant

**Verdict:** `REDISCOVERED / CIRCULAR`.

For a locally Lipschitz endpoint map `F`, the integral

```text
∫_E ∫_{F⁻¹(y)} φ(x) / J_v F(x) dH^{m-v}(x) dH^v(y)
```

is the coarea disintegration of the source probability of `F⁻¹(E)`.  It correctly retains fibre
sheets, but supplies no upper bound.  The 2021 coarea distribution theorem gives this exact
pushforward-density formula.  Calling the same probability an action does not move the frontier.

**Positive survivor:** retain coarea mass as the left side, but find a target-image invariant that
dominates it without enumerating target labels.

### C1 — one-copy span of circuit targets controls the complete union

**Verdict:** `FALSIFIED AS A USEFUL BOUND`.

One-copy linear span can already be the full ambient space for a small universal word dictionary;
then its projector is the identity and the estimate is trivial.  This is the same linear-universality
obstruction already formalized by the local-Casimir/Hall route.

**Positive survivor:** lift each occupied target projectively before taking the span.  The growing
Veronese layers remember nonlinear image geometry that one-copy linearization destroys.

### C2 — replica target-span projection law

**Status:** `[PROVED HERE] [LEAN-PROVED]`.  Pointwise proof route:

1. `z^(⊗r) ∈ S_r(Z)`;
2. orthogonal projection preserves its inner product with that vector;
3. Cauchy--Schwarz and `||z^(⊗r)|| = ||z||^r ≤ 1` give
   `|<psi,z>|^(2r) ≤ q_r`;
4. target capture at fidelity `a` gives `a^r ≤ q_r`;
5. Markov integration gives `(RHCI)` for the complete union at once.

The target dictionary appears only through `S_r(Z)`.  Duplicate labels leave it unchanged.  A zero
return residue contributes the zero vector and changes nothing.  Source multiplicity is untouched,
because every source point is still integrated in `q_r`.

### C3 — Hilbert image law

**Status:** `[PROVED HERE] [LEAN-PROVED]` bridge to existing corpus.

Duality between degree-`r` homogeneous evaluation and the span of Veronese vectors identifies
`rank S_r(Z)` with the homogeneous Hilbert function of the distinct occupied projective image.
The existing `PrimeValuationVeroneseHilbert` module already proves finite-point interpolation and
surjectivity from degree `N-1`.  The quantum target-span duality is the finite-dimensional dual-rank
identity proved below.

## Complete paper proof

### Pointwise complete-union bound

Fix `x` and write `u = psi(x)^(⊗r)`.  For every return-removed target `z`, put
`v = z^(⊗r)`.  By definition `v ∈ S_r(Z)`.  If `P_r` is the orthogonal projector onto
`S_r(Z)`, then

```text
<u,v> = <P_r u,v>.
```

Tensor-product inner products factor and tensor norms multiply.  Therefore Cauchy--Schwarz and
`||z|| ≤ 1` give

```text
|<psi(x),z>|^(2r)
  = |<u,v>|²
  = |<P_r u,v>|²
  ≤ ||P_r u||² ||v||²
  = q_r(x) ||z||^(2r)
  ≤ q_r(x).                                                (1)
```

If `x ∈ E_a`, some target has squared overlap at least `a`; raising that inequality to the
positive integer power `r` and applying `(1)` gives

```text
1_{E_a}(x) a^r ≤ q_r(x).                                  (2)
```

This is pointwise and already covers the complete target union.  Integrating `(2)` over the
quenched source law and dividing by `a^r > 0` proves `(RHCI)`.  Equivalently, this is Markov's
inequality applied once to `q_r`; no circuit-by-circuit union bound occurs.

### Fibre sheets, labels, and return removal

The proof never quotients the source.  Hence every parameter point mapping to the same endpoint
still contributes separately to the integral of `q_r`.  Whenever coarea disintegration applies,
the left side is exactly the incidence-normalized coarea mass with all fibre sheets retained.

Replacing a target indexing set by another family with the same occupied vectors leaves
`S_r(Z)` unchanged.  In particular duplicate circuit descriptions do not alter the bound.  The
lag-resolved recurrence theorem sends an exact return to residual vector zero.  Since
`0^(⊗r)=0`, adjoining or deleting any number of exact-return residues also leaves `S_r(Z)` and
`q_r` unchanged.  The anchor-rephasing theorem first absorbs every adaptive anchor into one fixed
enlarged finite word dictionary, so no source-dependent continuum is hidden in this step.

### Hilbert-function identity

Let `V` be the ambient coordinate space and let `Zbar` be the distinct occupied projective target
image.  Degree-`r` homogeneous polynomials form `Sym^r(V*)`.  Evaluation on `Zbar` is a linear map

```text
ev_r : Sym^r(V*) → C^Zbar.
```

Its dual sends the coordinate evaluation functional at `[z]` to the Veronese vector `z^(⊗r)`
under the canonical duality `Sym^r(V*)* ≅ Sym^r(V)`.  Consequently

```text
rank(ev_r) = rank(ev_r*) = dim span{z^(⊗r) : [z] ∈ Zbar}
           = h_Z(r).                                      (3)
```

The left side is the homogeneous coordinate-ring Hilbert function of `Zbar`.  This proves that
the projector measures occupied endpoint image rather than number of circuit descriptions.

For a finite image of `N` projective points, choose a linear coordinate nonzero at all of them and
normalize representatives so that coordinate is one.  Products of `N-1` linear separators produce
homogeneous delta functions on those points.  Multiplication by powers of the homogenizing
coordinate raises degree without changing evaluations.  Thus `ev_r` is onto for every
`r ≥ N-1`; `(3)` yields `h_Z(r)=N`.  The existing corpus proves this separator construction as
`homogeneousRecurringEvaluation_surjective_of_card_sub_one_le`.

### Haar benchmark

For Haar-random unit `psi` in complex dimension `d`, the standard symmetric-moment identity is

```text
E_Haar |psi^(⊗r)><psi^(⊗r)| = P_sym / binom(d+r-1,r).
```

Because `S_r(Z)` lies in the symmetric sector, trace pairing with its projector gives

```text
E_Haar q_r = Tr(P_r P_sym) / binom(d+r-1,r)
           = h_Z(r) / binom(d+r-1,r),
```

proving `(HAAR)`.

All statements above are unconditional finite-dimensional theorems.  No randomness, locality,
spectral gap, transversality, or unproved complexity premise enters the proof.  Local-Hamiltonian
structure is needed only for the next quantitative task: bounding the exact moment pairing more
sharply than its Haar benchmark or proving approach to that benchmark.

## External novelty audit

- Harrow's [symmetric-subspace review](https://arxiv.org/abs/1308.6595) supplies the Haar moment identity, so `(HAAR)` alone is
  background, not novelty.
- Existing [random-circuit complexity results](https://arxiv.org/abs/2106.05305) use volume, algebraic geometry, or stochastic circuit
  dynamics; the targeted search found no theorem replacing a complete approximate circuit union by
  the Hilbert function of its return-removed occupied image for one static local-Hamiltonian
  ensemble.
- [Stabilizer-rank](https://arxiv.org/abs/2106.03214) and symmetric-tensor/Waring literature confirms that tensor-power spans are a
  meaningful complexity invariant, but does not establish `(RHCI)` in this recurrence setting.
- **Current label:** `[NOVELTY UNVERIFIED]`.  Do not advertise novelty until theorem-level comparison
  is completed.

## Hostile review / exact remaining risk

- `(RHCI)` is an exact non-circular bound, but does not by itself prove decay for ordinary static
  local Hamiltonians.  That requires a bound on the quenched moment pairing
  `∫ ||Proj_{S_r(Z)} psi_J(t)^(⊗r)||² dP(J)` at growing `r`.
- If `S_r(Z)` fills the whole symmetric sector at the needed replica order, the law becomes trivial.
  Circuit endpoint Hilbert growth must therefore be bounded before claiming a Brown--Susskind
  plateau.
- For a continuum gate set, `h_Z(r)` measures algebraic image complexity, not number of circuit
  descriptions.  Any claimed size bound must be proved from the actual circuit parameterization.
- Coarea language must remain an interpretation of the left side, never evidence for its decay.

## Door passport

- **Door 0:** exact finite-dimensional Hilbert-space theorem; no spectral-gap or genericity premise.
- **Door 1:** complete shortcut union, arbitrary target multiplicity, arbitrary quenched source law.
- **Door 2:** compare against tensor-moment, symmetric-subspace, quantum complexity volume, and
  algebraic-circuit-image literature before publication claims.
- **Door 3:** Lean formalization of pointwise domination, complete-union inclusion, Markov bound,
  duplicate invariance, and return-zero invariance.

## No-go closure

- **Exact killing mechanism:** coarea equality is a representation of event probability, not an
  independent upper bound; one-copy span can be full.
- **Strongest positive survivor:** growing-replica target-span projector and its occupied-image
  Hilbert function.
- **New insight:** source multiplicity and target complexity are different objects.  The first is a
  moment measure; the second is a projective Hilbert function.  The former should not be normalized
  away and the latter should not be replaced by circuit-label count.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Lean verification

- Module:
  `formal/GaloisForLFunctions/HTGeometry/ReplicaHilbertCoareaIncidenceLaw.lean`.
- Capstone: `replicaHilbert_completeIncidence_bound`.
- Exact components:
  - `finitePureStateFidelity_pow_le_replicaTargetProjectionMass`;
  - `completePureStateTargetCapture_subset_replicaProjectionMass`;
  - `measure_completePureStateTargetCapture_le_replicaProjectionMoment`;
  - `replicaTargetHilbertNumber_eq_finrank_span`;
  - `replicaTargetProjectionMass_duplicated` and
    `replicaTargetHilbertNumber_duplicated`;
  - `replicaTargetProjectionMass_withZero` and
    `replicaTargetHilbertNumber_withZero`.
- `lake build GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw`:
  PASS on 2026-08-07.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Global formal lint reached this module through the `HTGeometry` umbrella and reported no forbidden
  declaration in it.  The global command remains red because four concurrently added unrelated
  modules are not yet reachable from their area umbrellas:
  `ConstrainedProlateSpectralIdentification`, `ProlateFourierSignSectors`,
  `SlepianKernelScaledFubini`, and `ShiftedDerivativeCoercivity`.

## Log

- 2026-08-07 — created directly in Stage 1 after internal corpus audit and conjecture C0/C1 failures.
- 2026-08-07 — C2/C3 paper proof closed; promoted to Stage 2.
- 2026-08-07 — complete-union, quenched moment, Hilbert-rank, duplicate-label, and return-zero laws
  formalized; promoted to Stage 3.
