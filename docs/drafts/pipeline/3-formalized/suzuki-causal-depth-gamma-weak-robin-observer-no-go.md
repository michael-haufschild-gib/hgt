# Suzuki causal-depth Gamma weak Robin-observer no-go

- **ID:** `suzuki-causal-depth-gamma-weak-robin-observer-no-go`
- **Stage:** 3-formalized
- **Route:** CCM-FU · `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Claim:** `[FORMALIZED C25] [PRODUCER-CLASS NO-GO]`

## Exact RH chain

`weakly pointwise bounded bounded-operator Robin family`
→ `pointwise norm boundedness` by Banach--Steinhaus on vector orbits
→ `uniform operator-norm boundedness` by Banach--Steinhaus on operators
→ existing trace duality makes correction uniformly bounded
→ existing transition-core divergence forbids rectangular Ward semiboundedness
→ kill every WOT-bounded bounded-operator realization of remaining CCM-FU producer.

This strictly strengthens C24. Survivor must have an unbounded matrix coefficient on some fixed
pair of source vectors, hence cannot converge or remain relatively compact in weak or strong
operator topology; alternatively it must use a genuine unbounded/common-domain observer or a
non-trace-class relative trace before Gram/cofinal limit.

## Internal frontier

- `SuzukiCausalDepthGammaBoundedRobinTraceNoGo` kills only a supplied uniform operator-norm bound.
- `exists_seminorm_bound_of_bddAbove` and
  `barrelledPointwiseBounded_opNorm_isBigO_one` formalize the required Banach--Steinhaus mechanism
  for scalar currents on barrelled normed sources.
- `suzukiCanonicalCausalDepthGammaEnergyOperator_isTraceClass` supplies fixed positive
  trace-class carrier.
- `eventually_linear_le_causalDepthGammaTraceNorm_mul_observerNorm_of_Ward_bddBelow` supplies
  contradiction once uniform operator boundedness is derived.
- Corpus search found no theorem applying the two-level weak-to-uniform argument to this observer
  family.

## External frontier through 2026-08-31

Banach--Steinhaus and weakly bounded subsets of Banach spaces are classical. Novelty claim is not
that general theorem; it is exact source-specific impossibility and the resulting CCM-FU route
classification. Checked Suzuki's 2026 nonlocal Weil-operator paper; it does not formulate a
causal-depth Gamma-Schur Robin observer or this obstruction.

## C25

Let `B_N` be bounded operators on the canonical causal-depth Gamma Hilbert space. Assume every
matrix coefficient family is bounded:

`forall x y, BddAbove (range (fun N => norm (inner (B_N x) y)))`.

Then no choice of aperture and lower floor makes the corrected transition-core rectangular Ward
defect eventually lower-semibounded on apertures `8n`.

## Paper proof

Fix `x`. The vectors `B_N x` are weakly bounded by hypothesis. Regard them through real parts of
their Riesz functionals; Banach--Steinhaus gives `sup_N ||B_N x|| < infinity`. Now the operator
family is pointwise norm bounded. A second Banach--Steinhaus application gives one `M` with
`||B_N|| <= M` for every `N`. C24's closed theorem
`no_uniformlyBounded_causalDepthGammaTrace_WardProducer` gives the contradiction.

The contrapositive is the sharp survivor: any semibounding bounded-operator Robin family has fixed
`x,y` whose matrix coefficient is unbounded. WOT/SOT convergence implies coefficient boundedness,
so neither topology can contain a convergent successful family.

## Lean closure

`SuzukiCausalDepthGammaWeakRobinTraceNoGo.lean` proves:

- `uniformlyBounded_of_weaklyPointwiseBounded`: the two-level Banach--Steinhaus bridge;
- `no_weaklyPointwiseBounded_causalDepthGammaTrace_WardProducer`: the producer-class kill;
- `exists_unbounded_causalDepthGammaObserver_matrixCoefficient_of_Ward_bddBelow`: the sharp
  survivor.

Direct `lake env lean` and targeted `lake build` pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

`[PAPER-PROVED] [LEAN-CLOSED]`
