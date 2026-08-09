# Connected parity context, proper-face blindness, and positive state — Lean certification

- **ID:** ULF-CTX-1
- **Paper card:**
  `connected-parity-context-proper-face-blindness-and-positive-state-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### The context system

`parityBoundary` is the unsigned incidence map `∂_G : (G.edgeSet → ZMod 2) → (V → ZMod 2)` as a
`ZMod 2`-linear map, `(∂_G x) v = ∑_{e ∋ v} x e`.  `parityBoundary_apply_incidence` identifies the
value at `v` with the sum over the observables of the context at `v`, and `exists_global_law_iff`
identifies the global classical laws of the card with the solutions of `∂_G x = b`.

### Theorem 2.1 — exact contextuality criterion

`sum_parityBoundary_eq_zero` proves every edge column has even weight, so the image lies in the
even-charge hyperplane.  `walkParity` assigns to a walk its mod-two edge multiplicity and
`parityBoundary_walkParity` proves its boundary is the sum of the two endpoint indicators; a support
induction pairing off odd contexts along connecting walks then gives
`exists_parityBoundary_eq_of_sum_eq_zero`.  Together:

- `exists_parityBoundary_eq_iff` — a global classical law exists iff `∑_v b v = 0`;
- `range_parityBoundary` — `im ∂_G = ker (totalCharge V)`, the even-charge hyperplane exactly;
- `parityCokerEquiv` and `finrank_parityCoker` — the obstruction group is canonically `ZMod 2`,
  one dimensional, the obstruction being the total parity charge;
- `finrank_range_parityBoundary` — `rank ∂_G = |V| − 1`.

No spanning tree, rank computation, or matrix inversion is used: the walk construction proves
surjectivity onto the hyperplane directly.

### Theorem 2.2 — proper-face blindness

`exists_parityBoundary_eq_on_of_ne_univ` proves that for every `W ≠ univ` and *every* charge `b`
there is one edge assignment satisfying all context equations indexed by `W`; the correction is
carried by a single vertex outside `W`.  `properFace_blindness` bundles the odd-charge case: no
global classical law exists, while every proper observer face is jointly satisfiable, so no test
confined to a proper set of contexts detects the obstruction.

### Theorem 2.3 — positivity does not classicalize

`two_mul_card_fiber_of_flip` is the halving principle: a two-valued observable flipped by an
involution has both fibres of exactly half the size.  It yields `card_parityFiber`,
`card_valueFiber`, and `card_parityFiber_fixed`, hence at the level of contexts:

- `card_localLaws` — a context of degree `d ≥ 1` has exactly `2^(d−1)` local classical laws;
- `card_localLaws_fixed` — fixing the value of one incident observable leaves `2^(d−2)` of them,
  the same count for either value, when `d ≥ 2`;
- `localLaw_marginal_prob` — the uniform distribution on local laws gives each incident observable
  the marginal `1/2`;
- `localLaw_marginal_compatible` — two contexts sharing an observable give it the same marginal,
  so the local uniform laws are a compatible positive empirical state on the whole cover;
- `positive_state_no_global_law` — under connectedness, minimum degree two, and odd total charge:
  local laws exist everywhere, all marginals are uniform and compatible, and no global classical
  law exists.

`card_contextEdges` (through `contextEdgesEquivIncidence`) identifies the observables of a context
with its incident edges, so the counts are stated in the graph degree.

### Native models

`triangle_contextual` instantiates the three conclusions at the triangle `⊤ : SimpleGraph (Fin 3)`
with any single-context odd charge.  `peresMermin_contextual` does the same for the Peres–Mermin
context skeleton `completeBipartiteGraph (Fin 3) (Fin 3)`, supported by
`completeBipartiteGraph_connected`, `completeBipartiteGraph_degree_inl`, and
`completeBipartiteGraph_degree_inr`, which are proved for arbitrary inhabited finite sides.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveParityContextuality.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
scripts/formal_tools.py lint --check-generated
```

All checks passed with no warnings.  `#print axioms` on the criterion, the range and cokernel
computations, proper-face blindness, the positive-state capstone, marginal compatibility, and both
native models reports only `propext`, `Classical.choice`, and `Quot.sound`.  No project axiom,
placeholder, hypothesis interface, or unresolved theorem premise is used.

## Exact field consequence

A total-context obstruction can be exactly invisible on every proper observer face and can coexist
with a compatible positive state on the full cover.  Local classicality, pairwise consistency, and
positivity are therefore jointly insufficient for a global deterministic law; the missing datum is
a one-bit invariant of the whole cover, not a refinement of any part of it.
