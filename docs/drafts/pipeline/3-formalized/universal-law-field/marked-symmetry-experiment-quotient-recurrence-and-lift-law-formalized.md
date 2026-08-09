# Marked-symmetry experiment quotient, recurrence, and lift — Lean certification

- **ID:** ULF-MSQ-1
- **Paper card:** `marked-symmetry-experiment-quotient-recurrence-and-lift-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

The general clauses are stated for an arbitrary group action `MulAction H P`, where `P` is the
space of laws with the pushforward action — no probabilistic structure is needed for any of the
three theorems, which is exactly the card's claim that this is a *coordinate-free* law.  The exact
instantiation of §2 is realised concretely with `H = Circle` (the rotation group `SO(2)`),
`K = {1, −1}` the half-turn subgroup, `H ⧸ K ≅ Circle` (`ℝP¹ ≅ S¹`), and the universal covering
`Circle.exp : ℝ → Circle`.

## Certified declarations

### Theorem 1 — relative gauge and exact experiment quotient

- `passive_invisible` — clause (2): an invariant source law is unchanged by every transformation;
- `smul_eq_smul_iff_mem_stabilizer` — clause (3): `g • ν = h • ν ↔ h⁻¹ * g ∈ Stab_H(ν)`;
- `markedResponse` — clause (4): the descent of `g ↦ g • ν` to `H ⧸ Stab_H(ν)`, with
  `markedResponse_mk`, `markedResponse_injective`, `markedResponse_continuous`, and
  `markedResponse_isClosedEmbedding` (compact `H`, Hausdorff `P`).

### Theorem 2 — compact response recurrence

- `oneParameter_zero`, `oneParameter_sub` — the elementary one-parameter identities
  `γ 0 = 1` and `γ a · (γ b)⁻¹ = γ (a − b)`;
- `oneParameter_recurrence` — for a compact topological group `H`, a continuous one-parameter
  subgroup `γ`, a neighbourhood `U` of `1` and any bound `M > 0`, there is `t ≥ M` with `γ t ∈ U`.

  The paper's proof passes through the closure `L = cl(γ(ℝ))` and a cancellative-subsemigroup
  argument.  The Lean proof avoids that step: it covers the compact group by right translates of a
  symmetric neighbourhood `V` with `V · V⁻¹ ⊆ U`, extracts a finite subcover, pigeonholes the sample
  times `M, 2M, 3M, …` into it, and applies `oneParameter_sub` to the two colliding times.  This is
  strictly more elementary and needs no structure theory of compact abelian groups.
- `oneParameter_periodic` — exact periodicity `γ(t + T) • ν = γ(t) • ν` when `γ T ∈ Stab_H(ν)`.

### Theorem 3 — closed response and open lifted history

General half:

- `liftPath_one_eq_of_nullhomotopicRel` — a response loop null-homotopic rel endpoints has a closed
  lift along **any** covering of the response space;
- `monodromy_eq_self_iff_eq_one` — for a *universal* covering (simply connected total space) the
  monodromy of a class fixes a point of the fibre exactly when the class is trivial.  Together these
  are (6): the lift is closed **iff** `[γ̄] = 0`.

Exact instantiation (§2):

- `halfTurnSubgroup` — `K` as the kernel of squaring on `Circle`;
- `mem_halfTurnSubgroup_iff` — `K = {1, −1}`;
- `exp_mem_halfTurnSubgroup_iff` — `Circle.exp t ∈ K ↔ ∃ k : ℤ, t = kπ`, i.e. `K` is `πℤ` in the
  angle coordinate;
- `markedAxis` and `stabilizer_markedAxis` — `Stab_{SO(2)}(marked axis) = K`, so `K` genuinely is
  the stabilizer of a *marking*, matching clause (1);
- `sq_surjective_circle`, `responseQuotientEquiv`, `responseQuotientEquiv_mk` —
  `Circle ⧸ K ≃* Circle` with projection the squaring map;
- `halfTurnPath`, `halfTurnPath_zero`, `halfTurnPath_one`, `halfTurnPath_one_mem` — the half-turn
  path starts at the identity and ends inside `K`;
- `responseLoop`, `responseLoop_one`, `responseLoop_eq_sq` — its projection is the once-around loop
  in the response circle, and every `responseLoop n` is closed;
- `liftedAngle` — the genuine mathlib path lift of `responseLoop n` along `Circle.exp`, together
  with `liftedAngle_eq` (it is exactly `t ↦ 2πnt`), `liftedAngle_zero`, `liftedAngle_one`
  (endpoint `2πn`), `liftedAngle_one_ne_zero`, `liftedAngle_one_zsmul` (the endpoint is the `n`-th
  deck translation by `2π`), and `liftedAngle_one_injective` (distinct windings escape through
  distinct deck transformations);
- `responseLoop_not_nullhomotopicRel` — hence the winding response loop is not null-homotopic;
- `closed_response_open_lift` — the capstone bundling all six clauses.

### Corollary — positive phase erasure

`character_norm_one` — `‖χ(h)‖ = 1` for every `h` and every character `χ : H →* Circle`, so
positive character data is constant and cannot carry phase history.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveMarkedSymmetryQuotient.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,418 jobs.  `#print axioms` on
`smul_eq_smul_iff_mem_stabilizer`, `markedResponse_injective`, `markedResponse_isClosedEmbedding`,
`oneParameter_recurrence`, `oneParameter_periodic`, `liftPath_one_eq_of_nullhomotopicRel`,
`monodromy_eq_self_iff_eq_one`, `stabilizer_markedAxis`, `responseQuotientEquiv`,
`closed_response_open_lift`, and `character_norm_one` reports only `propext`, `Classical.choice`,
and `Quot.sound`.  No project axiom, placeholder, hypothesis interface, or unresolved theorem
premise is used.

## Reused mathlib content — nothing rebuilt

`MulAction.stabilizer`, `QuotientGroup`, `Continuous.isClosedEmbedding`,
`IsCompact.elim_nhds_subcover`, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`,
`IsCoveringMap.liftPath` / `eq_liftPath_iff'` / `liftPath_apply_one_eq_of_homotopicRel` /
`liftPath_const`, `IsQuotientCoveringMap.monodromy_eq_id_iff` / `monodromyPerm_injective`,
`Circle.isCoveringMap_exp`, `Circle.exp_eq_one`, `Circle.exp_surjective`,
`QuotientGroup.quotientKerEquivOfSurjective`.

## Exact field consequence

Gauge equivalence is not a property of a transformation but of a declared experiment family.  The
Lean proof separates the three levels cleanly on one fixed compact group: the passive doctrine sees
nothing (`passive_invisible`), the marked doctrine sees exactly the coset space
(`markedResponse_isClosedEmbedding`), the projective marked doctrine is recurrent
(`oneParameter_recurrence`, `responseLoop_one`), and only the lifted marked history is open
(`liftedAngle_one_injective`).  Any universal-law claim that calls routes gauges without exhibiting
the stabilizer relation `K = Stab_H(ν)` — certified here as `stabilizer_markedAxis` — has not
constructed the doctrine it is asserting.
