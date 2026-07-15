# A nonzero HT source conormal forces a strict topology refinement

- **ID:** `source-conormal-strict-topology-refinement`
- **Stage:** 3-formalized
- **Type:** GENERAL HT TOPOLOGY NECESSITY THEOREM
- **Scientific status:** `[LEAN-FORMALIZED] [SIGNIFICANT POSITIVE RESIDUE] [PARENT-THEORY BRIDGE]`
- **Parent:** `../1-in-progress/hypertranscendental-mackey-corona-field.md`
- **Statement:** A nonzero Hausdorff-valued conormal annihilating a finite-observably free source
  tangent is necessarily discontinuous for the raw product clock, and the minimal topology making
  it continuous is strictly finer.

## Theorem

Let `W` be a subspace of `K^N` whose restriction to every finite coordinate set is surjective. Let

```text
L : K^N -> Q,       L(W)=0,
```

where `Q` is Hausdorff and `L` is nonzero. Define

```text
t_L = t_product inf induced(L,t_Q).
```

Topologies in Lean are ordered by reverse inclusion of open sets. Then

```text
t_L < t_product.
```

Moreover, if `t` refines `t_product` and makes `L` continuous, then `t <= t_L`. Thus `t_L` is the
coarsest refinement carrying the conormal continuously.

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `sourceConormalRefinedTopology`;
- `sourceConormalRefinedTopology_lt_product`;
- `le_sourceConormalRefinedTopology`.

The touched module passed direct Lean checking. The two theorems use only the standard axiom set
`propext`, `Classical.choice`, and `Quot.sound`. Its cached object already existed, so no module or
full build was run.

## Scientific boundary

The topology lattice argument is parent functional analysis. Its role is to turn the HT product-
topology no-go into a positive necessity theorem: every nonzero constraint conormal contributes
strictly new open sets, so the topology is part of the source object. The source-canonical conormal
module, its Mackey interval, and the capacity--current transgression remain conjectural.
