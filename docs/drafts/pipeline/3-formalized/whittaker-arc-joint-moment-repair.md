# Joint Whittaker moment repair

- **ID:** whittaker-arc-joint-moment-repair
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whittaker-arc-weighted-moment-repair; `ModularArcWhittakerStability`.
- **Statement:** A positive trigonometric density gives an arc moment repair with the same mass.

For `K_n=K₀(2π(n+1))` and a finite real vector `v`, put
`Q_v(t)=2Σ_n (v_n/K_n)cos(2π(n+1)t)`.
If `M>0` and `M+Q_v≥0` on `[0,1]`, then there are at most
`N+1` arc atoms with nonnegative weights, mass exactly `M`, and moments `v`.

**Proof.** First take `M=1`. For a linear functional `f`, the minimum
principle transfers `f(C(u))≥−η` on the arc to `W(t)≥−η` on the horocycle.
Fourier orthogonality gives `∫W=∫Q_v=0` and `∫WQ_v=f(v)`. Thus
`0≤∫(W+η)(1+Q_v)=f(v)+η`. Separation puts `v` in the closed convex hull
of the arc readings: a separating level at most zero contradicts this
bound; a positive level contradicts Whittaker coefficient rigidity.
The compact arc image admits an exact convex combination on at most
`N+1` points by finite atomic cubature. Apply this to `v/M` and multiply
the weights by `M`.

The theorem retains cancellation between coefficients of `Q_v`.
A bound on its negative part suffices; separate coefficient bounds are
unnecessary. The elementary estimate `|Q_v|≤2Σ_n |v_n|/K_n` also gives
the [unconditional weighted repair](whittaker-arc-weighted-moment-repair.md).

The ordinary Whittaker coordinates have not been identified with the
arithmetic node and pole corrections. No bound for that source is assumed.

## Verification

Lean: `RHTower/ModularArc/WhittakerMomentRepair.lean`,
`mem_closure_convexHull_arcCosMomentVector_of_density` and
`exists_arcCosMoment_atoms_of_density`. Foreground `lake --old env lean`
check passes; transitive axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Imported by `RHTower.lean`.
