# F2 — closed Cauchy reflection across the strip

- **Stage:** 1-in-progress
- **Conjecture:** At every `0<Re s<1/2`, closing the actual Cauchy source pairs gives a canonical densely defined closed conjugate-linear reflection. Reflected parameters give inverse operators. Every positive-length source interval determines the same closed graph.
- **Purpose:** Recover the full-strip operator identity after bounded fixed-Haar compatibility fails, without assuming any positivity or changing the arithmetic source.

## Proposed graph

Let `A_s` be actual normalized Cauchy averaging and `J` the arithmetic field antiunitary. Linearize the reflection by `S_s=J R_s`. Its graph should be

`G_s={(x,y): A_s y=A_(s♯)† x}`.

The defining equation is bounded, so this graph is closed; injectivity of `A_s` makes it single-valued. Commutativity of the Fourier multipliers puts `(A_s f,A_(s♯)†f)` in the graph and supplies a dense domain.

To prove that these source pairs are a graph core, take a graph vector `(u,v)` orthogonal to all source pairs. Then `A_s†u+A_(s♯)v=0`. Applying `A_s`, commuting the multipliers, and using the graph equation gives

`(A_s A_s†+A_(s♯) A_(s♯)†)u=0`.

Its inner product with `u` is a sum of squared norms. Injectivity gives `u=v=0`. Restricting the source to one interval should leave the same closure: the orthogonality row is analytic, hence local vanishing extends globally.

Conjugating the second graph coordinate by `J` recovers the actual reflection. The identities `J A_s J=A_s†` should identify the reflected graph with the inverse graph. Boundedness retains the sharp `Re s≥1/4` classification.

## Gaps

Prove graph-core density, the exact inverse relation, and interval determination in Lean. The construction selects the minimal closed extension; compatibility alone is not a uniqueness claim for arbitrary larger closed extensions. This does not yet intertwine the full weighted Mayer transfer family or identify a positive Weil metric. WTZ period lifts have paired branches; unrestricted interval sources must not be confused with those lifts.
