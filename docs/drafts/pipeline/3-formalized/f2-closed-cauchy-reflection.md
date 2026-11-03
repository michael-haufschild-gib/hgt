# F2 — closed Cauchy reflection across the strip

- **Stage:** 3-formalized
- **Result:** Actual Cauchy source pairs have a canonical closed, single-valued, densely defined conjugate-linear closure. Swapping the parameters gives its inverse. Every positive-length source interval gives the same graph closure.
- **Scope:** This supplies a full-strip closed operator identity, including the sector where a bounded total realization is impossible. Full Mayer-transfer compatibility and Weil positivity remain separate.

## Proof

Write `A_s` for actual normalized Cauchy averaging and `J` for the arithmetic field antiunitary. All `A_s` and their adjoints commute, since their Fourier symbols multiply. Each operator and its adjoint is injective; each has dense range. Also `J A_s J=A_s†`.

For any `Re s,Re r>0`, define the linearized graph

`G_(s,r)={(x,y): A_s y=A_r†x}`.

It is closed because both sides are bounded operators. Injectivity of `A_s` makes it single-valued. Commutativity puts every source pair `(A_s f,A_r†f)` in the graph.

Fix an interval `I=(a,b)`, `a<b`. A graph vector `(u,v)` orthogonal to all source pairs with `f` supported in `I` has adjoint row `A_s†u+A_r v` orthogonal to those inputs. Both terms have holomorphic representatives on a common strip. Local orthogonality, continuity, and analytic uniqueness make the row zero globally. Applying `A_s`, commuting operators, and using `A_s v=A_r†u` gives

`A_s A_s†u+A_r A_r†u=0`.

Pairing with `u` yields `‖A_s†u‖²+‖A_r†u‖²=0`. Injectivity gives `u=0`, then `v=0`. Hilbert orthogonal decomposition therefore identifies the closure of the interval source span with `G_(s,r)`.

Undo linearization in the second coordinate. The actual reflection graph is

`R_(s,r)={(x,y): A_s J y=A_r†x}`.

It is closed and single-valued, and contains `(A_s f,A_r Jf)` for every `f`. Its domain is dense because it contains the range of `A_s`. Addition and conjugate scaling preserve the relation. Applying `J` to its defining equation gives

`A_s†y=A_r Jx`,

which is precisely `(y,x)∈R_(r,s)`. Thus the two closed reflections are inverse. Setting `r=s♯` gives arithmetic parameter reflection throughout `0<Re s<1/2`. The actual field/core identities place `(core_s,core_(s♯))` in this graph at every upper resonance.

This graph is the minimal closed extension of the source law: any closed linearized relation containing one interval of source pairs contains it. The statement does not classify arbitrary larger closed extensions. A bounded total conjugate-linear selection below `Re s=1/4` would satisfy the already excluded global source law, so none exists.

The interval inputs here are unrestricted physical source functions. The paired WTZ period lift is a different class; no density claim for that lift is used.

## Lean

Module: `RenormalizedIntersectionTheory/MayerScattering/ClosedCauchyReflection`.

Endpoints: `mayerCauchy_window_graph_core`, `mayerCauchy_window_graph_minimal`,
`isClosed_mayerCauchyClosedReflectionGraph`,
`mayerCauchyClosedReflectionGraph_single_valued`,
`mayerCauchyClosedReflectionGraph_source`,
`dense_mayerCauchyClosedReflectionGraph_domain`,
`mayerCauchyClosedReflectionGraph_inverse`,
`mayerCauchyClosedReflectionGraph_conjugate_linear`,
`mayerCauchyClosedReflectionGraph_core`,
`mayerCauchyClosedReflectionGraph_no_bounded_total_selection`.

Final plain `lake --old env lean` check passed, warning-free. All ten printed
transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella import wired.
