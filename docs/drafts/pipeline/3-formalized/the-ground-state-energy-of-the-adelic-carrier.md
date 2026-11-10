# The ground-state energy of the adelic carrier

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; the actual weighted adelic adjacency and its restricted Green product.
- **Statement:** On every finite configuration of actual adelic vertices,
  the quadratic form of `λ−Σ_p p⁻²A_p` splits exactly into interior
  edge squares, outgoing boundary energy, and the prime-agreement potential.
  The common prime-agreement mass gives a strictly positive coercivity bound.

## Construction

For a centre `x`, finite vertex set `F`, and real charges `f`, set
`h(y)=finiteGreenProduct x y` and
`V_x(y)=Σ_p p⁻²(p−1)/√p · 1_{x_p=y_p}`.
Let `N_p(y)` be the finite set of actual vertices obtained by replacing
the `p` coordinate by one of its neighbours, and define
`K(y,z)=Σ_p p⁻²1_{z∈N_p(y)}`. The local undirected correspondence
and agreement away from `p` show `z∈N_p(y) ↔ y∈N_p(z)`.

The exact decomposition is

`Q_F(f)=Σ_{y∈F}V_x(y)f(y)²`
`       +Σ_{y∈F}boundary_F(h)(y) f(y)²/h(y)`
`       +(1/2)Σ_{y,z∈F}K(y,z)h(y)h(z)(f(y)/h(y)−f(z)/h(z))²`,

where `boundary_F(h)=Ah−K_Fh≥0` and `Q_F` uses the actual adjacency
operator on charges extended by zero outside `F`.

Define the common prime-agreement mass by
`c(x,F)=Σ_p p⁻²(p−1)/√p · 1_{∀y∈F, x_p=y_p}`.
Then `c(x,F)>0` and `Q_F(f)≥c(x,F)Σ_{y∈F}f(y)²`. The mass is
unchanged under simultaneous finite adelic transport of `x` and `F`.

## Proof [PROVED HERE]

For every `y,z,p`, the entry `p⁻²1_{z∈N_p(y)}` is bounded by
`p⁻² A_p H(z,·)(y)`: the latter includes `p⁻²H(z,z)=p⁻²` when
`z` is a neighbour and is nonnegative otherwise. The already proved
operator domain of `H(z,·)` therefore proves entry summability.
Finite summation over `z∈F` commutes with this convergent prime sum,
giving the exact matrix action on every finitely supported function,
including signed charges. Symmetry of `N_p` proves symmetry of `K`.

Zero extension of `h|F` lies between zero and `h`, so positivity of
adjacency gives `K_Fh≤Ah`, proving nonnegative boundary energy.
For each pair, expand
`K(y,z)h(y)h(z)(f(y)/h(y)−f(z)/h(z))²`.
The two square terms have equal double sums by symmetry. The cross
term is twice the actual compressed adjacency pairing. Substituting
`λh−Ah=hV_x` gives the displayed decomposition. All terms converge:
the configuration sums are finite, the matrix entries are summable,
and `h` belongs to the actual adjacency domain.

The union of the restricted supports of `x` and all vertices in `F`
is finite. Choose a prime larger than every prime in that union. All
coordinates there equal the base vertex, so its strictly positive
mass occurs in `c(x,F)`. Comparison with the summable total source
mass proves convergence and positivity of `c(x,F)`. Every common
agreement is an agreement with each `y∈F`, hence `V_x(y)≥c(x,F)`.
The remaining two terms of the decomposition are nonnegative, which
proves coercivity and strict positivity for nonzero charges on `F`.
Coordinatewise group actions preserve equality, proving invariance
of the common agreement mass.

## Boundary

This concerns the specified weighted carrier operator. Positivity of
this form does not identify it with Weil's form or prove RH.
Positivity and symmetry of the full Green covariance require a further
argument; they are not assumed here.

## Lean

Module: `HyperbolicArakelovTheory/TheGroundStateEnergyOfTheAdelicCarrier.lean`.
Namespace: `GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen`.

- `finiteSource_inDomain`, `adjacency_finiteSource`: actual operator domain and matrix action for signed charges.
- `energy_decomposition`: exact potential, boundary, and interior-square identity.
- `agreementMass_pos`, `agreementMass_smul`: positive, invariant common agreement mass.
- `energy_coercive`, `energy_pos_iff`: explicit coercivity and strict positivity exactly for nonzero charges.

Plain `lake --old env lean GaloisForLFunctions/HyperbolicArakelovTheory/TheGroundStateEnergyOfTheAdelicCarrier.lean`
passes without warnings. All six printed dependency audits use only
`[propext, Classical.choice, Quot.sound]`. Imported by the programme umbrella.
