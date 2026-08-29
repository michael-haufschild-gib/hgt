# Differential-algebraic / HT topological interlacing law

- **ID:** `da-ht-topological-interlacing-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean) — `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; compact-open and Hardy topologies; continuous-selector no-go
- **Statement:** On every connected complex domain, the DA functions over `C(z)` are dense and
  meagre in the compact-open holomorphic space, while the HT functions are dense and comeagre.  In
  `H^2(D)`, both DA and HT functions are norm dense.

## Goal

Determine whether “differentially algebraic versus hypertranscendental” can behave as a stable
analytic phase label.  It cannot.  In the natural function-space topologies, both classes occur
arbitrarily close to every carrier, and the HT class is topologically generic in the compact-open
topology.

This is a theorem about HT functions in general.  Its RH consequence is limited but exact: no
continuous norm/compact-open implementation can use the bare DA/HT dichotomy as its missing zero,
positivity, cyclicity, or spectral selector.

## Compact-open theorem `[PROVED HERE]`

Let `Omega subset C` be a connected domain.  Give `O(Omega)` its compact-open Frechet topology.  Let

```text
DA(Omega)
  = {f in O(Omega) : f satisfies a nonzero ADE over C(z)},

HT(Omega) = O(Omega) minus DA(Omega).                         (1)
```

Then:

1. `DA(Omega)` is dense and meagre in `O(Omega)`;
2. `HT(Omega)` is a dense comeagre `G_delta` subset of `O(Omega)`;
3. every nonempty compact-open neighborhood contains both DA and HT functions.

The coefficient field in this theorem is the full uncountable field `C(z)`, not a countable
subfield.

## Countable support normal form

After clearing denominators, every ADE over `C(z)` is a finite complex linear relation among
distinct expanded differential monomials

```text
M_(k,alpha)(z,Y_0,...,Y_m)
  = z^k product_(j=0)^m Y_j^(alpha_j),                        (2)
```

where `k,m` and the entries of `alpha` are nonnegative integers.  Although the coefficients of a
relation are arbitrary complex numbers, there are only countably many finite supports `S` made of
monomials (2).

For a finite support `S={M_1,...,M_r}`, define

```text
L_S = {f in O(Omega) :
       M_1(z,j^m f(z)),...,M_r(z,j^m f(z))
       are linearly dependent over C}.                       (3)
```

Then

```text
DA(Omega) = union_S L_S.                                     (4)
```

This finite-support reduction is what removes the apparent uncountability obstruction.

## Closedness of each bounded-complexity locus `[PROVED HERE]`

The functions in (3) are linearly dependent exactly when every evaluation determinant

```text
det(M_j(z_i,j^m f(z_i)))_(1<=i,j<=r)                         (5)
```

vanishes as `(z_1,...,z_r)` ranges over `Omega^r`.  Compact-open convergence of holomorphic
functions implies compact-open convergence of every fixed derivative.  Hence every determinant
(5) is a continuous function of `f`, and `L_S`, the intersection of their zero sets, is closed.

## Empty interior `[PROVED HERE]`

The distinct monomials `M_1,...,M_r` are linearly independent polynomial functions on

```text
Omega times C^(m+1).                                        (6)
```

The standard evaluation lemma supplies points

```text
(z_i,v_i) in Omega times C^(m+1),       1<=i<=r,              (7)
```

with distinct base coordinates `z_i`, for which

```text
det(M_j(z_i,v_i)) != 0.                                     (8)
```

Distinct base coordinates may be imposed inductively: deleting finitely many `z`-values preserves
linear independence, since a polynomial relation vanishing on the remaining open set would vanish
identically.

The joint jet map

```text
J:O(Omega) -> (C^(m+1))^r,
J(f)=(j^m f(z_1),...,j^m f(z_r)),                            (9)
```

is continuous and surjective by polynomial Hermite interpolation.  As a continuous surjective
linear map from a Frechet space to a finite-dimensional space, it is open.

If `L_S` contained a nonempty open set `U`, then `J(U)` would be nonempty and open.  But (5) would
force the nonzero polynomial determinant in (8) to vanish on all of `J(U)`, impossible.  Thus every
`L_S` has empty interior.  Since it is closed, it is nowhere dense.

Equation (4) is a countable union of nowhere dense sets.  The Frechet space `O(Omega)` is Baire, so
`DA(Omega)` is meagre and `HT(Omega)` is comeagre and dense.

## Density of the DA locus `[PROVED HERE]`

Runge's theorem approximates every member of `O(Omega)`, uniformly on compact subsets, by rational
functions whose poles lie outside `Omega`; when `Omega=C`, use polynomials.  Every such approximant
belongs to `C(z)` and is therefore DA over `C(z)`.  Hence `DA(Omega)` is dense.

The two classes are consequently topologically interlaced:

```text
closure(DA(Omega)) = closure(HT(Omega)) = O(Omega),           (10)

DA(Omega) is meagre,
HT(Omega) is comeagre.                                       (11)
```

## Hardy-norm theorem `[PROVED HERE]`

Let `H^2(D)` be the classical Hardy space of the unit disk, with its Hilbert norm.  Then both its
DA and HT subsets over `C(z)` are norm dense.

Polynomials are DA and dense in `H^2(D)`, so the DA assertion is immediate.

For the HT assertion, put

```text
h(z)=Gamma(z+2).                                             (12)
```

The closed disk `{z+2:|z|<=1}` contains no Gamma pole.  Hence `h` is bounded on `D`, so
`h in H^infinity(D) subset H^2(D)`.  It is HT over `C(z)`: an ADE for `Gamma(z+2)` on `D` would,
after the affine change of variable and analytic continuation, give an ADE for `Gamma`, contrary
to Holder's theorem.

Fix arbitrary `f in H^2(D)`.  At most one scalar `lambda in C` can make

```text
f+lambda h                                                   (13)
```

DA.  Indeed, if two distinct scalars did so, subtracting the two DA functions would make the
nonzero scalar multiple of `h` DA.  This is impossible because the DA elements in the meromorphic
function field form a differential subfield.

Choose nonexceptional nonzero scalars `lambda` tending to zero.  Then every `f+lambda h` is HT and

```text
||f+lambda h-f||_(H^2) = |lambda| ||h||_(H^2) -> 0.          (14)
```

Thus HT functions are norm dense in `H^2(D)`.

No comeagreness claim is made in the Hardy norm: differentiation is not continuous as an
`H^2 -> H^2` operator, so the compact-open closed-locus proof does not transfer mechanically.

## Continuous phase-selector law `[PROVED HERE]`

Let `X` be either `O(Omega)` with the compact-open topology or `H^2(D)` with its norm topology, and
let `Y` be Hausdorff.  Suppose a continuous map

```text
Phi:X -> Y                                                    (15)
```

is constant on the DA locus and constant on the HT locus.  Since both loci are dense, the two
constants agree and continuity forces `Phi` to be constant on all of `X`.

In particular, no continuous two-valued classifier separates DA from HT in either topology.  More
generally, no continuous construction whose only nonconstant input is the Boolean DA/HT status can
produce a nontrivial analytic or spectral phase.

## Exact consequences for RH route implementations

The law excludes only implementations which discard their route-specific marked data and retain
the bare HT phase through a continuous carrier map.

1. **Nyman--Beurling / Mellin--Hardy.**  Norm closure cannot turn HT status into the missing cyclicity
   selector: both DA and HT functions are dense in the ambient Hardy topology.  The true criterion
   survives because it retains the distinguished zeta multiplier and arithmetic approximation
   subspace.
2. **Connes / Hilbert--Polya.**  A norm- or compact-open-continuous operator construction cannot
   derive a discrete spectral conclusion from the DA/HT label alone.  A canonical arithmetic
   domain, full determinant, trace formula, or exact spectral measure lies outside the theorem.
3. **de Branges.**  Compact-open HT status cannot replace the complete Hermite--Biehler inequality or
   reproducing-kernel positivity.  Those are gauge-breaking global data.
4. **Weil and Li.**  The DA/HT label cannot replace the full noncompact test cone or all-order
   coefficient sequence.  Their divisor-sensitive criteria remain logically available.

The common boundary is exact:

> Hypertranscendence is generic but topologically nonseparating.  Any RH-bearing HT law must add a
> distinguished, discontinuous or gauge-breaking constraint; bare absence of an ADE cannot carry
> the selector.

## Parent-theory and novelty audit

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The compact-open proof is a direct Baire-category and finite-jet openness argument.  The DA density
is Runge approximation.  The Hardy density is the affine-line consequence of the differential-field
closure of DA elements plus Holder's theorem.  Van den Dries proves a closely adjacent meagreness
theorem for interpolation data of DA entire functions using Malgrange parametrization.  Rubel's
program studies the ring and interpolation behavior of DA entire functions.  These parents make
the present topological packaging useful but scientifically non-novel.

Primary adjacent sources:

- L. van den Dries, *Parametrizing the solutions of an analytic differential equation*, Illinois J.
  Math. 39 (1995), 450--462, DOI `10.1215/ijm/1255986390`.
- L. A. Rubel, *On the ring of differentially-algebraic entire functions*, J. Symbolic Logic 57
  (1992), 449--451, DOI `10.2307/2275279`.
- Holder's classical theorem that `Gamma` is hypertranscendental; a modern statement is recalled in
  B. Adamus, *On the differential transcendentality of the Morita p-adic gamma function*,
  arXiv:2109.11448.

## Lean status (2026-08-29)

Fully formalized unconditionally in Lean 4.  Every gap listed in the earlier assessment has been
closed, including **Runge's theorem**, which was in neither mathlib nor the corpus.

Compact-open half:

- `HTGeometry/HolomorphicCompactOpenDomain.lean` — `HoloCO Ω`, the holomorphic functions on an open
  `Ω ⊆ ℂ` as a closed complex subspace of the compact-open space `C(↥Ω, ℂ)`; complete, completely
  metrizable, Baire; `ContinuousAdd`/`ContinuousSMul`; and `continuous_holoCOJet` — every fixed jet
  is a continuous functional.
- `HTGeometry/DifferentialAlgebraicCompactOpenMeagre.lean` — the bounded-complexity strata
  `daCompactOpenStratum`, `isClosed_daCompactOpenStratum`, `daCompactOpenLocus_eq_iUnion`, and
  `exists_tendsto_notMem_daCompactOpenStratum` / `isNowhereDense_daCompactOpenStratum` — the
  empty-interior half, proved with the explicit geometric jet configuration
  `v (i,c) = a i ^ ((d+1)^(c+1))`, whose jet-sample matrix becomes a nonsingular Vandermonde matrix
  under the base-`(d+1)` digit bijection.  Consequences: `isMeagre_daCompactOpenLocus`,
  `isGδ_htCompactOpenLocus`, `dense_htCompactOpenLocus`, and the abstract selector-collapse laws
  `eq_const_of_continuous_of_dense_eqOn`, `const_eq_const_of_continuous_of_dense`.

Runge's theorem (new, not in mathlib):

- `HTGeometry/RungeGridContour.lean` — the four-edge decomposition of `RHTower.rectIntegral`, the
  grid, the **edge-cancellation identity** `sum_gridRect_eq_edges`, the fact that a surviving edge
  misses `K`, the Cauchy kernel on a grid square, and the contour representation
  `sum_gridRect_cauchyKernel`.
- `HTGeometry/IntervalRiemannSum.lean` — uniform left-endpoint Riemann sums with an oscillation
  bound.
- `HTGeometry/RungeEdgeRiemann.lean` — `exists_edgeCauchyRiemann_approx`: uniform rational
  approximation of a Cauchy-kernel edge integral on a compact set disjoint from the edge.
- `HTGeometry/RungePolePush.lean` — both pole-pushing steps with explicit error identities:
  `exists_polePush_small` (to a nearby point outside `Ω`) and `exists_infPush_small` (to infinity,
  giving polynomials).
- `HTGeometry/RungeApproxClass.lean` — the approximation bookkeeping `ApproxOn` and the class
  `RungeDA Ω` of functions analytic *and* differentially algebraic on `Ω`, with its closure
  properties.
- `HTGeometry/RungeSelection.lean`, `RungeEdgeApprox.lean`, `RungeDensity.lean` — the selection rule
  (squares **contained** in `Ω` and in a large ball), which fills the bounded components of `ℂ∖K`
  lying inside `Ω` and thereby removes both the `Ω`-hull and the pole-pushing chains of the
  classical proof; and the capstone
  **`approxOn_rungeDA_of_analyticOnNhd`**: every function analytic on a domain is uniformly
  approximable on every compact subset by functions analytic and differentially algebraic on the
  whole domain.
- `HTGeometry/RungeCompactOpenDensity.lean` — an explicit compact exhaustion, and the card's
  compact-open statements: `dense_daCompactOpenLocus`, `compactOpen_interlacing`,
  `exists_mem_both_of_isOpen`, `compactOpen_phase_selector_collapse`.

Hardy half:

- `HTGeometry/HardyDifferentialAlgebraicInterlacing.lean` — `dense_hardyDALocus` (polynomial
  truncations of `lp` sequences), the bounded hypertranscendental Hardy carrier
  `hardyHTCarrier` built from the entire reciprocal Gamma function
  (`memℓp_diskCoeff_reciprocalGammaEntire`, `not_differentiallyAlgebraicOn_hardyHTCarrier`),
  `dense_compl_hardyDALocus` (at most one exceptional scalar per point), and
  `hardy_phase_selector_collapse`.

Supporting general layers added on the way: `HTGeometry/DomainJetRelationLocus.lean` (the `(n,d)`
jet-minor certificate on an arbitrary open preconnected domain) and
`HTGeometry/DifferentialAlgebraicOnSum.lean` (constants, sums, finite sums, scalar multiples and
`differentiallyAlgebraicOn_of_eqOn` for `DifferentiallyAlgebraicOn`).

No `sorry`, `admit`, new axiom or heartbeat increase is used.  Targeted `lake env lean` and
`lake build` of every new module pass, all modules are wired into `GaloisForLFunctions.HTGeometry`,
and axiom audits of every capstone report only `propext`, `Classical.choice` and `Quot.sound`.

## Gates

- [x] 0 -> 1: arbitrary-constant coefficient obstruction reduced to countable monomial supports
- [x] 1 -> 2: meagreness, both density theorems, Hardy corollary, and continuous-selector law proved
- [x] parent-theory and primary-literature audit; classified as a bridge
- [x] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: closed by failed novelty gate

## Log

- 2026-06-20 -- Opened as the countable-base topological-largeness conjecture.
- 2026-06-23 -- Removed the countable-base restriction by counting finite differential-monomial
  supports over `C(z)`; van den Dries comparison killed novelty.
- 2026-07-11 -- Completed the dense-DA half, the Hardy norm interlacing theorem, and the continuous
  phase-selector consequence; moved the result from backlog to the stage-2 bridge lane.
