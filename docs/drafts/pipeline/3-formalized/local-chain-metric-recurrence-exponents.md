# Sharp metric recurrence exponents for generic local quantum chains

- **ID:** `local-chain-metric-recurrence-exponents`
- **Stage:** 3-formalized
- **Type:** PAPER-PROVED BRIDGE / FIRST-RETURN LAW
- **Source:** open core I.5 of
  `../1-in-progress/temporal-codimension-interaction-law.md`
- **Scientific status:** `[PAPER-PROVED USING PUBLISHED METRIC THEOREM] [PRIORITY OPEN]`
- **Imported theorem:** Kleinbock--Margulis extremality of analytic
  nondegenerate manifolds

## Main theorem

Let \(q\geq2\), and let \(\mathcal L_{P_n,q}\) be the full real space of
traceless one-site and nearest-neighbour two-site Hamiltonians on an open
chain of \(n\geq2\) \(q\)-level systems. Put
\[
 D=q^n,\qquad d=D-1.
\]
For a simple-spectrum Hamiltonian, order the eigenvalues and define its
projective gap vector
\[
 g(H)=(E_2-E_1,\ldots,E_D-E_1)\in\mathbb R^d.       \tag{1}
\]

For Lebesgue-almost every \(H\in\mathcal L_{P_n,q}\), the following limits
hold.

For integer-time sampling, let
\[
 T_H^{\rm disc}(r)
 =
 \min\left\{
 k\geq1:
 \left\|k\,\frac{g(H)}{2\pi}\right\|_{\mathbb T^d}<r
 \right\}.                                           \tag{2}
\]
Then
\[
 \boxed{
 \lim_{r\downarrow0}
 \frac{\log T_H^{\rm disc}(r)}{\log(1/r)}
 =d=q^n-1.
 }                                                    \tag{3}
\]

For continuous time, use the first gap as a Poincaré clock and put
\[
 \alpha(H)
 =
 \left(
 \frac{E_3-E_1}{E_2-E_1},\ldots,
 \frac{E_D-E_1}{E_2-E_1}
 \right)\in\mathbb R^{d-1}.                           \tag{4}
\]
Define the first return after at least one winding of that clock by
\[
Q_H(r)
 =
 \min\{q\geq1:\|q\alpha(H)\|_{\mathbb T^{d-1}}<r\}.
                                                               \tag{5}
\]
Define
\[
 T_H^{\rm cont}(r)
 =
 \inf\left\{
 t\geq\frac{\pi}{E_2-E_1}:
 \left\|t\,\frac{g(H)}{2\pi}\right\|_{\mathbb T^d}<r
 \right\}.                                            \tag{5a}
\]
For sufficiently small \(r\), this lower cutoff excludes only the initial
departure near \(t=0\) and forces at least one winding of the Poincaré clock.
The corresponding physical time differs from
\(2\pi Q_H(r)/(E_2-E_1)\) by \(O_H(r)\). Hence
\[
 \boxed{
 \lim_{r\downarrow0}
 \frac{\log T_H^{\rm cont}(r)}{\log(1/r)}
 =d-1=q^n-2.
 }                                                    \tag{6}
\]

If recurrence accuracy is measured by any reporter deficit with a
nondegenerate quadratic minimum at the return point, then phase radius
\(r\asymp\sqrt\varepsilon\). Therefore
\[
 \boxed{
 \lim_{\varepsilon\downarrow0}
 \frac{\log T_H^{\rm disc}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{q^n-1}{2},
 \qquad
 \lim_{\varepsilon\downarrow0}
 \frac{\log T_H^{\rm cont}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{q^n-2}{2}.
 }                                                    \tag{7}
\]

Thus generic local-chain first recurrence has an exact exponent, not only a
volume-density law or worst-case upper bound.

## Lemma 1 — extremality gives an exact first-hit exponent

For \(\beta\in\mathbb R^m\), let
\[
 N_\beta(r)=\min\{q\geq1:\|q\beta\|_{\mathbb T^m}<r\}.
                                                               \tag{8}
\]
If the simultaneous Diophantine exponent of \(\beta\) is \(1/m\), then
\[
 \lim_{r\downarrow0}
 \frac{\log N_\beta(r)}{\log(1/r)}=m.                \tag{9}
\]

### Proof

Simultaneous Dirichlet approximation gives
\[
 N_\beta(r)\leq C_m r^{-m}
 \]
for all sufficiently small \(r\), which proves the limsup bound.

Fix \(\eta>0\). Diophantine exponent \(1/m\) says that only finitely many
\(q\) satisfy
\[
 \|q\beta\|_{\mathbb T^m}<q^{-1/m-\eta}.
 \]
For small \(r\), put \(q=N_\beta(r)\). Then
\[
 q^{-1/m-\eta}\leq\|q\beta\|_{\mathbb T^m}<r,
 \]
and hence
\[
 q>r^{-1/(1/m+\eta)}.
 \]
Letting \(\eta\downarrow0\) gives the liminf bound \(m\). ∎

## Lean progress -- Lemma 1

`formal/GaloisForLFunctions/HTGeometry/SimultaneousDirichlet.lean` (new, umbrella-wired,
axiom-clean) proves Lemma 1's two halves, together with the classical input the upper half needs.

| Card item | Declaration |
|---|---|
| being within `r` of the integer lattice, and its monotonicity | `latticeClose`, `latticeClose_mono` |
| the box subdivision of the unit interval into `Q` parts | `boxIndex`, `boxIndex_lt` |
| two numbers in one box have fractional parts within `1/Q` | `abs_fract_sub_lt_of_boxIndex_eq` |
| **simultaneous Dirichlet approximation**: some `q <= Q^m` is within `1/Q` of the lattice in every coordinate | `exists_simultaneous_dirichlet` |
| the first hitting time `N_beta(r)` | `firstHit` |
| **`(9)` upper half**: `N_beta(r) <= ceil(1/r)^m` | `firstHit_le` |
| **`(9)` lower half**: a multiple that misses the Diophantine radius but hits at `r` forces `q^{-c} < r` | `rpow_lt_of_hit` |
| the exponent form `r^{-1/c} < q` | `rpow_lt_cast_of_hit` |

Simultaneous Dirichlet approximation is *not* in mathlib -- only the one-dimensional statement is --
so it is proved here from the pigeonhole principle on the `Q^m` boxes of side `1/Q`, applied to the
first `Q^m + 1` multiples.

## Lean progress -- Lemma 4

`formal/GaloisForLFunctions/HTGeometry/WindingReturnEquivalence.lean` (new, umbrella-wired,
axiom-clean) proves Lemma 4's equivalence in both directions.

| Card item | Declaration |
|---|---|
| the anchored gap phase in turns, `t g_j/(2 pi)`, and the projective ratios `g_j/g_0` | `gapTurn`, `gapRatio` |
| a continuous `r`-return, and a winding `r`-return at winding `q` | `ContinuousReturn`, `WindingReturn` |
| the anchor phase scales the ratios to the other phases | `gapTurn_zero_mul_gapRatio` |
| **the converse of Lemma 4, exactly**: at `t = 2 pi q/g_0` a winding `r`-return *is* a continuous `r`-return | `continuousReturn_of_windingReturn` |
| **Lemma 4 forward**: a continuous `r`-return gives `\|\|q alpha\|\| < r(1+A)`, with `q` read off the anchor phase | `exists_windingReturn_of_continuousReturn` |
| the winding number is controlled by the elapsed time, `\|q\| <= \|t\|\|g_0\|/(2 pi) + r` | `abs_winding_le_of_continuousReturn` |
| the two-sided statement the exponent argument consumes | `continuousReturn_iff_exists_windingReturn` |

The converse direction is exact -- no `O_H(r)` -- because the anchored phase at the time
`2 pi q/g_0` *equals* `q` times the ratio.  The forward direction costs exactly the factor `1 + A`,
where `A` bounds the ratios; since that is a fixed multiplicative constant on the radius and the
time-to-winding distortion is linear, the logarithmic exponents of the two first-hit functions
coincide.  This is the "time itself supplies one winding direction" step: `d+1` continuous phases
become `d` winding ratios.

## Lean progress -- the reporter-deficit rescaling `(7)`

`formal/GaloisForLFunctions/HTGeometry/QuadraticDeficitRescaling.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| a homogeneous deficit vanishes at the return point | `deficit_zero_of_homogeneous` |
| **the two-sided Taylor comparison** `c dist(z,0)² <= Q_H(z) <= C dist(z,0)²`, by compactness of the unit sphere | `exists_deficit_two_sided_bounds` |
| **`(7)`, one half**: `Q_H(z) <= eps` forces `dist(z,0) <= sqrt(eps/c)` | `norm_le_sqrt_of_deficit_le` |
| **`(7)`, other half**: `dist(z,0) <= sqrt(eps/C)` forces `Q_H(z) <= eps` | `deficit_le_of_norm_le_sqrt` |

The statement is proved for any continuous degree-two homogeneous function that is positive off the
origin -- no Hessian, no smoothness and no explicit quadratic form is needed, only homogeneity and
compactness -- so it covers the card's `Q_H` as soon as its leading Taylor term is isolated.  The
two bounds sandwich the sublevel set `{Q_H <= eps}` between the balls of radii `sqrt(eps/C)` and
`sqrt(eps/c)`, which is exactly "replacing `r` by `sqrt(eps)`": the exponent measured in the deficit
is half the exponent measured in the distance.

### What remains

Lemma 2 (nondegeneracy of the spectral manifold, via the corpus qudit endpoint-extension theorem
plus a discriminant-symmetrised minor) and Lemma 3 (the **imported** Kleinbock--Margulis extremality
theorem, which is not in mathlib and is the card's declared external input).

## Lemma 2 — the local spectral manifold is nondegenerate

On a simple-spectrum chart, regard the centered ordered spectrum as an
analytic map
\[
 F:\mathcal L_{P_n,q}\longrightarrow
 W=\{x\in\mathbb R^D:\sum_jx_j=0\}.                  \tag{10}
\]
The qudit endpoint-extension theorem in
`../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md` proves that on one
such chart there is no constant real affine relation among the eigenbranches
except trace.
Consequently the positive-order derivatives of \(F\), up to some finite
order, span \(W\) at some point: otherwise a nonzero covector annihilating
their span would make its pairing with \(F\) locally constant and hence give
an affine branch relation.

This witness can be globalized without choosing an eigenvalue ordering.
Choose finitely many parameter multiindices whose derivative columns span
\(W\) at the witness. Form a maximal minor for one eigenvalue labeling and
multiply its squared value over all \(D!\) labelings. Derivatives of simple
roots are rational functions of the characteristic coefficients and the
discriminant. After multiplication by a sufficiently high discriminant
power, this symmetrized product is a polynomial in the local Hamiltonian
parameters. It is nonzero at the witness. Its zero set is therefore null.

Outside that null set, \(F\) is nondegenerate in the metric-Diophantine
sense. Invertible linear coordinates on \(W\) show that the gap map \(g\) is
nondegenerate. Projectivization on \(E_2-E_1\neq0\) shows that the ratio map
\(\alpha\) is also nondegenerate: an affine relation among its coordinates
would become a linear relation among the gap branches.

## Lemma 3 — metric extremality applies

Kleinbock and Margulis prove that almost every point, with respect to the
parameter measure on an analytic nondegenerate manifold in \(\mathbb R^m\),
has simultaneous Diophantine exponent \(1/m\):

- D. Kleinbock and G. Margulis, *Flows on homogeneous spaces and
  Diophantine approximation on manifolds*, Annals of Mathematics 148 (1998),
  339--360,
  [journal](https://annals.math.princeton.edu/articles/12997).

Apply this theorem to \(g/(2\pi)\in\mathbb R^d\) and to
\(\alpha\in\mathbb R^{d-1}\). Lemma 1 gives `(3)` and the winding-number
form of `(6)`.

## Lemma 4 — winding number equals continuous return time

If all projective phases are within \(r\) of the identity and \(r\) is
small, then
\[
 t(E_2-E_1)=2\pi q+O(r)
\]
for a unique integer \(q\). Substitution in the remaining phases gives
\[
 \|q\alpha(H)\|_{\mathbb T^{d-1}}=O_H(r).
 \]
Conversely, an \(r\)-approximation in `(5)` evaluated at
\(t=2\pi q/(E_2-E_1)\) returns every projective phase within \(O_H(r)\).
The fixed multiplicative constants and the \(O_H(r)\) time correction do
not change a logarithmic exponent. This proves `(6)`.

For a smooth reporter deficit with positive-definite Hessian on the minimal
temporal hull, compactness and Taylor expansion give
\[
 c_H\,\operatorname{dist}(z,0)^2
 \leq Q_H(z)
 \leq C_H\,\operatorname{dist}(z,0)^2
 \]
near the return point. Replacing \(r\) by \(\sqrt\varepsilon\) proves `(7)`.
∎

## What this closes

1. Long-time return density and first return are now separate proved laws.
2. The continuous exponent loses exactly one phase dimension because time
   itself supplies one winding direction.
3. Static nearest-neighbour locality attains the exponent associated with the
   full projective Hilbert dimension.
4. The result is typical in physical coupling space, not in an unrestricted
   random-matrix ensemble.

## Hostile boundary

1. The theorem is almost-everywhere, not a uniform bound for every local
   Hamiltonian.
2. Constants and finite-resolution crossover times remain Hamiltonian
   dependent.
3. Translation-invariant low-parameter families require a separate
   nondegeneracy proof.
4. Continuous spectra, thermodynamic limits and open-system contraction are
   not covered by this finite-chain theorem.
5. Formalization requires a first-principles development of the imported
   metric extremality theorem or a formally proved replacement; no manuscript
   claim is authorized before that dependency is closed.

## Gates

- [x] exact Diophantine-to-first-return lemma
- [x] local spectral nondegeneracy bridge on paper
- [x] discrete exponent
- [x] continuous transverse exponent
- [x] quadratic-deficit conversion
- [ ] exact-object priority audit
- [ ] specialist audit of algebraic symmetrization
- [x] formal metric-Diophantine dependency

## Lean progress -- the Dirichlet half of `(3)`

`formal/GaloisForLFunctions/RHTower/DiscreteRecurrenceDirichletBound.lean` (new, umbrella-wired,
axiom-clean) proves the upper half of the discrete exponent law, for *every* spectrum, with no
genericity and no metric theory.

| Card item | Declaration |
|---|---|
| the first integer time at which every projective phase is within `r` of an integer | `discreteRecurrenceTime` |
| **the Dirichlet bound** `T^disc(r) <= (⌈1/r⌉ + 1)^d`, from the corpus's simultaneous approximation `exists_fin_simultaneous_integer_approximation_quantitative` | `discreteRecurrenceTime_le_ceil` |
| its real form `T^disc(r) <= (1/r + 2)^d` | `discreteRecurrenceTime_le_pow` |
| **hence `log T^disc(r) <= d · log(1/r + 2)`**, so the exponent is at most `d` | `log_discreteRecurrenceTime_le` |
| the comparison factor `log(N+2)/log N` tends to one, so the bound is asymptotically exactly `d` | `tendsto_dirichletShiftRatio` |

No new pigeonhole was written: the corpus already owned quantitative simultaneous Dirichlet
approximation in `d` coordinates, so this file is the exponent bookkeeping on top of it.

### What remains

The matching *lower* bound, which is where all the content of the sharp law sits.  It holds only
for Lebesgue-almost every `H`, and it is exactly the imported Kleinbock--Margulis extremality of
analytic nondegenerate manifolds: the gap map of the local chain must be shown nondegenerate, and
extremality then rules out the exceptional Diophantine set.  Neither extremality nor the
Khintchine--Groshev transfer it feeds is present in mathlib, so this is the card's genuine formal
gap; the Dirichlet half above needs none of it.

## Lean progress -- Lemma 3 (the imported metric theorem) is CLOSED (2026-08-22)

The card's declared external input -- Kleinbock--Margulis extremality of analytic nondegenerate
manifolds -- is now an unconditional Lean theorem in this repository, not an import.

| Card item | Declaration | Module |
|---|---|---|
| **Theorem A**: a.e. parameter of a nondegenerate `C^l` map is not very well *multiplicatively* approximable | `theoremA` | `KleinbockMargulis/TheoremA.lean` |
| the same with a non-uniform nondegeneracy order (only the all-order degenerate locus must be null) | `theoremA_allOrders` | same |
| the mathlib gap `∑_{m ∈ ℕⁿ} r^{∑ mᵢ} < ∞` for `0 ≤ r < 1` | `summable_pow_sum` | same |
| **Khintchine transference**, dual ⟸ simultaneous | `vwma_of_vwa` | `KleinbockMargulis/Transference.lean` |
| its pigeonhole core: the index-`q` sublattice meets the cube of side `q^{1/n}` | `exists_small_dvd_dotProd`, `exists_transfer_point` | same |
| **Lemma 3 as the card uses it**: a.e. parameter has simultaneous Diophantine exponent exactly `1/n` | `theoremA_simultaneous`, `theoremA_simultaneous_allOrders`, `measure_exists_dioph_exponent_eq_zero` | `KleinbockMargulis/Extremal.lean` |
| the exponent statement unpacked: for every `η > 0` only finitely many `q ≥ 1` with `‖q y‖ ≤ q^{-1/n-η}` | `finite_of_not_vwa` | same |

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) and wired into
`GaloisForLFunctions.HTGeometry`.  §5 of the paper (quantitative nondivergence), §3 (goodness) and
§2 (the reduction) were already Lean-complete in `KleinbockMargulis/`; Theorem A is their
Borel--Cantelli assembly.

### What remains on this card

**Lemma 2 only** -- nondegeneracy of the spectral manifold.  With `theoremA_allOrders` the
requirement is exactly:

> the set of chain Hamiltonians at which some nonzero `w` kills *every* positive-order derivative
> of the gap-ratio map `α` is Lebesgue-null.

For a real-analytic `α` on a connected chart that set is *empty* as soon as no nonzero real affine
relation among the `α_i` holds identically on the chart -- which is the content of the qudit
endpoint-extension theorem of `../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`.
So Lemma 2 splits into (a) analyticity/derivative bookkeeping for simple eigenbranches and (b) the
already-owned no-affine-relation theorem, or alternatively the card's own discriminant-symmetrised
minor route, which lands in `realMvPolynomial_zero_set_volume_fin`
(`HTGeometry/RealPolynomialZeroMeasure.lean`) instead of an analyticity argument.

## Lemma 2 reduced to one algebraic statement (2026-08-22)

`formal/GaloisForLFunctions/HTGeometry/KleinbockMargulis/AnalyticNondegeneracy.lean` (new,
umbrella-wired, axiom-clean) removes the whole derivative-spanning half of Lemma 2.

| Card item | Declaration |
|---|---|
| an analytic function whose positive-order derivatives all vanish at a point is constant near it | `eventuallyEq_const_of_iteratedFDeriv_eq_zero` |
| **nondegeneracy from the absence of an identical relation**: on a preconnected open set, an analytic map none of whose nonzero component combinations is constant is nondegenerate at some finite order at *every* point | `exists_nondegAt_of_no_constant_combination` |
| **Theorem A for an analytic family**: hence a.e. parameter is not simultaneously very well approximable | `theoremA_analytic` (and `theoremA_analytic_multiplicative`) |

The proof of `exists_nondegAt_of_no_constant_combination` is the nested-compact argument: the unit
covectors killing the first `l` derivatives form a decreasing sequence of nonempty compacts, so one
covector kills every positive-order derivative; analyticity makes `w·F` locally constant and
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` propagates that over the set.

**Analyticity of the ordered spectrum is already owned**:
`SortedEigenbranchAnalytic.analyticAt_sortedEnsembleSpectrum` — the sorted spectrum of
`∑_a q_a P_a` is real-analytic at every point of the simple locus, for any Hermitian family `P`.

### The single remaining statement

Multiplying `∑_j w_j α_j ≡ c` by `E_2 - E_1` turns it into `∑_i u_i E_i ≡ 0` with `u` traceless and
`u = 0 ⟺ w = 0` (the identity is homogeneous of degree one, so no constant term survives).  So
Lemma 2 -- and with it this card and clause 5 of `onset-recurrence-dimension-independence-law` --
is exactly:

> **(L2)** On a connected component of the simple-spectrum locus of the traceless path-local
> family, no nonzero traceless real `u` satisfies `∑_i u_i E_i(H) = 0` identically.
> Equivalently: the ℝ-span of the sorted-spectrum image is the whole trace-zero hyperplane `W`.

Two things are worth recording about (L2).

1. **A single Hamiltonian can never witness it.**  At one fixed `H`, `u ↦ ∑ u_i E_i(H)` is a single
   linear functional, so its kernel is a hyperplane: real relations always exist pointwise.  Unlike
   the *rational* rank statement, (L2) is not a "generic point" statement and is not implied by
   `exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`.
2. **Monodromy is the clean route.**  The annihilator `C` of the span is stable under the spectral
   monodromy group (continuation along a loop permutes the branches), `W` is the irreducible
   standard `S_D`-module over ℝ, and `C = W` would force all eigenvalues identically equal.  So
   full symmetric monodromy of the path family implies (L2) outright.  The corpus already has the
   **two-local** analogue in exactly this shape --
   `TwoLocalCommonBaseEdgeMonodromy.commonBaseTwoLocalMonodromySubgroup_eq_top` together with
   `TwoLocalMonodromyRelationRigidity.coefficients_constant_of_commonBaseTwoLocalMonodromyInvariantRelation`,
   the latter stated for *complex* coefficients, i.e. it is already the real rigidity.  What is
   missing is the path version: the corpus's loops live in the star family
   (`HypercubeTwoLocalParameter`: constant, onsite, all-pairs interaction, transverse), and the
   endpoint-extension escape stack (`HermitianLocalExtensionRelationEscape`,
   `ParityCompleteLocalExtensionRelationEscape`) is stated for *balanced integer* characters.

## Lemma 2 reduces to path-family monodromy, and the rigidity half is already corpus-owned (2026-08-22)

Statement `(L2)` above — no nonzero traceless real `u` with `∑ u_i E_i ≡ 0` on a chart — follows
from **full symmetric monodromy of the path family** together with a corpus theorem that is
*already coefficient-agnostic*:

`SpectralMonodromyRelationRigidity.coefficients_eq_of_all_permuted_relations` is stated for an
arbitrary base field `K` (`c : ι → K`, `x : ι → L`, `[Algebra K L]`), so it applies verbatim with
`K = ℝ`.  Given a relation that holds identically on a chart, analytic continuation along a closed
loop realizing the permutation `σ` turns it into `∑ u_x E_{σ(x)}(H₀) = 0` at the common base point;
ranging over all `σ` the theorem forces every `u_x` equal, and tracelessness then forces `u = 0`.

So the only missing ingredient is the path analogue of
`TwoLocalCommonBaseEdgeMonodromy.everyPermutation_has_exact_commonBase_twoLocalLoop`.

**Why the existing two-local result does not transfer.**  The corpus family
`HypercubeTwoLocalParameter` carries `constant`, `onsite i` (`Z_i`), `interaction i j` (`Z_iZ_j` for
*all* pairs) and `transverse i` (`X_i`); the loops are built inside the *star* sub-family coupling
site `0` to every other site.  The card's family has only nearest-neighbour couplings, so the
non-adjacent `Z_iZ_j` are unavailable, and
`polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_twoLocalEmbedding` transfers
genericity only *upward*, to families **containing** the hypercube two-local directions.

**What a path construction needs.**  The mechanism is unchanged: a diagonal Hamiltonian with
distinct energies, one transverse `X_i` turned on to create an isolated avoided crossing between
`x` and `x ⊕ eᵢ`, and a loop around it; then `closure_hypercubeEdgeSwaps`.  The diagonal energies
`d_x = ∑_i a_i x_i + ∑_i b_i x_i x_{i+1}` are pairwise distinct for generic `(a, b)` — each
`d_x − d_y` is a nonzero linear form — and the corpus already owns an explicit separating choice
(`BaseThreeSignSeparation`).  The work is the labelled-path bookkeeping
(`LabeledPolynomialMatrixPath`), which is what makes the endpoint permutation literal and supplies
the *common base point* that the whole argument turns on.

## Lemma 2: the *global* route, and why monodromy is the wrong tool here (2026-08-22, later)

The path-monodromy plan recorded above has an obstruction that is not technical.  With strictly
nearest-neighbour couplings the detuning of the pair `{x, x ⊕ eᵢ}` is
`δ_z = 2(a_i + ∑_{k adjacent to i} b_{ik} z_k)`, which depends **only on the neighbours of `i`** —
so it takes at most four values, and `2^{n-3}` pairs share each one.  Every pair with the same local
environment collides simultaneously, so a loop around such a crossing realizes a *product* of
`2^{n-3}` disjoint transpositions, never a single one.  Adding the other nearest-neighbour terms
(`Z_{i-1}X_i`, `X_iZ_{i+1}`, …) does not help: the flip amplitude is equally local.  A path family
therefore cannot isolate one hypercube edge by an avoided crossing, and the two-local construction
does not carry over.

**The route that does work is the corpus's own second-order/escape mechanism, and its core is
already stated over `ℂ`.**  Inside `HermitianLocalExtensionRelationEscape` the load-bearing lemma
takes `coefficient : α × ρ → ℂ` with hypothesis `¬ ∀ x y, coefficient x = coefficient y` and
concludes `∃ p ∈ V, ∑ i, coefficient i * C.branch i (…) ≠ target` — exactly the real-coefficient
escape, with no integrality anywhere.  Only the *wrappers* are typed with `ℤ`.

**And the statement can be made global, avoiding any connectedness of the simple locus.**  For
`c : I → ℝ` put

  `Ω_c = ∏_{σ ∈ S_I} ∑_i c_i X_{σ i}`.

`HTGeometry/LinearSpectralRelationOrbitPolynomial.lean` (new, axiom-clean, wired) builds it, over an
arbitrary integral domain `K` (the application takes `K = ℝ`; the corpus already had the *integer*
linear case over `ℚ` and the *quadratic-rate* case over a domain, but not this one):

| Card item | Declaration |
|---|---|
| the linear form and its labeling orbit | `linearRelationPoly`, `linearRelationOrbit` |
| the orbit is nonzero for every nonzero coefficient vector | `linearRelationPoly_ne_zero`, `linearRelationOrbit_ne_zero` |
| the orbit is a **symmetric** polynomial | `linearRelationOrbit_isSymmetric` |
| its value is nonzero exactly when every relabeling of the relation is | `linearRelationOrbitValue_ne_zero_iff`, `eval_linearRelationOrbit` |
| **hence it is a polynomial in the elementary symmetric functions**, i.e. in the characteristic-polynomial coefficients | `linearRelationCoefficient`, `esymmAlgHom_linearRelationCoefficient`, `linearRelationCoefficient_ne_zero`, `eval_linearRelationCoefficient_esymm` |

So `∑_i c_i E_i ≡ 0` on a nonempty open set would make a genuine **polynomial** function of the
Hamiltonian parameters vanish on an open set, hence identically — contradicting
`linearRelationCoefficient_ne_zero` once one point escapes every relabeling.  The Vieta bridge from
`esymm` of the eigenvalues to the characteristic coefficients is corpus-owned
(`HermitianCharpolyFactorization.isHermitian_esymm_eigenvalues_eq_coeff`,
`PolynomialHermitianMatrixProjectiveGenericity.eval_matrixCharacteristicElementaryPolynomial`).  That point is what the
`ℂ`-coefficient escape supplies.  No connected component bookkeeping, and no monodromy.

### The obstruction pullback is built (2026-08-22)

`HTGeometry/LinearRelationObstructionPullback.lean` (new, axiom-clean, wired) composes the orbit
obstruction with the signed characteristic coefficients of a polynomial matrix family, turning it
into a polynomial in the **parameters**.  It mirrors
`complexSpectralCoefficientObstructionPullback`, which does the same for balanced *integer*
characters.

| Card item | Declaration |
|---|---|
| the pullback, and its evaluation | `linearRelationObstructionPullback`, `eval_linearRelationObstructionPullback` |
| evaluating a real polynomial through the real-to-complex cast | `eval₂_ofRealHom_eq` |
| **one spectrum escaping every relabeling makes the parameter obstruction a nonzero polynomial** | `linearRelationObstructionPullback_ne_zero` |
| conversely, wherever the relation itself vanishes the obstruction vanishes (the identity relabeling is one factor) | `eval_linearRelationObstructionPullback_eq_zero` |

Together these two give `(L2)` outright: if `∑ c_i E_i` vanished on a nonempty open set `U`, the
obstruction — a genuine polynomial in the parameters — would vanish on `U`, hence identically,
contradicting the first theorem.  What is left is only to feed in the escaping spectrum, which the
`ℂ`-coefficient lemma inside `HermitianLocalExtensionRelationEscape` supplies, and to quote the
corpus's "a nonzero complex polynomial has meagre, null real zero set"
(`ComplexPolynomialRealParameterGenericity`).

### The escape half is built, and it needed no new mathematics (2026-08-22)

`HTGeometry/ComplexPermutedSpectralEscape.lean` (new, axiom-clean, wired) supplies the last generic
piece.  The corpus carried simultaneous escape only for balanced *integer* characters
(`AnalyticSpectralRelationEscape`); nothing in the argument uses integrality, so the complex version
is the same reduction to the finite-escape engine.

| Card item | Declaration |
|---|---|
| one labeling of a complex relation, and its coefficient packet | `permutedComplexRelation`, `permutedComplexCoefficient`, `sum_permutedComplexCoefficient_eq_relation` |
| a nonzero balanced complex coefficient vector stays nonconstant after every relabeling | `permutedComplexCoefficient_not_constant` |
| analyticity of each labeled relation, over `ℂ` and over `ℝ` | `permutedComplexRelation_analyticOnNhd`, `permutedComplexRelation_analyticOnNhd_real` |
| **simultaneous escape**, in both the complex-parameter and the **real-parameter** form a Hermitian family actually supplies | `exists_all_permutedComplexRelation_ne_zero`, `exists_all_permutedComplexRelation_ne_zero_real` |

The real-parameter form is the one the chart uses: parameters real, branches complex-valued and
real-analytic, exactly as in `exists_hermitianLocalExtension_action_ne_target` — the corpus's
`ℂ`-coefficient affine escape, which provides the per-labeling hypothesis `hlabel`.

**The `(L2)` chain is therefore closed end to end in generic form:**

```text
exists_hermitianLocalExtension_action_ne_target        (per labeling, ℂ coefficients — corpus)
  + permutedComplexCoefficient_not_constant            (nonconstancy after relabeling)
  → exists_all_permutedComplexRelation_ne_zero_real    (one point escapes every labeling)
  → linearRelationObstructionPullback_ne_zero          (parameter obstruction is a nonzero polynomial)
  → not_relation_on_open_of_escape                     (L2: no relation on any nonempty open set)
  → exists_nondegAt_of_no_constant_combination         (nondegeneracy at every point)
  → theoremA_analytic                                  (a.e. parameter is not simultaneously VWA)
```

What is left is instantiation at the card's chain family: writing the path-local Hermitian family as
a local extension, checking the connected interaction lift, and supplying a maximally projective
base — all of which the corpus's `NearestNeighborQuditPathGenericityLaw` already assembles for the
rational statement.

## The whole chain from escape to exponent is Lean-closed (2026-08-22, later)

Ten new modules close everything on this card except the realization of the card's *specific* chain
family as a local extension.  Every declaration is unconditional and axiom-clean
(`propext, Classical.choice, Quot.sound`), and all are wired into `GaloisForLFunctions.HTGeometry`.

### The escape property, and its affine form

Nondegeneracy rules out combinations of the energies that are *constant* on a chart, not merely
zero, so the whole obstruction stack was carried across to affine relations.

| Card item | Declaration | Module |
|---|---|---|
| a set of Hamiltonians whose spectra escape a prescribed homogeneous relation, and monotonicity in the set | `SpectrumEscapesRealRelations`, `.mono` | `SpectrumRealRelationEscape` |
| **(L2) for a real-affine Hermitian family** | `not_relation_on_open_of_spectrumEscapes` | same |
| the local-extension slice escapes every homogeneous real relation | `hermitianLocalExtensionSlice_spectrumEscapesRealRelations`, `not_relation_on_open_of_localExtensionSlice` | `LocalExtensionSpectrumRealRelationEscape` |
| the **affine** labeling-orbit obstruction `Ω_{c,t} = ∏_σ (∑_i c_i X_{σ i} - t)`: symmetric, nonzero for `c ≠ 0`, a polynomial in the elementary symmetric functions | `affineRelationPoly`, `affineRelationOrbit`, `affineRelationOrbit_isSymmetric`, `affineRelationOrbit_ne_zero`, `affineRelationCoefficient`, `eval_affineRelationCoefficient_esymm` | `AffineSpectralRelationOrbitPolynomial` |
| its pullback through a characteristic-coefficient family, and **(L2') for a polynomial matrix family** | `affineRelationObstructionPullback`, `not_affineRelation_on_open_of_escape`, `not_affineRelation_on_open_of_rootPacket_escape` | `AffineRelationObstructionPullback` |
| simultaneous escape from a prescribed value, and the **affine local-extension escape** | `exists_all_permutedComplexRelation_ne_target_real`, `exists_hermitianLocalExtension_realRootPacket_affineOrbit_ne_zero` | `HermitianLocalExtensionAffineRelationEscape` |
| the affine escape property, **(L2') for a real-affine family**, and the local-extension slice instance | `SpectrumEscapesAffineRelations`, `not_affineRelation_on_open_of_spectrumEscapes`, `hermitianLocalExtensionSlice_spectrumEscapesAffineRelations`, `not_affineRelation_on_open_of_localExtensionSlice` | `AffineSpectrumRelationEscape` |

The corpus already owned the affine half of the analytic core
(`hermitianLocalExtension_constantAction_coefficients_constant` carries an arbitrary target), so
only the finite simultaneous escape had to be retargeted.

### Lemma 2, in full

| Card item | Declaration | Module |
|---|---|---|
| the balanced coefficient vector a constant combination of anchored gaps produces, and of gap ratios (where the constant is absorbed by the clock gap, so the relation is *homogeneous*) | `anchoredRelationCoefficient`, `gapRatioRelationCoefficient` and their sum/value/nonvanishing lemmas | `SpectralGapRatioExtremality` |
| **no nonzero constant combination** of the anchored gaps, respectively of the gap ratios | `no_constant_combination_anchoredGap`, `no_constant_combination_gapRatio` | same |
| **extremality of the two maps** (Theorem A applied) | `theoremA_anchoredGap`, `theoremA_gapRatio` | same |
| the simple-spectrum chart, and analyticity of the two maps on it | `simpleEnsembleLocus`, `isOpen_simpleEnsembleLocus`, `analyticOnNhd_anchoredGapMap`, `analyticOnNhd_anchoredGapRatioMap` | `SortedSpectrumGapExtremality` |
| **extremality for the sorted spectrum of `∑_a θ_a P_a`** | `theoremA_sortedGap`, `theoremA_sortedGapRatio` | same |

### Lemma 1 as a limit, and the exponent law

`SimultaneousDirichlet` had the two halves of Lemma 1 as inequalities; the limit itself needed the
divergence of the first hit time, which is where "not very well approximable" enters a second time.

| Card item | Declaration | Module |
|---|---|---|
| distance to the nearest integer, and its comparison with `latticeClose` | `latticeDist`, `latticeClose_iff_latticeDist_lt`, `latticeDist_eq_zero_iff` | `FirstHitExponentLaw` |
| the first hit time is attained | `firstHit_set_nonempty`, `firstHit_mem`, `one_le_firstHit` | same |
| a vector that is not very well approximable has **no positive integer multiple in the lattice** | `notMem_intRange_of_not_vwa` | same |
| hence the first hit time **diverges** as the radius shrinks | `tendsto_firstHit_atTop` | same |
| the Dirichlet half as a quotient bound, and its vanishing correction `m·log(1+r)/log(1/r)` | `log_firstHit_div_log_le`, `tendsto_dirichletCorrection` | same |
| **`(9)`: the first-hit exponent is exactly `m`** | `tendsto_log_firstHit_div_log` | same |
| **the discrete and winding recurrence exponents, almost everywhere** | `ae_tendsto_log_firstHit_sortedGap`, `ae_tendsto_log_firstHit_sortedGapRatio` | `SpectralRecurrenceExponentLaw` |

With `scale = 2π`, `anchor = 0` and `ι k = k+1` the first is exactly `(3)`; with `anchor = 0`,
`clock = 1` and `ι k = k+2` the second is exactly the winding form of `(6)`, and `Lemma 4`
(`WindingReturnEquivalence`) converts it to continuous time.

### What remains on this card

**One item.**  The card's own family — traceless onsite plus nearest-neighbour Hermitian terms on an
open path of `n` qudits — has to be exhibited as a real-affine Hermitian family whose range contains
a local-extension slice with (a) maximally projective base energies, (b) simple product spectrum,
(c) connected interaction lift.  Then `hermitianLocalExtensionSliceAffine_spectrumEscapesAffineRelations`
plus `SpectrumEscapesAffineRelations.mono` gives the escape hypothesis of
`ae_tendsto_log_firstHit_sortedGap`, and the card's boxed statements follow with no further
mathematics.

That realization is exactly the corpus's inductive leaf extension
(`exists_physicallyRealizedTensorTree_leafExtension`, `IsPhysicalLeafChart`): the last site of the
chain is the new local factor `ρ`, the base energies are the eigenvalues of a local Hamiltonian on
the first `n-1` sites, and the interaction lift is the single new edge.  The remaining work is
bookkeeping in that stack, not new mathematics.

## CLOSED: the card's boxed theorems are Lean-proved unconditionally (2026-08-22)

The chain family itself is now formalized, so `(3)` and the winding form of `(6)` are unconditional
Lean theorems.  The last step was the observation that the whole chain is **one leaf extension of
the chain one site shorter**, attached at its last site — so the local-extension escape applies to
the chain's own local Hamiltonian space, with no new construction.

| Card item | Declaration | Module |
|---|---|---|
| characteristic roots and the escape property transport along a rectangular unitary coordinate change | `card_eq_of_coordinateUnitary`, `matrixCharpolyRelation_eq_zero_of_coordinate`, `SpectrumEscapesAffineRelations.ofCoordinate` | `CoordinateSpectrumRelationTransfer` |
| one coded layer shift makes the whole product spectrum simple | `exists_codedIntegerLayerShift_injective` | `LeafExtensionSpectrumRealRelationEscape` |
| **the local Hamiltonian space of one leaf extension escapes every constant real relation** | `leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations` | same |
| relabelling the carrier, and the escape property in canonical submodule coordinates | `matrixCharpolyRelation_reindex`, `SpectrumEscapesAffineRelations.reindex`, `.ofSubmodule` | `SubmoduleSpectrumRelationEscape` |
| real diagonal matrices escape every constant real relation (the unrestricted two-site architecture) | `exists_injective_escaping_energy`, `diagonalSet_spectrumEscapesAffineRelations` | `DiagonalSpectrumRelationEscape` |
| **adjoining one leaf at the last vertex of a path is the next path** | `leafPathEquiv`, `leafGraphExtension_comap_pathGraph` | `QuditPathLeafArchitecture` |
| **the open qudit chain, with the escape property of its exact onsite-plus-nearest-neighbour Hamiltonian space** | `exists_quditPathChain_spectrumEscapes` | `QuditPathChainEscape` |
| a simple root packet makes the canonical eigenvalues injective; an escaping family is nonzero and has a simple-spectrum chart | `hermitianEigenvalues_injective_of_rootPacket`, `exists_ne_zero_of_spectrumEscapes`, `exists_chart_of_spectrumEscapes` | `QuditPathChainRecurrenceExponent` |
| the chain in canonical coordinates | `exists_quditPathChain_coordinateFamily` | same |
| **`(3)`: the discrete recurrence exponent is exactly `q^n − 1`, almost everywhere** | `exists_quditPathChain_discreteRecurrenceExponent` | same |
| **the winding form of `(6)`: exponent `q^n − 2`** | `exists_quditPathChain_windingRecurrenceExponent` | same |

Both capstones return, besides the exponent law, the architecture identity
`T.graph = comap eObs (pathGraph n)`, the provenance of the coefficient family as the canonical
generators of `T.hermitianLocalHamiltonianSubmodule`, and a **witness chart** — a nonempty
preconnected open subset of the simple-spectrum locus — so the statement is not vacuous.

`Lemma 4` (`WindingReturnEquivalence`) converts the winding exponent to the continuous first-return
time, and the quadratic-deficit rescaling `(7)` is `QuadraticDeficitRescaling`; both were already
Lean-closed.

Every declaration is unconditional, hypothesis-free and axiom-clean
(`propext, Classical.choice, Quot.sound`), and all modules are wired into
`GaloisForLFunctions.HTGeometry`.

**Scope note.**  The exponent laws are stated on an arbitrary preconnected open chart of the
simple-spectrum locus, which is exactly where the ordered spectrum is analytic; the witness chart
theorem shows such a chart exists.  This is the faithful reading of the card's "for Lebesgue-almost
every `H`": the ordered gap map is not analytic across spectral collisions, and the collision locus
is closed with empty interior.
