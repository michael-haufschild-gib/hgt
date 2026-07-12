# Joint Hurwitz monodromy-character hypertranscendence

- **ID:** `joint-hurwitz-monodromy-character-hypertranscendence`
- **Stage:** 3-formalized
- **Type:** theorem / new scientific knowledge
- **Scientific status:** `[PROVED] [FORMALIZED] [NOVELTY AUDIT PASSED — EXACT PARENT NOT LOCATED]`
- **Internal significance score:** 92/100
- **Publication:**
  `docs/drafts/pipeline/4-publication-ready/joint-hypertranscendence-of-hurwitz-zeta-functions.md`

## The law

Let $I$ be any index type, let $s:I\to\mathbb C$ satisfy $\operatorname{Re}s_j>1$, and suppose
that the augmented family $1,(s_j)_{j\in I}$ is linearly independent over $\mathbb Q$. Then the
upper-end meromorphic germs

\[
  a\longmapsto\zeta(s_j,a),\qquad j\in I,
\]

form a differentially algebraically independent family over $\mathbb C(a)$.

Equivalently, every finite mixed jet packet

\[
  \{\partial_a^k\zeta(s_j,a):j\in J,\ 0\leq k\leq N\},
  \qquad J\subset I\text{ finite},
\]

is algebraically independent over $\mathbb C(a)$. The same holds for every finite union of
Hurwitz ladders $\zeta(s_j+k,a)$.

The stronger intrinsic finite-family hypothesis is injectivity of the monodromy-character map

\[
  \alpha\longmapsto
  \prod_j e^{-2\pi i\alpha_js_j},\qquad \alpha\in\mathbb N^{J}.
\]

Rational linear independence of $1,(s_j)$ implies this injectivity.

## Exact mechanism

One loop around $a=-n$ acts on all exponent families with one common loop count:

\[
  (c_{j,n})_j\longmapsto(e^{-2\pi i s_j}c_{j,n})_j.
\]

The common cyclic power orbit is Zariski dense under monomial separation. Independent
branch points provide a product of these common-time orbits. At fixed $a$, the deformation-to-value
map is block diagonal, with block

\[
  W^{(j)}_{k,n}(a)=(a+n)^{-s_j-k}.
\]

Each block is a nonzero diagonal factor times a Vandermonde matrix and is invertible. The product
monodromy grid therefore maps onto the full finite ladder-value space, forcing every polynomial
relation to vanish coefficientwise.

The derivative law

\[
  \partial_a^k\zeta(s,a)=(-1)^k(s)_k\zeta(s+k,a)
\]

is an invertible diagonal coordinate change when $\operatorname{Re}s>1$. Canonical simultaneous
denominator clearing upgrades polynomial coefficients to $\mathbb C(a)$. Passing to the fraction
field of analytic upper-end germs turns the relation theorem into an object-level
`DifferentialIndependent` theorem.

## Formal theorem surface

The load-bearing declarations are:

- `mv_power_orbit_zero`
- `mv_power_grid_zero`
- `monomialValue_monoScalar_injective_of_linearIndependent`
- `jointRelA_move`
- `jointRelA_grid`
- `joint_hurwitz_ladder_independence`
- `joint_hurwitz_ladder_rational_independence`
- `joint_hzeta_rational_hypertranscendental_in_shift`
- `joint_hzeta_upperEnd_rectangle_algebraicIndependent`
- `joint_hzeta_upperEnd_differentialIndependent_finite`
- `joint_hzeta_upperEnd_differentialIndependent`

The final declaration has no relation predicate, no project-specific mathematical assumption, and
no unresolved analytic input. Its only mathematical conditions are the displayed half-plane and
rational-linear-independence conditions.

## Novelty gate

The closest parent surfaces found are distinct:

1. Lagarias--Li compute analytic continuation and linear monodromy spaces for the Lerch family;
   they do not give fixed-exponent nonlinear algebraic independence in the shift variable.
2. Joyner proves algebraic independence over $\mathbb C$ for integral-index Hurwitz polyzeta
   functions through difference equations and stuffle algebra. The present result concerns
   arbitrary complex nonresonant exponents, coefficients in $\mathbb C(a)$, all mixed derivatives,
   and arbitrary exponent families.
3. Amou--Katsurada study differential transcendence in the Dirichlet-series variable $s$, with the
   Hurwitz parameter fixed.
4. Hurwitz universality and functional-independence papers also vary the Dirichlet-series variable,
   not the shift variable.
5. Adamczewski--Dreyfus--Hardouin give a general dichotomy for homogeneous linear shift equations
   over the rational function field. For nonintegral $s$, the Hurwitz shift equation has forcing
   term $a^{-s}$ outside that coefficient field, and their result does not state joint independence.

No exact parent theorem was located for the monodromy-character law or its arbitrary-family
differential-field form. External expert review remains the final literature safeguard.

## Significance gate

- **Novelty: 28/30.** Exact fixed-exponent, shift-variable, mixed differential independence was not
  found in the parent literature; the closest integer-index and Dirichlet-variable results are
  materially different.
- **Mathematical depth: 25/30.** The proof couples analytic continuation, cyclic-character Zariski
  density, independent branch columns, block controllability, denominator clearing, and a concrete
  meromorphic differential field.
- **Reach: 24/25.** The theorem covers every finite jet order and arbitrary rationally independent
  exponent families, rather than one function or one fixed finite packet.
- **Verification: 15/15.** Every load-bearing mathematical statement has an exact axiom-clean
  declaration, including the object-level differential-independent conclusion.

Total: **92/100**. The score rests on the arbitrary-family differential-field law and the exact
parent separation, not on formalization or terminology.

## Positive boundary statement

When the monodromy-character map is not injective, its cyclic orbit has a lower-dimensional
algebraic closure. The positive residual datum is therefore the monodromy resonance lattice. The
present theorem identifies the monomial-separated chamber as a chamber of complete joint
differential freeness; other chambers require additional invariants to determine their remaining
relations.

## Gates

- [x] simultaneous branch-continuation law
- [x] common cyclic power-orbit density
- [x] product-grid density across branch points
- [x] block-Vandermonde controllability
- [x] rational coefficient clearing
- [x] arbitrary finite-family relation theorem
- [x] arbitrary-index object-level differential independence
- [x] primary-source parent comparison
- [x] standalone paper contains no internal formalization narrative
- [x] every mathematical claim in the paper lies on the proved theorem surface
