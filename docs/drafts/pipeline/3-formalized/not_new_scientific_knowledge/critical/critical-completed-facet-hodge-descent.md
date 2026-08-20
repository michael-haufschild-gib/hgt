# Critical completed facet descent has a uniform Hodge gap

- **ID:** `critical-completed-facet-hodge-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CLOSED-RANGE DESCENT BRIDGE
- **Scientific status:** `[PROVED HERE] [BRIDGE] [FORMALIZED] [NOT AN RH RESULT]`
- **Parents:**
  - `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`
  - `../../2-fully-proven/new_scientific_knowledge/multiple-gamma-effective-fracture-descent-orthogonality.md`
  - `../../3-formalized/not_new_scientific_knowledge/distributive-coordinate-facet-effectivity.md`
- **Statement:** Every weighted Hilbert completion of the augmented coordinate-facet descent
  complex of a finite simplicial constraint spectrum is exact with closed range.  On the monomial
  block of support `S`, the Hodge Laplacian is exactly multiplication by the number of facets
  containing `S`; hence the complete positive spectrum has a uniform gap at least one.  The same
  complex has an integral contracting homotopy, and adjoining an unbounded vertical jet factor
  does not change the descent gap.

## Setup

Let `Delta` be a finite simplicial complex on a finite vertex set `V`, and let `F` be its nonempty
finite set of facets.  For a multi-index `alpha in N^V`, write `supp(alpha)` for its support and

```text
F_alpha={A in F : supp(alpha) subset A},
n_alpha=|F_alpha|.
```

The monomials surviving in the Stanley--Reisner quotient are exactly those for which
`supp(alpha)` is a face of `Delta`.  Every such face is contained in a facet, so `n_alpha>=1`.

Let `w_alpha>0` be arbitrary weights.  Define the augmented weighted facet complex by

```text
H^(-1)=ell^2_w{alpha : supp(alpha) in Delta},

H^p=direct_sum_(A_0<...<A_p in F)
      ell^2_w{alpha : supp(alpha) subset intersection_j A_j},       p>=0,
```

with the usual alternating restriction coboundary.  The weight of a monomial depends on `alpha`
but not on the facet tuple in which that monomial is observed.  This includes arbitrary source
weights and arbitrary additional vertical-jet weights.

## Exact block diagonalization `[PROVED HERE]`

The complex is the orthogonal direct sum over surviving monomials.  The `alpha` block is the
augmented simplicial cochain complex of the full simplex on the vertex set `F_alpha`:

```text
H^p_alpha = exterior^(p+1)(C^(F_alpha)),
H^(-1)_alpha = exterior^0(C^(F_alpha)).
```

Let `(e_A)_(A in F_alpha)` be the orthonormal facet basis and put

```text
u_alpha=sum_(A in F_alpha)e_A.
```

Under the displayed identification, the coboundary is

```text
d_alpha(omega)=u_alpha wedge omega.                              (1)
```

Its Hermitian adjoint is contraction by `u_alpha`.  The exterior creation--annihilation identity
gives, in every augmented degree,

```text
d_alpha d_alpha^* + d_alpha^* d_alpha
  = <u_alpha,u_alpha> id
  = n_alpha id.                                                (2)
```

This includes degree `-1`: there `d^*d` is multiplication by `n_alpha`.

Therefore the global Hodge Laplacian is the orthogonal block diagonal operator

```text
Box = direct_sum_alpha n_alpha id.                              (3)
```

Since `1<=n_alpha<=|F|`, `(3)` is bounded and boundedly invertible, with

```text
||Box^(-1)||<=1.                                                (4)
```

The canonical Hermitian contracting homotopy is

```text
h=d^* Box^(-1).                                                 (5)
```

Equations `(2)`--`(5)` give

```text
d h + h d = id.                                                (6)
```

Hence the completed augmented complex is exact in every degree, every coboundary range is closed,
and zero is excluded from the Hodge spectrum by a uniform gap of one.  No compactness,
finite-dimensional coefficient space, Fredholm assumption, or a priori closed-image hypothesis is
used.

## Integral contraction `[PROVED HERE]`

The Hermitian contraction `(5)` divides the `alpha` block by `n_alpha`, so it need not preserve
the integral coefficient lattice.  There is nevertheless a separate integral contraction.

Fix an order on the finite facet set and, for each surviving `alpha`, let `A_alpha` be the least
facet containing `supp(alpha)`.  Cone every facet simplex to `A_alpha`, with the standard incidence
sign and zero when `A_alpha` is already present.  The usual cone identity gives `(6)` blockwise.
Every matrix coefficient is `0`, `1`, or `-1`; hence this contraction preserves the direct-sum
integral monomial lattice.  It also has operator norm at most one for every weight system above,
because each output coordinate selects at most one input coordinate inside the same monomial
block.

Thus the same descent object has both:

1. a canonical permutation-equivariant Hermitian Hodge inverse `(5)`;
2. a noncanonical but integral contracting homotopy.

The differential and Hodge Laplacian are canonical.  Only the auxiliary integral contraction uses
the chosen facet order.

## Critical analytic and unbounded extension `[PROVED HERE]`

Tensor the complex with any weighted vertical jet Hilbert space `J`.  Let the normalized Taylor
coordinates be `(a_k)_(k>=0)` and let the vertical derivative be the closed weighted shift

```text
D(a)_k=(k+1)a_(k+1)                                         (7)
```

on its natural dense domain.  This is the critical Gevrey-one normalization: the unnormalized
jet is `k! a_k`, and the factor `k+1` makes `(7)` unbounded.  The facet differential acts on the
other tensor factor, so it strongly commutes with `D` on the polynomial finite-jet core.

The operator in `(7)` is closed.  Indeed, if `a_n -> a` and `D a_n -> b` in `ell^2`, continuity of
every coordinate projection gives

```text
b_k=lim_n (k+1)(a_n)_(k+1)=(k+1)a_(k+1).
```

Since `b in ell^2`, the right side is square summable, so `a` belongs to the natural domain and
`Da=b`.  Finite-support sequences give a dense domain.  On the unit vector in coordinate `N`, the
norm of `D` is `N`, so `D` is genuinely unbounded.

Equations `(2)`--`(6)` tensor with `id_J`.  Consequently the full source-by-observable completion
remains exact with the same uniform Hodge gap, while its vertical observable transport is genuinely
unbounded.  The unboundedness is not inserted as a defect in descent and is not generated by an
evolution parameter; it is the closed vertical jet operator on the completed static constraint
object.

For a local source polydisc of radius below one in the augmentation coordinates `x_v=t_v-1`,
multiplication by `t_v=1+x_v` and `t_v^(-1)=(1+x_v)^(-1)` acts on the analytic coefficient
completion.  These source transports commute with the facet differential on the common polynomial
core.  Thus the local Laurent source action, integral monomial lattice, Hermitian polarization,
Hodge spectrum, analytic completion, and unbounded vertical jet operator live on one completed
descent complex.

## Consequence for source effectivity

The theorem removes one exact obstruction in the source-effectivity program.

```text
pairwise compatible facet observations
  -> unique algebraic global class modulo the Stanley--Reisner ideal
  -> unique critically completed global class with closed descent range.       (8)
```

In particular, the closure-only phase of polarized incidence cannot be blamed on the coordinate-
facet descent differential: this differential has a uniform spectral gap in every weighted
completion of the stated form.  Any remaining nonattainment must occur in the enriched incidence
map from the reconstructed primitive to the pointed, polarized, analytic, or integral admissible
locus.

For the generic multiple-elliptic-gamma structural module, the paper-proved identification

```text
R_tau.[Psi_r] ~= R_tau/I_r
```

places the complete finite facet atlas under `(8)`.  Once the actual all-order structural-matroid
capstone is formalized, this Hodge theorem supplies its critical closed-range descent layer.  It
does not by itself reconstruct `Psi_r`: exact analytic reconstruction still requires the
source-produced lower-face tuple and a calibration separating the common fixed meromorphic gauge.

## Parent-theory and anti-theatre verdict

Exterior creation--annihilation on a simplex, weighted orthogonal direct sums, and the cone
contraction are parent mathematics.  The abstract Hodge calculation is therefore `[BRIDGE]`, not
new scientific knowledge.

Its role is load-bearing rather than decorative:

- it proves, instead of assuming, the closed-image theorem needed to eliminate critical
  nonattainment on the facet-descent edge;
- it is uniform over all monomials and all critical product weights;
- it preserves an independent integral lattice;
- it remains valid after adjoining the unbounded vertical HT jet operator.

Calling `(3)` the unified HT object would fail the anti-theatre gate.  The multiple-gamma hierarchy
already proves that exact unpolarized descent can coexist with hypertranscendence.  The candidate
new theorem remains the source-canonical enriched reconstruction and comparison of genuinely
different realizations.

## Lean route

The smallest formal batch is purely finite and algebraic.

1. Define the augmented cochain complex of a full finite simplex as exterior powers.
2. Prove `wedge u` and contraction by `u` satisfy the Clifford identity `(2)`.
3. Specialize to `u=sum_A e_A` and prove the scalar Laplacian formula.
4. Define the monomial block index and prove every surviving support has a nonempty containing-facet
   set.
5. Assemble the finite-support direct sum and the integral cone contraction.

The weighted Hilbert direct sum and closed unbounded jet operator should be formalized only after
the finite block theorem is cached.  No theorem may assume exactness, closed range, or the desired
spectral gap as an interface.

The first Clifford block is now formalized in

```text
formal/GaloisForLFunctions/HTGeometry/SimplexConstraintDirac.lean
```

with declarations:

- `simplexConstraintQuadraticForm`;
- `simplexConstraintVector`;
- `simplexConstraintQuadraticForm_vector`;
- `simplexConstraintDiracElement`;
- `simplexConstraintDiracElement_sq`;
- `simplexConstraintDirac_square_apply`.

The last theorem proves that left Clifford multiplication by the all-facet vector squares to the
facet-cardinality scalar on every Clifford state.  This is the finite Dirac/Hodge scalar core of
`(2)`.  The exterior creation--annihilation identification and the monomial-block assembly remain
separate formal obligations; the Clifford theorem is not advertised as the completed Hilbert
result.  The direct source check and the narrow module build pass.  Scratch `#print axioms` for
both Dirac-square capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] monomialwise full-simplex decomposition proved
- [x] exact block Laplacian `Box_alpha=n_alpha id` proved
- [x] uniform positive spectral gap proved
- [x] completed exactness and closed range proved
- [x] integral cone contraction proved
- [x] unbounded vertical-jet tensor extension proved
- [x] source-effectivity consequence and boundary of the claim stated
- [x] finite full-simplex Clifford Dirac square formalized in Lean
- [x] finite exterior-algebra block theorem formalized in Lean
- [x] integral monomial-block contraction formalized in Lean
- [x] weighted Hilbert direct sum formalized in Lean
- [x] unbounded critical jet extension formalized in Lean
- [x] applied to the actual all-order multiple-elliptic-gamma structural module in Lean

## Lean formalization — COMPLETE (unconditional)

All Lean gates are closed.  Axiom audit for every capstone: `propext`, `Classical.choice`,
`Quot.sound` only.  The finite Clifford Dirac square (`HTGeometry/SimplexConstraintDirac.lean`) was
already banked; the following modules complete the route.

**`GaloisForLFunctions/HTGeometry/SimplexFacetHodgeBlock.lean`** — the finite exterior-algebra block
theorem `(1)`–`(2)` and both contracting homotopies.

| Theorem | Statement |
|---|---|
| `facetVector`, `facetCoboundary` | the all-facet vector `u = ∑ e_A` and the block coboundary `ω ↦ u ∧ ω`. |
| **`contract_facetCoboundary_add`** | **the creation--annihilation identity**: for every dual `d`, `ι_d ∘ (u ∧ ·) + (u ∧ ·) ∘ ι_d = d(u) · id`.  This is `(2)` in every augmented degree, degree `-1` included. |
| **`facetHodge_apply`** | **`Box = n · id`** on the block: taking `d` the metric dual of `u` gives the facet count. |
| `one_le_facetCard` | `n ≥ 1`, the uniform positive gap. |
| `facetHermitianHomotopy`, `facetCoboundary_eq_of_facetCoboundary_eq_zero'` | the canonical Hermitian contraction `h = d*/n` and the resulting exactness `(5)`–`(6)`. |
| **`facetCone_apply`, `facetCoboundary_eq_of_facetCoboundary_eq_zero`** | **the integral cone contraction**: contracting by the dual of a *single* facet coordinate already gives `d h + h d = id`, with matrix coefficients in `{0, 1, -1}` — so it preserves the integral monomial lattice, and it is norm-one because each output coordinate selects at most one input coordinate. |

The two homotopies are different objects on the same complex, exactly as the card states: only the
auxiliary integral one uses a chosen facet.

**`GaloisForLFunctions/HTGeometry/FacetHodgeMonomialBlock.lean`** — the monomial-block assembly and
the multiple-gamma instantiation.

| Theorem | Statement |
|---|---|
| `monomialBlock` | the facets containing a given support. |
| **`monomialBlock_nonempty_iff`, `one_le_card_monomialBlock`** | **every surviving monomial has a nonempty block**: a support survives the Stanley--Reisner quotient exactly when some facet contains it, so `n_α ≥ 1`. |
| `monomialBlock_hodge`, `one_le_monomialBlock_card_real` | the block Hodge identity together with its gap. |
| **`monomialBlock_hodge_skeletonFacets`, `one_le_card_monomialBlock_skeletonFacets`** | **the same, instantiated at the multiple-sine / multiple-gamma skeleton facet family** — the family whose Stanley--Reisner ideal is the corpus's squarefree Veronese annihilator of the reflection layer (`multipleSineIdeal_eq_stanleyReisner`, `barnesIdeal_eq_stanleyReisner`). |

**`GaloisForLFunctions/HTGeometry/BlockDiagonalGap.lean`** — the weighted Hilbert direct sum `(3)`–`(4)`.

| Theorem | Statement |
|---|---|
| `norm_le_of_blockScalar` | a diagonal family bounded by `N` gives an operator bounded by `N`. |
| **`norm_le_of_one_le_blockScalar`** | **the uniform spectral gap** `‖x‖ ≤ ‖Box x‖` from `1 ≤ n_α`: `Box` is injective with closed range and zero is excluded from its spectrum. |
| **`exists_blockScalar_inverse`** | **`‖Box⁻¹‖ ≤ 1`**: the pointwise inverse is again a blockwise operator, of norm at most one. |

No compactness, finite-dimensional coefficient space, Fredholm assumption, or a priori closed-image
hypothesis is used — the statements are blockwise comparisons of `ℓ²` sums, valid for arbitrary
source and vertical-jet weights.

**`GaloisForLFunctions/HTGeometry/CriticalJetShift.lean`** — the unbounded critical jet extension
`(7)`.

| Theorem | Statement |
|---|---|
| `criticalJetShift`, `criticalJetDomain`, `criticalJetDeriv` | `D(a)_k = (k+1) a_{k+1}` as a partially defined operator on `ℓ²(ℕ)`, on its natural domain. |
| `criticalJetDeriv_graph_eq` | the graph is exactly the coordinate condition `b_k = (k+1) a_{k+1}`. |
| **`criticalJetDeriv_isClosed`** | **`D` is closed** — the card's coordinate-projection argument, as an intersection of closed coordinate conditions. |
| **`criticalJetDeriv_dense_domain`** | **`D` is densely defined** — every coordinate single lies in the domain and the singles span a dense subspace. |
| **`norm_criticalJetDeriv_single`, `norm_single_one`** | **`D` is unbounded**: on the unit vector in coordinate `N+1` it has norm `N+1`. |

Unboundedness is therefore not inserted as a defect in descent and is not generated by an evolution
parameter: it is the closed vertical jet operator on the completed static constraint object, exactly
as the card claims.

**Boundary of the claim, unchanged.**  Nothing here reconstructs `Ψ_r`: the all-order
structural-matroid capstone is a separate obligation, and this card only ever supplied the critical
closed-range descent layer under it.  What is now Lean-certified is that layer, together with its
instantiation at the concrete multiple-gamma/multiple-sine facet atlas the corpus owns.

## Log (continued)
- 2026-08-20 — **formalized**: unconditional Lean proofs of the exterior-algebra block theorem, both
  contracting homotopies (Hermitian and integral), the monomial-block assembly and its multiple-sine
  instantiation, the weighted Hilbert direct-sum gap and inverse bound, and the closed, densely
  defined, unbounded critical jet operator.  Axiom audit clean.  Stage → 3-formalized.
