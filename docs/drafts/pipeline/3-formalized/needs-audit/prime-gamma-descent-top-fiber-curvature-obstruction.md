# Four-letter descent-top fiber curvature obstruction

- **ID:** `prime-gamma-descent-top-fiber-curvature-obstruction`
- **Stage:** 3-formalized
- **Type:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [POSITIVE SURVIVOR]`
- **Parent:** `../../1-in-progress/prime-gamma-signed-permutation-eulerian-rh.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SignedEulerianTopFiberCurvature.lean`
- **Statement:** Every scalar adjacent-descent cocycle that factors through the
  Visontai--Williams type-`B` descent/ascent-top signature has zero multiplicative curvature on
  every ordered four-label rectangle; for positive cocycles this forces rank-one separation.

## Exact literature frontier

`[LITERATURE]` Visontai--Williams define, for a signed permutation `sigma` with `sigma_0 = 0`,

```text
DT_B(sigma) = {max(|sigma_i|,|sigma_(i+1)|) : sigma_i > sigma_(i+1)},
AT_B(sigma) = {max(|sigma_i|,|sigma_(i+1)|) : sigma_i < sigma_(i+1)},
N(sigma)    = number of negative letters,
```

and prove stability of

```text
B_n(x,y;q) = sum_sigma q^N(sigma) x^DT_B(sigma) y^AT_B(sigma),   q > 0.
```

Their insertion recurrence is

```text
B_(n+1) = (q x_(n+1) + y_(n+1)) B_n
          + (1+q) x_(n+1)y_(n+1) partial B_n.
```

Thus variables are indexed by ascent/descent **top labels**, not descent positions or ordered
adjacent pairs.  Visontai's thesis explicitly notes that indexing the type-`A` refinement by
positions instead of tops destroys stability.  Branden--Leander enlarge the support to linear
extensions of certain posets, but their stable weights are again statistic monomials rather than
arbitrary adjacent-pair activities.  Later stable signed/colored/excedance refinements found in the
2024--2026 descendant literature change the tracked statistic; none of the audited primary sources
proves stability for arbitrary adjacent-edge weights.

Primary sources:

- M. Visontai and N. Williams, *Stable multivariate W-Eulerian polynomials*, Theorem 3.9,
  <https://doi.org/10.1016/j.jcta.2013.07.009>;
- M. Visontai, *Real-rooted polynomials in combinatorics*, Sections 2.3.2--2.3.3 and Remark 2.2.15,
  <https://www2.math.upenn.edu/grad/dissertations/VisontaiThesis.pdf>;
- P. Branden and M. Leander, *Multivariate P-Eulerian polynomials*,
  <https://arxiv.org/abs/1604.04140>;
- X. Yan and L. L. Liu, *The Real Stability of the Multivariate Eulerian Polynomials for
  Restricted Excedance Statistics*, <https://doi.org/10.1007/s11464-025-0210-1>.

`[NOVELTY UNVERIFIED]` No audited source states the four-letter edge-curvature obstruction or the
rank-one consequence below.  Search absence is not a priority proof.

## The exact collision

Work in `B_4` and consider the all-positive signed permutations

```text
sigma = (3,1,4,2),       tau = (3,2,4,1).
```

With the required boundary letter `sigma_0 = tau_0 = 0`, direct comparison gives

```text
DT_B(sigma) = {3,4} = DT_B(tau),
AT_B(sigma) = {3,4} = AT_B(tau),
N(sigma) = 0 = N(tau).
```

Consequently every Visontai--Williams monomial specialization assigns `sigma` and `tau` the same
weight, for every commutative coefficient monoid and every choice of `x`, `y`, and `q`.

Their descending adjacent pairs differ:

```text
DescEdge(sigma) = {(3,1),(4,2)},
DescEdge(tau)   = {(3,2),(4,1)}.
```

## `[PAPER-PROVED]` four-letter curvature theorem

Let `kappa(c,a)` be a scalar local factor attached to a positive descent `c > a`, with word weight
the product of its descent-edge factors.  If this word weight factors through the
Visontai--Williams signature `(DT_B,AT_B,N)`, then

```text
kappa(3,1) kappa(4,2) = kappa(3,2) kappa(4,1).                 (1)
```

More generally, after the unique order-preserving relabeling of any four labels `a < b < c < d`,

```text
kappa(c,a) kappa(d,b) = kappa(c,b) kappa(d,a).                 (2)
```

For positive real `kappa`, define multiplicative curvature

```text
Omega(a,b;c,d)
  = log kappa(c,a) + log kappa(d,b)
    - log kappa(c,b) - log kappa(d,a).
```

Equation `(2)` is exactly `Omega(a,b;c,d)=0`.

### Proof

The displayed comparison of the four adjacent slots proves equality of `DT_B`, `AT_B`, and `N`.
Signature factorization therefore makes the two word weights equal.  Expanding their two descent
edges gives `(1)`.  Order-preserving relabeling gives `(2)`.  Positivity permits logarithms, which
turn `(2)` into `Omega=0`.  No analytic, asymptotic, or RH input is used.

## `[PAPER-PROVED]` rank-one classification

Let labels be `1 < ... < n`, and suppose `kappa(c,a) > 0` for every `a < c` and `(2)` holds for every
`a < b < c < d`.  Then there are positive scalars `alpha_c` and `beta_a` such that

```text
kappa(c,a) = alpha_c beta_a       for every a < c.             (3)
```

### Proof

Set `alpha_c = kappa(c,1)` and `beta_1 = 1`.  For `a > 1`, set

```text
beta_a = kappa(a+1,a) / kappa(a+1,1).
```

Equation `(3)` is the definition when `c=a+1`, and is immediate when `a=1`.  If
`1 < a < a+1 < c`, apply `(2)` to columns `1,a` and rows `a+1,c`:

```text
kappa(a+1,1) kappa(c,a) = kappa(a+1,a) kappa(c,1).
```

Division by the positive first factor gives `(3)`.  These cases exhaust `a<c`.

## Hostile verdict and route consequence

`FALSE`: the SP-E card's former claim that a genuinely adjacent prime/Gamma factor
`kappa(p_i,p_j;sign_i,sign_j)` could simply be a nonnegative specialization of the known stable
type-`B` Eulerian polynomial.  That polynomial forgets edge pairing inside each top-signature fiber.
Compatibility forces zero curvature and, in the positive sector, rank-one separation.

This does **not** prove that every stable refinement has zero curvature.  It kills only direct
scalar specialization through the Visontai--Williams top signature.  A source may still enter by
changing the allowed signed-word support, by a different proved stable statistic, or through a
matrix/noncommutative stable pencil whose determinant retains holonomy.

## Positive survivor and exact insight

- **Strongest positive survivor:** multiplicative four-label curvature `Omega` is a canonical
  obstruction invariant for scalar SP-E insertion.
- **New insight:** first decisive finite test is rank four, not only the proposed `B_2 -> B_3`
  insertion check.  Two- and three-label agreement cannot certify descent-top factorization.
- **Representation lesson:** arithmetic completion curvature cannot be stored as scalar edge
  activity inside the known Eulerian stable cone.  It must become support, state, or matrix
  holonomy before scalar stable specialization.
- **Lean status:** `[LEAN-PROVED]`.  Exact declarations:
  `typeBTopSignature_signedWord3142_eq_signedWord3241`,
  `typeBTopWeight_signedWord3142_eq_signedWord3241`,
  `crossRelation_of_descentEdgeWeight_factorsThrough`, and
  `exists_rankOne_of_ordered_crossRelations`.

## Lean verification

- `lake env lean GaloisForLFunctions/HTGeometry/SignedEulerianTopFiberCurvature.lean` — pass;
- `lake build GaloisForLFunctions.HTGeometry.SignedEulerianTopFiberCurvature` — pass, `8655/8655`;
- `/tmp` `#print axioms` audit — only standard `propext`, `Classical.choice`, and `Quot.sound`;
- imported by `GaloisForLFunctions.HTGeometry` umbrella;
- no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration in the module.

The repository-wide `scripts/formal_tools.py lint` scan reports no finding in this module but exits
nonzero on three pre-existing, unrelated unreachable modules:
`RHTower.XiShiftedHardEdgeCayleyLimit`, `HTGeometry.DenseCoreHyperplane`, and
`HTGeometry.ProductStabilizerCliffordOrbit`.  Those dirty-worktree ownership issues were not changed.

## Gates

- [x] 0 -> 1 exact claim, collision, hostile scope, and primary-source frontier
- [x] 1 -> 2 complete dependency-closed paper proof
- [x] 2 -> 3 exact Lean theorem; targeted build, axiom audit, module lint, umbrella wiring
- [ ] 3 -> 4 independent priority review and publication package
