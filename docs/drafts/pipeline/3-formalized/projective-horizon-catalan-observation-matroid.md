# Catalan observation matroid of reciprocal finite jets

- **ID:** projective-horizon-catalan-observation-matroid
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Classification:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** source-pure unit-jet constraint `X(t)Y(t)=1 mod t^(N+1)`
- **Statement:** Every complete mixed observation of raw coefficients of `X` and reciprocal coefficients of `Y=X^{-1}` is generically independent exactly when its four-state resolution word is a nonnegative two-coloured Motzkin path; its Jacobian is a skew-Schur polynomial, and there are `Cat_(N+2)` such bases.

## Theorem

Let `K` be a field of characteristic zero, let `N >= 0`, and put `n=N+1`.  In the rational function
field `F=K(x_0,...,x_N)`, set

```text
X(t) = sum_(i=0)^N x_i t^i,
Y(t) = X(t)^(-1) mod t^(N+1) = sum_(i=0)^N y_i t^i,
Q(t) = Y(t)^2 mod t^(N+1) = sum_(i=0)^N q_i t^i.
```

Choose `A,B subset {0,...,N}` with `|A|+|B|=n`, and observe

```text
O_(A,B) = {x_a : a in A} union {y_b : b in B}.
```

Let `C={0,...,N}\A`, so `|C|=|B|=:k`, and list
`C={c_1<...<c_k}` and `B={b_1<...<b_k}`.  With `q_d=0` for `d<0`, the following are equivalent:

1. `O_(A,B)` is a transcendence basis of `F/K`;
2. its full Jacobian determinant is nonzero;
3. `det(q_(b_i-c_j))_(1<=i,j<=k)` is nonzero;
4. `c_i <= b_i` for every `i`;
5. `|C intersect {0,...,r}| >= |B intersect {0,...,r}|` for every `r`.

Define

```text
lambda_i = b_(k+1-i) - (k-i),
mu_i     = c_(k+1-i) - (k-i),
h_d      = q_d/q_0,   h_0=1,   h_d=0 for d<0.
```

Then `lambda` and `mu` are partitions.  Condition 4 is `mu subset lambda`, and, up to the sign from
the raw identity rows,

```text
Jac(O_(A,B)) = q_0^k s_(lambda/mu)(h)
             = y_0^(2k) s_(lambda/mu)(h).                 (1)
```

At each resolution `i`, encode membership in `(C,B)` by

```text
(1,0): up          = neither x_i nor y_i is observed,
(0,1): down        = both x_i and y_i are observed,
(1,1): horizontal  = only y_i is observed,
(0,0): horizontal  = only x_i is observed.
```

This is a nonnegative two-coloured Motzkin path ending at height zero exactly in the equivalent
cases above.  Consequently the reciprocal observation matroid has `Cat_(n+1)=Cat_(N+2)` bases.

More precisely, after ordering the ground set as
`x_0,y_0,x_1,y_1,...,x_N,y_N`, its dual is the minor of Ardila's Catalan matroid `C_(n+1)` obtained
by contracting the forced first up-step and deleting the forced last down-step.

## Proof

### 1. Differential Toeplitz reduction

Differentiate the source constraint `XY=1`:

```text
dY = -Y^2 dX.
```

Taking coefficient `t^b` gives

```text
dy_b = -sum_(c=0)^b q_(b-c) dx_c,
partial y_b / partial x_c = -q_(b-c).                    (2)
```

The rows of the Jacobian belonging to observed raw coordinates are rows of the identity matrix.
Expanding along those rows deletes precisely the columns in `A`; the remaining columns are indexed
by `C` and the remaining rows by `B`.  Thus the full determinant is, up to sign,
`det(q_(b_i-c_j))`.  This proves `2 iff 3`.  In characteristic zero the Jacobian criterion for
rational functions in a purely transcendental field gives `1 iff 2`.

### 2. Exact nonvanishing criterion

Suppose `c_i>b_i` for some `i`.  In the first `i` rows, every nonzero entry lies in a column with
`c_j<=b_i`.  There are at most `i-1` such columns, so these rows have rank less than `i`; the
determinant vanishes.

Now suppose `c_i<=b_i` for every `i`.  Reverse both row and column orders.  This changes the
determinant by the square of the reversal sign and hence not at all.  Direct substitution gives

```text
lambda_i - mu_j - i + j
  = b_(k+1-i) - c_(k+1-j).
```

The strict increase of the `b_i` and `c_i` makes `lambda` and `mu` weakly decreasing and
nonnegative.  The inequalities `c_i<=b_i` are exactly `mu_i<=lambda_i`.  Factoring `q_0` from each
row leaves the skew Jacobi--Trudi determinant, proving (1) as a polynomial identity.

It remains to show that the skew-Schur polynomial does not vanish after the reciprocal-jet
substitution.  Put `z_d=x_d/x_0`.  Since `Q=X^(-2)`, coefficient extraction gives, for every `d>=1`,

```text
h_d = -2 z_d + P_d(z_1,...,z_(d-1))                     (3)
```

for a polynomial `P_d` over `K`.  Because `2` is invertible, (3) is a triangular polynomial
automorphism.  Hence `h_1,...,h_N` are algebraically independent over `K`.  For a valid skew shape
`lambda/mu`, `s_(lambda/mu)` is a nonzero polynomial: its semistandard-tableau expansion contains a
monomial with positive integral coefficient.  Therefore its image under (3) is nonzero.  Also
`q_0=y_0^2=x_0^(-2)` is nonzero in `F`.  This proves `3 iff 4`.

### 3. Prefix topology and enumeration

For two increasing `k`-subsets, `c_i<=b_i` for every `i` if and only if every initial interval
contains at least as many `c`'s as `b`'s.  Indeed, failure of the componentwise condition at the
least index `i` leaves `i` elements of `B` but at most `i-1` elements of `C` in the prefix ending at
`b_i`; conversely a deficient prefix forces some `i`-th `C` element to occur after the `i`-th `B`
element.  This proves `4 iff 5`.

The four membership states contribute height changes `+1,-1,0,0` respectively, so condition 5 is
exactly nonnegativity of the two-coloured Motzkin path.  Since `|B|=|C|`, its final height is zero.

There is also an explicit Dyck-path identification.  Start with an up-step; at resolution `i`, emit
an up-step exactly when `x_i` is unobserved and then an up-step exactly when `y_i` is unobserved,
using down-steps otherwise; finish with a down-step.  The four Motzkin steps become

```text
up -> UU,   down -> DD,   horizontal_1 -> UD,   horizontal_2 -> DU.
```

The Dyck height after a complete resolution prefix is one plus twice the Motzkin height.  The only
potential intermediate fall from height one is the `DU` case, which lands at zero and immediately
returns.  This is a bijection with Dyck paths of semilength `n+1`, hence the basis count is
`Cat_(n+1)`.

The up-step set, after removing the forced initial up-step and final down-step, is exactly the
complement of the observed coordinates.  Ardila's Catalan matroid uses these up-step sets as bases.
Thus the observation matroid is the dual of the stated Catalan-matroid minor.

## Physical meaning

The derivative index is a static resolution axis.  At each resolution a complete observer may see
neither projective chart, both charts, only the raw chart, or only the reciprocal chart.  The path
height is the exact latent-information balance: missing raw data creates one unit of unresolved
information and observing both charts spends one unit.  A complete cut reconstructs the finite jet
exactly when this balance never becomes negative.  Formula (1) is the cut amplitude; its vanishing
is the caustic at which that observer loses a local degree of freedom.  No time evolution, carrier,
or numerical experiment enters the theorem.

## Novelty and significance verdict

The reciprocal-jet derivation and the skew-Schur formula are a useful exact bridge, but the proposed
new combinatorial object is not new.  The explicit final construction identifies it with the dual
of a forced-step minor of the Catalan matroid.  Ardila introduced the Catalan matroid from Dyck-path
bases, and Bonin--de Mier--Noy developed the encompassing minor- and dual-stable lattice-path
matroids.  The Toeplitz-minor/skew-Schur identity is also established parent theory.  See:

- Federico Ardila, [The Catalan matroid](https://arxiv.org/abs/math/0209354);
- Joseph Bonin, Anna de Mier, and Marc Noy,
  [Lattice path matroids: enumerative aspects and Tutte polynomials](https://arxiv.org/abs/math/0211188);
- David Garcia-Garcia and Miguel Tierz,
  [Toeplitz minors and specializations of skew Schur polynomials](https://arxiv.org/abs/1706.02574).

Accordingly this theorem fails the `NOVEL` half of the dual gate and cannot be promoted as new
scientific knowledge.  Its value is the complete identification of the universal reciprocal-jet
observation topology with a classical matroid and the exact translation of its caustic amplitudes.

## RH impact audit

Applied to a hypertranscendental zeta or completed-zeta germ, the theorem classifies every finite
mixed raw/reciprocal jet packet that generically reconstructs the full finite jet.  The criterion
depends only on derivative order and universal inversion.  It is blind to zero locations, the
critical line, Euler-product orientation, and positivity, so it has no direct RH implication.  Any
RH use requires an arithmetic marking that selects or orients bases inside the Catalan minor while
remaining source-pure.

## Formalization boundary

The targeted Lean core should certify the differential Toeplitz law, the prefix-dominance law, and
the Dyck expansion.  Formalizing the entire existing theory of skew Schur polynomials or algebraic
matroids solely to restate the parent collision is not warranted.

## Lean formalization

- **Module:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonCatalanObservationMatroid.lean`
- **Closed capstone:** `projectiveHorizonCatalanObservationMatroid_unconditional`.
- **Differential Toeplitz law:** inherited from `arbitraryReciprocalJacobian_apply` and
  `arbitraryReciprocalJacobian_eq_neg_toeplitz` in
  `ProjectiveHorizonObservationMatroid`.
- **Exact prefix law:** `indexedObservation_componentwise_iff_prefixCount` proves both directions
  for the strictly increasing enumerations stipulated by the card; the equivalent height form is
  `indexedObservation_componentwise_iff_height_nonnegative`.
- **Dyck expansion:** `reciprocalObservationWordEquivDyckWord n` is the explicit bijection between
  length-`n` nonnegative balanced two-coloured observation words and Dyck words of semilength
  `n+1`.  Its encoder emits `UU`, `DD`, `DU`, and `UD` for the four local states and adds the forced
  initial `U` and terminal `D`; its decoder and both inverse laws are proved.
- **Catalan count:** `card_reciprocalObservationWord_length_eq_catalan n` proves the exact value
  `catalan (n+1)`, hence `Cat_(N+2)` for the card's `n=N+1` resolutions.
- **Boundary fidelity:** no skew-Schur or abstract algebraic-matroid surrogate was introduced; those
  parent-theory restatements are explicitly outside the card's stated Lean boundary.
- **Verification:** `lake env lean
  GaloisForLFunctions/HTGeometry/ProjectiveHorizonCatalanObservationMatroid.lean` and targeted
  `lake build GaloisForLFunctions.HTGeometry.ProjectiveHorizonCatalanObservationMatroid` pass.
  `#print axioms projectiveHorizonCatalanObservationMatroid_unconditional` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-26 - Added ordered-prefix converse, exact latent-height equivalence, explicit
  two-coloured-Motzkin/Dyck encoding and decoding, inverse laws, and Catalan cardinality; wired the
  module into the HTGeometry umbrella and promoted the card to stage 3.
