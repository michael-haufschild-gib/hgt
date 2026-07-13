# No diagonal Hilbert or finite-index superspace can normalise the zeta pairing in the critical strip

- **ID:** `dirichlet-diagonal-hilbert-rigging-abscissa-barrier`
- **Stage:** 3-formalized
- **Type:** THEOREM / SUPERSPACE ROUTE GATE
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `prime-fisher-superspace-unimodular-phase-blindness`; separate from RHTower Routes A--D
- **Lean:** `formal/GaloisForLFunctions/RHTower/DirichletHilbertRiggingBarrier.lean`

## Statement

Let `sigma` be real. There exists a positive diagonal coefficient-space Hilbert rigging in which

1. the Dirichlet state with coefficients `(n+1)^(-s)` belongs to the Hilbert space; and
2. the formal all-ones summation covector is bounded

if and only if `sigma>1`.

Thus no choice of diagonal weights, no finite change of metric signature, and no one-timelike-mode
DeWitt/Pontryagin completion can turn the analytically continued zeta value in
`1/2<Re(s)<=1` into a normal Hilbert-space matrix coefficient.

More generally, abandoning diagonal weights does not help if the integer modes remain a Bessel
family. No infinite Bessel family `{u_n}` can admit a Hilbert vector `Omega` with
`<u_n,Omega>=1` for every `n`.

## Proof

Fix positive weights `w_n` and give the coefficient basis squared norm `w_n`. The corresponding
Hilbert norm is

```text
||x||_w^2 = sum_n w_n |x_n|^2.                         (1)
```

The all-ones summation covector

```text
Omega(x)=sum_n x_n
```

is bounded on this space exactly when

```text
sum_n w_n^(-1) < infinity.                             (2)
```

Indeed, `(2)` gives boundedness by Cauchy--Schwarz, while applying a bounded `Omega` to the finite
vectors with coefficients `w_n^(-1)` gives the converse.

The Dirichlet state

```text
Psi_s = ((n+1)^(-s))_(n>=0)
```

belongs to the space exactly when

```text
sum_n w_n (n+1)^(-2 sigma) < infinity.                 (3)
```

If `(2)` and `(3)` both hold, Cauchy--Schwarz gives

```text
sum_n (n+1)^(-sigma)
  = sum_n [sqrt(w_n)(n+1)^(-sigma)] [1/sqrt(w_n)]
  < infinity.                                          (4)
```

The `p`-series criterion forces `sigma>1`.

Conversely, if `sigma>1`, choose

```text
w_n=(n+1)^sigma.
```

Then the series in both `(2)` and `(3)` equal `sum_n (n+1)^(-sigma)` and converge. This proves the
sharp equivalence.

Lean proves a pointwise weighted-square inequality

```text
2 a_n <= w_n a_n^2 + w_n^(-1)
```

and uses summable comparison to formalize the same Cauchy--Schwarz argument. The final declaration
is `admitsDiagonalHilbertRigging_iff`.

## Non-diagonal strengthening: the Bessel-frame barrier

Suppose `{u_n}` is any family in a complex Hilbert space with Bessel bound `B`, so for every finite
set `S` and vector `x`,

```text
sum_(n in S) |<u_n,x>|^2 <= B ||x||^2.                (5)
```

If a bounded summation vector `Omega` satisfied `<u_n,Omega>=1` for all `n`, then `(5)` would give

```text
|S| <= B ||Omega||^2                                 (6)
```

for every finite `S`, impossible because `N` has arbitrarily large finite subsets. Lean proves
`card_le_of_bessel_unit_response` and the global contradiction
`no_bessel_family_with_unit_response`.

This removes the most obvious non-diagonal escape: Riesz bases, frames, orthonormal systems, and all
other Bessel mode families are incompatible with a normal all-ones zeta summation vector. A
positive Hilbert realization would have to make the integer modes non-Bessel, losing bounded
synthesis and stable quantum superposition.

## Krein, DeWitt, and supersymmetric consequence

A diagonal Krein or Pontryagin metric replaces `(1)` by signs `epsilon_n in {+1,-1}` but retains the
fundamental Hilbert topology determined by `w_n`. Boundedness and state convergence are therefore
still governed by `(2)`--`(3)`. In particular:

- one negative conformal/scale mode does not move the abscissa from `1` to `1/2`;
- any finite negative index leaves the obstruction unchanged;
- a finite boson--fermion direct sum also leaves the obstruction unchanged componentwise.

So the Lorentzian signature of a finite-index superspace can describe a constraint once supplied,
but it cannot manufacture the analytic continuation pairing as a normal amplitude.

The same argument excludes a countably-Hilbert diagonal nuclear test space. Continuity of `Omega`
in a locally convex space defined by an increasing family of weighted Hilbert seminorms means that
`Omega` is bounded by one finite combination of those seminorms. If `Psi_s` belongs to the test
space, it belongs to that controlling Hilbert completion, and the sharp rigging theorem again forces
`Re(s)>1`. Thus a Gelfand triple does not help by merely adding more diagonal Sobolev/Gevrey norms:
in the critical strip both `Omega` and `Psi_s` remain on the distribution side, where their pairing
is not canonically defined.

## Exact boundary of the no-go

The sharp abscissa theorem assumes a coefficient-diagonal Hilbert topology, while the Bessel theorem
assumes stable bounded synthesis. Together they still do not exclude:

1. a genuinely non-diagonal prime--archimedean Gram operator whose integer modes are non-Bessel;
2. a singular/non-normal functional or an independently specified nuclear-space finite part;
3. an infinite-index indefinite completion; or
4. a quotient/cohomological construction in which analytic continuation is not represented by the
   all-ones coefficient covector.

At least one of these non-Fock mechanisms is mandatory for any superspace formulation of RH.

## Significance and novelty verdict

The sharp abscissa statement excludes an entire natural class of quantum/superspace
representations and strengthens the elementary observation that `(1,1,...)` is not in ordinary
`ell^2`. However, after project vocabulary is erased, its proof is the standard factorisation
`ell^1=ell^2 . ell^2` plus the `p`-series test. It is therefore a useful formal route gate, not new
scientific knowledge.
