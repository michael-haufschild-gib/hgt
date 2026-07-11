# No diagonal Hilbert or finite-index superspace can normalise the zeta pairing in the critical strip

- **ID:** `dirichlet-diagonal-hilbert-rigging-abscissa-barrier`
- **Stage:** 3-formalized
- **Type:** THEOREM / SUPERSPACE ROUTE GATE
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `prime-fisher-superspace-unimodular-phase-blindness`; separate from RHTower Routes A--D
- **Lean:** `formal/GaloisForLFunctions/DirichletHilbertRiggingBarrier.lean`

## Statement

Let `sigma` be real. There exists a positive diagonal coefficient-space Hilbert rigging in which

1. the Dirichlet state with coefficients `(n+1)^(-s)` belongs to the Hilbert space; and
2. the formal all-ones summation covector is bounded

if and only if `sigma>1`.

Thus no choice of diagonal weights, no finite change of metric signature, and no one-timelike-mode
DeWitt/Pontryagin completion can turn the analytically continued zeta value in
`1/2<Re(s)<=1` into a normal Hilbert-space matrix coefficient.

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

## Krein, DeWitt, and supersymmetric consequence

A diagonal Krein or Pontryagin metric replaces `(1)` by signs `epsilon_n in {+1,-1}` but retains the
fundamental Hilbert topology determined by `w_n`. Boundedness and state convergence are therefore
still governed by `(2)`--`(3)`. In particular:

- one negative conformal/scale mode does not move the abscissa from `1` to `1/2`;
- any finite negative index leaves the obstruction unchanged;
- a finite boson--fermion direct sum also leaves the obstruction unchanged componentwise.

So the Lorentzian signature of a finite-index superspace can describe a constraint once supplied,
but it cannot manufacture the analytic continuation pairing as a normal amplitude.

## Exact boundary of the no-go

The theorem assumes a coefficient-diagonal Hilbert topology and a bounded summation covector. It
does not exclude:

1. a genuinely non-diagonal prime--archimedean Gram operator;
2. a singular/non-normal functional or a nuclear rigged-space finite part;
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
