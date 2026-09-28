# Mertens-clock prime defect is trace class, but the exact Xi inverse is not

- **ID:** `stc-mertens-trace-class-xi-divisor-barrier`
- **Stage:** 3-formalized
- **Type:** THEOREM and ROUTE OBSTRUCTION
- **Routes:** STC, RHist, U, theta source transport
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`
- **Dependencies:** `stc-poisson-mertens-clock-commutator.md`; Mertens' second theorem with its bounded first-Mertens error; the Riemann–von Mangoldt zero count; the exact theta-source determinant identity.

## Statement

Use the prime-cell isometry and notation of the dependency card. Thus
`A=UKU*` has step kernel `h(x_p-x_q)` on the harmonic prime cells,
`W` has convolution kernel `h(y-z)` on `L²(0,∞)`, and
`h(s)=sech²(s/2)`. Put `E=A-W`.

1. **Arithmetic trace-class upgrade.** `E` is a nonzero self-adjoint
   trace-class operator with `Tr(E)=0`; consequently it has a positive
   eigenvalue and infinitely many negative eigenvalues. The proof of
   trace-class admission only
   needs the quantitative Mertens-clock error
   `|x_p+B-y| ≤ D e^(-y)` on the cell of `p`, exponential spatial decay,
   and strip analyticity of `h`.
2. **Xi inverse class mismatch.** Let `B_θ` be the Hilbert–Schmidt theta
   source inverse whose regularized determinant is `XiC(z)/XiC(0)`
   (up to the fixed sign convention). Then `B_θ` is not trace class.
3. Consequently no bounded two-sided transport
   `B_θ=L E R+F`, with `L,R` bounded and `F` trace class, can hold.
   In particular bounded similarity, unitary conjugacy, or a trace-class
   completion of the prime defect cannot identify its determinant divisor
   with the exact Xi divisor.
4. **Positive survivor.** Since `A=W+E` with `E∈S₁` and zero trace, the resolvent
   difference is trace class wherever both resolvents exist. The
   relative Fredholm determinant
   `D_rel(λ)=det(I+E(W−λ)^(-1))` is analytic for
   `λ∈ℂ\[0,4]`; its zeros are exactly the discrete eigenvalues of
   `A` outside the universal band. This is a canonical arithmetic
   observable relative to the continuum bulk, without an asserted Xi
   identity.

This is a **class obstruction to a proposed bridge**, not a statement
that prime data cannot contribute to a different, singular or
scale-dependent bridge. It sharpens the earlier self-adjointness no-go:
the trace-ideal mismatch survives nonunitary bounded two-sided maps.

## Proof of the trace-class upgrade

Write `φ(y)=x_p+B` on prime cell `I_p`, and `δ(y)=φ(y)-y`. The constant
`B` cancels in differences, so the kernel of `E` is

```text
e(y,z) = h(y-z+δ(y)-δ(z)) - h(y-z).
```

The needed rate is already an exact Lean theorem:
`RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le` in
`Sieve/MertensSecondSharp.lean` bounds the error by
`(2*mertensFirstConst+1/2)/log N`. Its paper mechanism is also
visible in the Abel-summation identity in
`MertensSecondPrimeRecipSum.lean`. If
`A(t)=Σ_(p≤t)(log p)/p` and `A(t)-log t` is bounded, subtracting the
limit constant from that identity leaves

```text
Σ_(p≤t) 1/p - log log t - B
  = (A(t)-log t)/log t
    - ∫_t^∞ (A(v)-log v)/(v log²v) dv = O(1/log t).
```

At `t=p`, omit the last `1/p` to obtain `y_p=x_p+B+O(1/log p)`.
On `I_p` the cell width is `1/p`, so `δ(y)=O(1/log p)`.
Since `y=x_p+B+o(1)`, `1/log p=e^(-x_p)=O(e^(-y))`.
Thus `|δ(y)| ≤ D e^(-y)` after enlarging `D` for finitely many
initial cells. Choose an integer `J` so that `2D e^(-J)` is smaller than a
fixed strip radius `r<π`. Divide `[J,∞)` into unit intervals
`Q_j=[j,j+1)`. On `Q_j×Q_k` expand in the small displacement:

```text
e(y,z) = Σ_(m≥1) h^(m)(y-z)/m! · (δ(y)-δ(z))^m.
```

Each summand is a finite sum of terms
`c_(a,b) M_(δ^a) C_(h^(a+b)) M_(δ^b)` from `L²(Q_k)` to `L²(Q_j)`,
where `a+b=m`, `c_(a,b)=(-1)^b/(a!b!)`, and `C_g` denotes the
integral operator with kernel `g(y-z)`. The multipliers require no
regularity: their norms are at most `(D e^(-j))^a` and
`(D e^(-k))^b`.

For clarity, here is the local nuclear estimate used for the smooth
middle operator. If `g` is `C²` on `Q_j-Q_k`, then
`C_g:L²(Q_k)→H²(Q_j)` has norm bounded by a constant times the
`L²(Q_j×Q_k)` norms of `g`, `g'`, and `g''`. The inclusion
`H²(Q_j)→L²(Q_j)` is trace class, with the same trace norm for every
unit interval. For example, extend boundedly from the interval to a
fixed periodic `H²` space and use its Fourier singular values
`(1+n²)^(-1)`, whose sum converges. Therefore

```text
‖C_g : L²(Q_k)→L²(Q_j)‖₁
  ≤ C Σ_(r=0)^2 ‖g^(r)(y-z)‖_(L²(Q_j×Q_k)).
```

The poles of `h(s)=sech²(s/2)` are at `s=(2n+1)iπ`. Cauchy's
estimate on any narrower strip, together with exponential decay in
`|Re s|`, gives constants `C,c>0` and `r₀>2D e^(-J)` such that

```text
Σ_(r=0)^2 ‖h^(m+r)(y-z)/m!‖_(L²(Q_j×Q_k))
  ≤ C (m+1)² r₀^(-m) e^(-c|j-k|).
```

Expanding `(δ(y)-δ(z))^m`, summing the binomial coefficients, then
summing `m≥1` gives

```text
‖1_(Q_j) E 1_(Q_k)‖₁
  ≤ C' (e^(-j)+e^(-k)) e^(-c|j-k|),  j,k≥J.
```

The double sum of this bound is finite. Absolute convergence of the
block operators in trace norm proves that the late-late compression
of `E` is trace class.

For the initial region `[0,J)`, only finitely many prime cells occur.
The corresponding row or column compression of `A` is finite rank:
its kernel is constant in the initial cell coordinate. The analogous
compression of `W` is trace class. Indeed each unit spatial block has
the displayed local `H²` nuclear bound, and its norm decreases
exponentially as the other block moves to infinity. Summing those
blocks proves the claim. The initial-initial compression is covered
by the same local bound for `W` and finite rank for `A`. Therefore
`E∈S₁` globally.

There is an exact trace cancellation, not merely a norm estimate.
Let `P_p` project onto `L²(I_p)`. The compression `P_p A P_p` is the
rank-one constant-kernel operator `1_(I_p)⊗1_(I_p)` and has trace
`μ_p`. The compression `P_p W P_p` has continuous positive-definite
kernel `h(y-z)` on the compact cell, is trace class by the same local
`H²` argument, and has trace
`∫_(I_p) h(0)dy=μ_p`. Hence
`Tr(P_p E P_p)=0` for every prime. The `P_p` are mutually orthogonal
and sum strongly to the identity. For a trace-class `E`, its trace is
the absolutely convergent sum of the traces of its diagonal
compressions. Therefore `Tr(E)=0`. In particular its ordinary
Fredholm determinant already equals its second regularization:
`det(I−zE)=det₂(I−zE)`.

The operator is not zero: on any prime cell, its kernel is
`1−h(y-z)`, strictly positive for almost every off-diagonal pair.
Its Hilbert–Schmidt kernel therefore has positive norm. A nonzero
self-adjoint trace-class operator with zero trace cannot have only
one eigenvalue sign. In fact the negative index is infinite. On the
infinite-dimensional mean-zero subspace of `L²(I_p)`, `U* f=0`, so
`A f=0` and `⟨Ef,f⟩=−⟨Wf,f⟩<0` for every nonzero `f` in that
subspace. Strict positivity of `W` follows from the strictly positive
Fourier transform
`ĥ(ξ)=4πξ/sinh(πξ)` (continuous value `4` at zero), itself the
`s=2` case of `HTGeometry/CoshFourierTransform.lean` after scaling.
The compact self-adjoint spectral theorem then gives infinitely many
negative eigenvalues. Trace neutrality forces at least one positive
eigenvalue. Thus arithmetic cell discretization creates an infinite
signed correction, despite positivity of both `A` and `W` separately.

The proof uses the **rate** in Mertens' formula. Mere `o(1)` would
only give the earlier compact equivalence and would not justify this
trace-class conclusion.

## Proof of the Xi inverse obstruction

`HedenmalmThetaTrace.lean` proves that the theta source inverse
`B_θ` is Hilbert–Schmidt, and
`HedenmalmThetaSourceDeterminantIdentity.lean` proves that its
Hilbert–Carleman determinant equals `XiC(z)/XiC(0)` (with its fixed
operator sign convention), where `XiC(z)=ξ(1/2+i z)` and `XiC(0)≠0`.
For a trace-class operator, the nonzero eigenvalues, counted with
algebraic multiplicity, have absolutely summable moduli. Zeros of its
regularized determinant are their reciprocals, with the same
multiplicities. Thus trace class would force

```text
Σ_(XiC(z)=0, multiplicity) 1/|z| < ∞.
```

This contradicts the unconditional Riemann–von Mangoldt count proved
in `RiemannVonMangoldt.lean`.
The number `N(T)` of ξ zeros with positive ordinate at most `T`
satisfies `N(T)∼T log T/(2π)`. Hence for all sufficiently large
dyadic `T`, the interval `(T,2T]` contains at least
`c T log T` zeros, counting multiplicity. If `s=β+iγ` is one of
them, its XiC coordinate is `z=γ+i(1/2-β)` and, since
`0<β<1`, `|z|≤2T+1/2`. The reciprocal sum over that dyadic band is
at least `c' log T`; disjoint bands force divergence. Thus
`B_θ∉S₁`.

Finally, `S₁` is a two-sided operator ideal. Bounded `L,R` and
trace-class `F` make `L E R+F` trace class, contradicting the
previous paragraph. This proves the no-go without assuming that the
transport preserves adjoints or positivity.

For the positive survivor, the resolvent identity gives

```text
(A−λ)^(-1)−(W−λ)^(-1)
  = −(A−λ)^(-1) E (W−λ)^(-1) ∈ S₁.
```

For `λ∉[0,4]`, `W−λ` is invertible and
`A−λ=(I+E(W−λ)^(-1))(W−λ)`. Analytic Fredholm theory gives the
stated relative determinant and its zero criterion. Since `A` is
positive self-adjoint, such zeros, if any, lie on the real axis above
`4`. This concrete survivor is stronger than the bare negative
trace-ideal statement: the arithmetic defect has an exact relative
spectral observable, but its direct physical-sheet zeros do not
yet encode the Xi divisor.

## Consequence for the actual RH gate

The prime Poisson/Mertens construction has a universal noncompact
Wiener–Hopf bulk and a trace-class arithmetic defect. The canonical
theta inverse carrying the full Xi divisor lives in `S₂\S₁`.
An exact source-to-theta route must therefore use an unbounded or
scale-dependent operation, or bring in additional non-trace-class
arithmetic/completion data. A bounded calibration of this defect,
even with any trace-class correction, cannot deliver the Xi divisor.
The still-open arithmetic theorem is an independent balance of the
theta eigenmode boundary ports; the existing theta metric and Green
identity only express that balance as an RH equivalent.

**Paper/Lean audit:** Every statement of this card is formalized in Lean
(certificate `stc-mertens-trace-class-xi-divisor-barrier-formalized.md`).
The Lean proofs use different mechanisms at three points: trace class via a
global factorization `E = T₂ + T₃ + T₅` through the oriented displacement
indicator (each piece a product of two Hilbert–Schmidt operators) instead of
local nuclear block bounds; `B_θ ∉ S₁` via the pinned Volterra structure
`B = i q P` and the pairing `⟨√2 sin(a_n t), P √2 cos(a_n t)⟩ = 1/a_n − 2/a_n³`
instead of the Riemann–von Mangoldt count; strict positivity of `W` via its
Laplace Gram representation and integer moments instead of Plancherel. No new axiom or premise is proposed. This card
does not establish RH, falsify RH, or identify a source-derived map to
the theta ports.

The later [theta CDF action and cross-frequency capacity theorem](theta-cdf-crossfrequency-rvm-capacity.md)
matches this prime clock to a literal theta-source action up to a
fixed `−log π` offset and a trace-class kernel difference. It also
shows that the determinant-bearing theta quotient obtains its
logarithm-squared spectral mass from cross-frequency coupling, which
this trace-class clock comparison cannot supply.

## Log

- 2026-09-28: formalized in Lean (`SchurKernelComposition`, `MertensClockDefectTraceClass`,
  `MertensClockDefectSignedSpectrum`, `SourceInverseTraceIdealNoGo`,
  `MertensClockRelativeDeterminant`; wired, oleans built, axioms standard); moved to stage 3.
