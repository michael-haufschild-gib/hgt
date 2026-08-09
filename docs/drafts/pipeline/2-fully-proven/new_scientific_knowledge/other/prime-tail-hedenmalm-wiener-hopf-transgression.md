# Theta Wiener--Hopf transgression and the Hedenmalm bulk--boundary polarity

- **ID:** `prime-tail-hedenmalm-wiener-hopf-transgression`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / OPEN-CORE REDUCTION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  - `hedenmalm-reflection-folded-dirac-source-defect.md`;
  - `critical-half-density-prime-tail-resolvent-law.md`;
  - `prime-tail-reflection-folded-second-order-resolvent.md`.

## Question

Is the map from the prime-tail half-line chart to Hedenmalm's theta eigenfunctions itself
missing, or is the obstruction more specifically the Hilbert boundary on which that map must
land?

## Setup

Use logarithmic theta coordinates

```text
k(x)=2 VarTheta_00(i exp(2x)),
D_x=-i partial_x,
XiC(alpha)=integral_R exp(i alpha x) k(x) dx.
```

The function `k` is real, even, Schwartz, and in `L^1(R)`.  For
`f in L^2(R_+)`, extend `f` by zero to the negative half-line and define

```text
(T_- f)(x)=integral_0^infinity k(x-L) f(L) dL,
(T_+ f)(x)=integral_0^infinity k(x+L) f(L) dL,           (1)

C f=(T_- f+T_+ f)/2,
S f=(T_- f-T_+ f)/2.                                    (2)
```

These operators are defined from the theta source before any zero is chosen.

## Theorem 1: bounded source transgression

The maps

```text
T_-,T_+,C,S : L^2(R_+) -> L^2(R)
```

are bounded, with

```text
||T_-||,||T_+|| <= ||k||_1,
T_+ f(x)=T_- f(-x).                                     (3)
```

Consequently `Cf` is even and `Sf` is odd.

### Proof

After zero extension, `T_- f=k*f`.  Young's convolution inequality gives the first bound.
Evenness of `k` gives

```text
T_- f(-x)=integral_0^infinity k(-x-L)f(L)dL
         =integral_0^infinity k(x+L)f(L)dL=T_+f(x).
```

The remaining assertions follow from `(2)`. QED.

## Theorem 2: exact boundary defect

For smooth decaying `f` on the half-line,

```text
partial_x C f=S(f'),
partial_x S f=k f(0)+C(f').                             (4)
```

Equivalently,

```text
D_x C f=-i S(f'),
D_x S f=-i k f(0)-i C(f').                              (5)
```

Thus the rank-one theta defect in the folded Hedenmalm system is exactly the endpoint trace of
an ordinary half-line derivative.  It is not an ad hoc forcing term.

### Proof

Integration by parts in `L` gives

```text
partial_x T_-f = k f(0)+T_-(f'),
partial_x T_+f =-k f(0)-T_+(f').                        (6)
```

Adding and subtracting `(6)` proves `(4)`, and multiplication by `-i` proves `(5)`. QED.

## Theorem 3: zero specialization is exactly Hedenmalm's fold

Let `rho` be a nontrivial Xi zero and set

```text
lambda=rho-1/2,
alpha=-i lambda,
```

so `lambda=i alpha` and `XiC(alpha)=0`.  First assume `Re lambda>0`, and put

```text
f_lambda(L)=exp(-lambda L).                              (7)
```

Then `f_lambda in L^2(R_+)`, and

```text
T_- f_lambda(x)
 =exp(-lambda x) integral_-infinity^x exp(lambda y)k(y)dy
 =u_alpha(x).                                           (8)
```

Since `k` and `XiC` are even and `XiC(-alpha)=0`,

```text
T_+ f_lambda=-u_(-alpha).                               (9)
```

Therefore

```text
C f_lambda=E_alpha,
S f_lambda=O_alpha,                                     (10)
```

where

```text
E_alpha=(u_alpha-u_(-alpha))/2,
O_alpha=(u_alpha+u_(-alpha))/2
```

are the even and odd Hedenmalm reflection folds.  Substitution of
`f_lambda'=-lambda f_lambda` into `(5)` gives exactly

```text
D_x E_alpha=-alpha O_alpha,
D_x O_alpha=-alpha E_alpha-i k,                         (11)

(D_x^2-alpha^2)E_alpha= i alpha k,
(D_x^2-alpha^2)O_alpha=-i D_x k.                        (12)
```

### Proof

Changing variables `y=x-L` in `(1)` proves `(8)`.  Changing variables `y=x+L` gives

```text
T_+f_lambda(x)
 =exp(lambda x) integral_x^infinity exp(-lambda y)k(y)dy.
```

The vanishing of the full integral

```text
integral_R exp(-lambda y)k(y)dy=XiC(-alpha)=0
```

turns the last expression into `-u_(-alpha)(x)`, proving `(9)` and `(10)`.
Equations `(11)` and `(12)` follow from `(5)` and `lambda=i alpha`. QED.

## Theorem 4: exact `L^2`/boundary wall

For the canonical input `(7)`,

```text
||f_lambda||_2^2=1/(2 Re lambda)                        (13)
```

when `Re lambda>0`.  More completely,

```text
Re rho>1/2  iff f_lambda is in L^2(R_+),
Re rho=1/2  iff f_lambda is bounded oscillatory and tempered but not in L^2,
Re rho<1/2  implies f_lambda has exponential growth and is not tempered.  (14)
```

The first alternative is intrinsic.  There is no `g in L^2(R_+)` with
`T_-g=u_alpha` when `alpha` is real and `XiC(alpha)=0`.

### Proof

Equation `(13)` is the elementary integral of `exp(-2 Re(lambda)L)`, and `(14)` follows
immediately.

For the last assertion, take Fourier transforms in `(8)`.  The zero extension of the
oscillation `exp(-i alpha L)` has boundary transform with a nonzero principal part proportional
to `(z-alpha)^{-1}`.  If `T_-g=u_alpha`, then away from the discrete real zero set of `XiC`,

```text
hat g(z)=1/(boundary constant times (z-alpha)).
```

This is not locally square-integrable at `z=alpha`, contradicting Plancherel.  Equivalently,
`T_-` is injective on `L^2(R_+)`: its full-line Fourier multiplier is `XiC`, which is nonzero
almost everywhere because it is a nonzero entire function.  The cancelled boundary pole cannot
be replaced by an `L^2` preimage. QED.

## Corollary: the positive self-adjoint consumer is elementary

Let

```text
A_N=-partial_L^2,  Dom(A_N)={f in H^2(R_+):f'(0)=0},
A_D=-partial_L^2,  Dom(A_D)={f in H^2(R_+):f(0)=0}.      (15)
```

Both are nonnegative self-adjoint operators.  The source-normalized functions

```text
c_lambda(L)=cosh(lambda L),
s_lambda(L)=sinh(lambda L)/lambda                       (16)
```

with `s_0(L)=L` satisfy

```text
A_N c_lambda=-lambda^2 c_lambda,   c_lambda(0)=1, c_lambda'(0)=0,
A_D s_lambda=-lambda^2 s_lambda,   s_lambda(0)=0, s_lambda'(0)=1. (17)
```

These are exactly the Neumann and Dirichlet shapes of the prime-tail reflected monodromy
theorem.  They are tempered generalized eigenfunctions of the fixed positive self-adjoint
operator `A_N direct_sum A_D` exactly when `Re lambda=0`; for `Re lambda != 0`, both have an
exponentially growing component.

Thus no new formal differential operator is required.  What Hedenmalm's proposal lacks is a
source theorem placing every Xi conormal nontrivially in the tempered spectral boundary of this
fixed operator.

## What the calculation means

The regular theta transgression `(1)` exists and exactly recovers Hedenmalm's reflected modes.
It has the wrong Hilbert polarity:

```text
hypothetical right off-line zero -> honest L^2 bulk input,
critical-line zero               -> non-L^2 threshold boundary input,
hypothetical left off-line zero  -> reflected exponentially growing input. (18)
```

Ordinary `L^2` completion therefore cannot prove RH.  It regularizes the wrong side of the
divisor and excludes the critical carrier.  This explains, in one calculation, why:

1. ordinary theta-translate quotients collapse by Wiener cyclicity;
2. finite-Rees maps cannot recover the all-orders-flat theta conormal;
3. infinite rank without a singular trace does not help;
4. Hedenmalm's forced resolvent equation survives while a genuine eigenvector does not;
5. the prime-tail chart sees homogeneous monodromy, while the theta chart sees a flat forced
   response.

They are bulk and boundary presentations of one endpoint-trace exact sequence.

## Revised open core

`[OPEN CORE: THETA_TRANSGRESSION_BOUNDARY_COHOMOLOGY_INJECTIVITY]`

Construct, from the ordinary-integer Euler--Poisson--Gamma source before choosing any zero, a
Hausdorff boundary cohomology `H_boundary` and a closed comparison map

```text
prime-tail monodromy
    -> tempered spectral dual of A_N direct_sum A_D
    -> H_boundary
    -> Hedenmalm theta fold,                              (19)
```

such that:

1. regular `L^2` bulk primitives are exact and vanish in `H_boundary`;
2. every Xi multiplicity conormal maps to a nonzero class;
3. source reflection becomes Hilbert adjunction;
4. the comparison commutes with the nonreal resolvents of `(15)`;
5. no divisor point or zero-dependent normalization occurs in the construction.

If `(19)` exists, each nontrivial Xi zero supplies a nonzero tempered generalized eigenmode of
`A_N direct_sum A_D`.  By `(17)`, its parameter must satisfy

```text
-lambda^2 in [0,infinity),
```

and the open critical strip excludes nonzero real `lambda`.  Hence `lambda` is purely imaginary
and `Re rho=1/2`.

This implication is short, but condition 2 is the RH-bearing theorem.  Calling it
“self-adjointness,” “purity,” “same-fibre dagger,” or “positive realization” does not prove it.
The gain here is narrower and concrete: the regular transgression and positive consumer are now
explicit, leaving only the singular boundary-cohomology lift and its source-side injectivity.

## Hostile audit

1. This does **not** construct `(19)` and does not prove RH.
2. Boundedness of `(1)` does not transport Hedenmalm modes to eigenvectors of `(15)`.  For
   `Re rho>1/2`, it transports a resolvent/bulk vector, which is precisely the wrong conclusion.
3. The Neumann/Dirichlet Laplacians are classical.  Novelty, if any, lies only in the exact
   source-chart comparison and the resulting reversal of the previously stated open core.
4. The Fourier division in Theorem 4 proves that the threshold input cannot secretly be replaced
   by an `L^2` input; it does not prove that the threshold class survives a new completion.
5. A completion defined by declaring the Xi conormals nonzero is target-fed.  Nonannihilation
   must follow from ordinary-prime incidence, Poisson summation, and the Gamma endpoint.
6. A space containing exponentially growing functions would destroy the tempered spectral
   argument.  Mere distributional solvability is insufficient.

## Literature audit

Targeted searches against Hedenmalm's paper, Wiener--Hopf/Volterra terminology, theta
convolution, and half-line self-adjoint realizations found no statement of Theorems 1--4 as the
prime-tail/Hedenmalm chart comparison.  Hedenmalm constructs the theta boundary pencil and asks
for a positive self-adjoint form; he does not make the half-line transgression `(1)` or identify
the `L^2` polarity `(18)`.

Classical credit remains classical:

- Young's convolution inequality;
- Wiener multiplier injectivity;
- half-line Neumann/Dirichlet self-adjoint Laplacians;
- limiting-absorption generalized eigenfunctions.

No external novelty is claimed until a broader operator-theory and analytic-number-theory audit
is complete.

## Lean status

The zero-specialized folded equations `(11)`--`(12)`, parity, and first-conormal
nonannihilation are already formalized in
`formal/GaloisForLFunctions/RHTower/XiHedenmalmReflectionFoldedDirac.lean`.

The new half-line convolution, trace-intertwining, and `L^2` wall are paper-level.  They should
be formalized only as the literal Bochner/Lebesgue integral theorem above; an abstract
“transgression” structure would erase the endpoint trace and would be theatre.

## 2026-08-01 essential-boundary refinement

`hedenmalm-theta-flat-borel-holonomy-law.md` now constructs the literal essential chart of the
flat theta tail.  After `y=x+log(1+t)/2`, every Hedenmalm tail factors through the universal
multiplier

```text
M_alpha(t)=(1+t)^(i alpha/2)=exp(i alpha Q),
Q=log(1+t)/2.
```

`Q` is a fixed positive self-adjoint multiplication generator.  Functional reflection sends
`M_alpha` to its inverse, while Hilbert adjunction sends it to `M_(-conjugate alpha)`.  These agree
exactly for real `alpha`.  Hence positive boundary generator and regular transgression are both
explicit; remaining theorem is common-domain nonannihilation of every source conormal for both
reflected multipliers.  Declaring that domain membership would still be RH, so it remains open.

## 2026-08-09 — the convolution norm inequality Theorem 1 needs

Theorem 1 asserts `‖T_-‖, ‖T_+‖ ≤ ‖k‖₁` as operators `L²(ℝ₊) → L²(ℝ)`, which after zero extension
is Young's convolution inequality `L¹ ⋆ L² → L²`.  An exact search shows **no convolution norm
inequality exists in mathlib** (`Mathlib/Analysis/Convolution.lean` and
`Mathlib/Analysis/LConvolution.lean` carry no `eLpNorm_convolution_le` and no Young statement) and
none in this tree; Minkowski's integral inequality is likewise absent.

`formal/GaloisForLFunctions/HTGeometry/YoungConvolutionL2.lean` supplies it by the route that
avoids Minkowski entirely:

- `lintegral_weighted_sq_le` — Cauchy--Schwarz against the weight `K dy` in `ℝ≥0∞`:
  `(∫ K·G)² ≤ (∫K)·(∫ K·G²)`;
- **`lintegral_convolution_sq_le`** — Tonelli on `∫∫ K(y)·F(x−y)²` plus translation invariance of
  Lebesgue measure, giving `∫ (∫ K(y)F(x−y) dy)² dx ≤ (∫K)²·∫F²`.

Everything is stated in `ℝ≥0∞`, so no integrability hypothesis appears anywhere; the `L²` operator
bound of Theorem 1 is the specialization to `K = ‖k‖₊`, `F = ‖f‖₊`.
