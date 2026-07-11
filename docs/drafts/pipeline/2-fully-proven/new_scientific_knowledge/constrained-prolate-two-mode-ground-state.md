# The vanishing-integral prolate ground state selects the CCM two-mode seed

- **ID:** `constrained-prolate-two-mode-ground-state`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`, provisional pending
  independent proof and literature review; `[NOT AN RH PROOF]`
- **Parent sources:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, Sections 7--8;
  Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited signals*
- **Statement:** The exact minimum-leakage unit prolate function in the positive even
  compressed-Fourier sector with vanishing integral converges to the Connes--Consani--Moscovici
  `h_(0,lambda)`--`h_(4,lambda)` seed at rate `O(lambda^(-7))`; its leakage is asymptotic to
  `8/11` of the `h_(4,lambda)` leakage, and its constrained spectral gap is at least a fixed
  positive multiple of that leakage.

## Result in context

Connes--Consani--Moscovici define

```text
k_lambda=E(h_lambda),
```

where `h_lambda` is the unique vanishing-integral combination of the prolate modes of indices zero
and four, `h_(0,lambda),h_(4,lambda)`. They call `k_lambda` an educated guess for the true lowest
Weil eigenvector and leave its comparison with that eigenvector as the main analytic obstacle.

The theorem below does not prove that comparison. It proves a prior statement that was also absent:
the seed `h_lambda` is asymptotically selected by an exact constrained time--frequency variational
problem, rather than by an arbitrary two-mode truncation. It also provides the quantitative surrogate
gap required by any later prolate-to-Weil transfer theorem.

The repository's compact-detector theorem shows why this is the relevant regime. Compact
fixed-aperture strict-margin Weil families cannot detect every remote off-line quartet. The optimizer
here escapes through both permitted channels: its support grows with `lambda`, and its leakage tends
to zero exponentially, so it approaches the prolate radical.

The global radical source space also imposes `f(0)=0`. The finite-aperture theorem
`ccm-restricted-summation-aperture-gauge.md` shows that this additional scalar condition is gauge at
the level of `k_lambda`: it can be imposed by an invisible central bump without changing
`R_lambda E(f)`. Endpoint regularity and the lower Poisson tail remain genuine, separate issues.

## Setup

Let `F` be the unitary additive Fourier transform on `L2(R)` in the convention

```text
Ff(y)=integral_R f(x) exp(2*pi*i*x*y) dx,
```

and let `P_lambda` be multiplication by the indicator of `[-lambda,lambda]`. Work in the real even
subspace of `P_lambda L2(R)`. The compact self-adjoint operator

```text
T_lambda=P_lambda F P_lambda
```

has normalized real prolate eigenfunctions `h_(n,lambda)`. On indices divisible by four,

```text
T_lambda h_(4j,lambda)=chi_(4j)(lambda) h_(4j,lambda),
1>chi_0>chi_4>chi_8>...>0.
```

Put

```text
H_lambda^+=closure span{e_j:j>=0},
e_j=h_(4j,lambda),
B_lambda=I-T_lambda^2,
d_j=1-chi_(4j)(lambda)^2,
ell_j=integral_R e_j(x) dx.
```

Thus `B_lambda e_j=d_j e_j`, with

```text
0<d_0<d_1<d_2<...<1,   d_j -> 1.
```

For a supported unit vector, `<B_lambda f,f>` is exactly the Fourier energy leaking outside
`[-lambda,lambda]`. Evaluation of the compressed Fourier eigenvalue equation at zero gives

```text
ell_j=chi_(4j)(lambda)e_j(0).                            (1)
```

The integral functional is bounded on `P_lambda L2(R)`. Its Riesz vector in `H_lambda^+` has
coordinates `ell=(ell_j)`, and Bessel's inequality gives

```text
sum_(j>=0) ell_j^2 <= ||1_[-lambda,lambda]||_2^2=2*lambda. (2)
```

Let

```text
M_lambda={f in H_lambda^+: integral_R f=0}=ell^perp.
```

The normalized CCM two-mode seed is

```text
g_lambda
 = (ell_1 e_0-ell_0 e_1)/sqrt(ell_0^2+ell_1^2).          (3)
```

It is the unique unit vector up to sign in `span{e_0,e_1} intersect M_lambda`.

## Theorem

`[PROVED HERE]` For all sufficiently large `lambda`, the compression of `B_lambda` to `M_lambda`
has a simple lowest eigenvalue `mu_0(lambda)` with unit eigenvector `v_lambda`, unique up to sign.
Moreover,

```text
min_(sigma in {+1,-1}) ||v_lambda-sigma*g_lambda||_2
  =O(lambda^(-7)),                                      (4)

mu_0(lambda)/d_1(lambda) -> 8/11.                       (5)
```

If `mu_1(lambda)` is the next constrained eigenvalue, then

```text
liminf_(lambda->infinity)
  (mu_1(lambda)-mu_0(lambda))/d_1(lambda) >= 3/11.       (6)
```

In particular, for every `c<3/11`,

```text
mu_1(lambda)-mu_0(lambda) >= c*d_1(lambda)               (7)
```

for all sufficiently large `lambda`.

The exponent `7` in (4) is a safe rate obtained from a global Bessel bound on the infinite tail; no
optimality is claimed.

## Proof

### 1. Fixed-mode prolate scale separation

Fuchs' fixed-index asymptotic, in the normalization used by Connes--Consani--Moscovici, implies that
for each fixed nonnegative integer `n` there is a constant `A_n>0` such that

```text
1-chi_n(lambda)^2
  ~ A_n lambda^(2*n+1) exp(-4*pi*lambda^2).              (8)
```

Some statements of the Fuchs formula use the concentration eigenvalue `chi_n^2`, while CCM quote it
for the positive compressed-Fourier eigenvalue `chi_n`. Passing between them uses
`1-chi_n^2=(1+chi_n)(1-chi_n)` and only changes the positive leading constant. The powers and all
ratios below are unchanged.

Applying (8) at `n=0,4,8` gives

```text
d_0/d_1=O(lambda^(-8)),
d_1/d_2=O(lambda^(-8)),
d_2-d_1 ~ d_2.                                          (9)
```

The prolate-to-Hermite estimate used in CCM gives `e_0(0)->h_0(0)` and `e_1(0)->h_4(0)`. Together
with (1) and `chi_0,chi_4->1`, this yields

```text
ell_0 -> a_0=2^(1/4),
ell_1 -> a_1=sqrt(3)/2^(5/4).                            (10)
```

In particular, `ell_0,ell_1` are bounded above and bounded away from zero for large `lambda`, and

```text
a_0^2/(a_0^2+a_1^2)=8/11.                               (11)
```

### 2. The first constrained eigenvalue is a secular root

Let `C_lambda` be the compression of `B_lambda` to `M_lambda`. Since `B_lambda=I-T_lambda^2` and
`T_lambda^2` is compact, `C_lambda` is the identity on `M_lambda` minus a compact self-adjoint
operator. Its spectrum below `1` is discrete.

The two-dimensional trial vector (3) has Rayleigh quotient

```text
mu_2mode
 = (ell_0^2*d_1+ell_1^2*d_0)/(ell_0^2+ell_1^2),         (12)
```

which lies strictly between `d_0` and `d_1` for large `lambda`. Hence `C_lambda` has an eigenvalue
below `d_1`.

If `v` is a constrained eigenvector with eigenvalue `mu` in `(d_0,d_1)`, then

```text
B_lambda v-mu*v in span{ell}.
```

Because `B_lambda-mu` is invertible, its coordinates are, up to one common nonzero scalar,

```text
v_j=ell_j/(d_j-mu).                                     (13)
```

The constraint `<v,ell>=0` is therefore the secular equation

```text
F(mu):=sum_(j>=0) ell_j^2/(d_j-mu)=0.                   (14)
```

The series and its derivative converge locally uniformly in `(d_0,d_1)`: for `j>=2`, the
denominators are uniformly separated from zero and `(ell_j)` is square summable by (2). The function
`F` is strictly increasing, tends to `-infinity` as `mu` decreases to `d_0`, and tends to `+infinity`
as `mu` increases to `d_1`. It has exactly one root `mu_0` in this interval. Formula (13) makes its
eigenspace one-dimensional. This proves existence and simplicity of the constrained ground state;
codimension-one min--max interlacing also gives `d_0<=mu_0<=d_1`, so no lower constrained
eigenvalue was omitted.

### 3. The infinite tail moves the two-mode root by only `O(lambda^(-7))` relatively

Write

```text
F_2(mu)=ell_0^2/(d_0-mu)+ell_1^2/(d_1-mu),
R(mu)=sum_(j>=2) ell_j^2/(d_j-mu).
```

The unique zero of `F_2` in `(d_0,d_1)` is exactly `mu_2mode` from (12). Since `R(mu)>0`,

```text
mu_0<mu_2mode.                                           (15)
```

For `mu in (d_0,d_1)`, (2) and (9) give

```text
0<R(mu)<=2*lambda/(d_2-d_1).                            (16)
```

On `(d_0,mu_2mode)`, (10) and the fact that both denominators have magnitude at most `d_1` give

```text
F_2'(mu)
 =ell_0^2/(d_0-mu)^2+ell_1^2/(d_1-mu)^2
 >= c_0*d_1^(-2)                                       (17)
```

with a constant `c_0>0`. Since `F_2(mu_0)=-R(mu_0)` and `F_2(mu_2mode)=0`, the mean value theorem,
(16), and (17) yield

```text
0<=mu_2mode-mu_0
 <= C*lambda*d_1^2/(d_2-d_1)
 =O(lambda*d_1^2/d_2).                                  (18)
```

Consequently,

```text
(mu_2mode-mu_0)/d_1
 =O(lambda*d_1/d_2)=O(lambda^(-7)).                     (19)
```

Equations (9), (10), and (12) show

```text
mu_2mode/d_1 -> a_0^2/(a_0^2+a_1^2)=8/11.
```

Combining this with (19) proves (5).

### 4. The constrained ground vector is asymptotically two-mode

Use the unnormalized coordinates (13) at `mu=mu_0`. The squared norm of their tail satisfies

```text
sum_(j>=2) ell_j^2/(d_j-mu_0)^2
 <=2*lambda/(d_2-d_1)^2.                                (20)
```

The squared norm of the first two coordinates is at least `c_1*d_1^(-2)` by (10). Therefore the
tail-to-head norm ratio is

```text
O(sqrt(lambda)*d_1/d_2)=O(lambda^(-15/2)).               (21)
```

At `mu=mu_2mode`, the first two coordinates in (13) are proportional to

```text
(-ell_1,ell_0),
```

which is the negative of the coefficient vector in (3). More explicitly, the ratio of the second
coordinate to the first is

```text
rho(mu)=(ell_1/ell_0)*(d_0-mu)/(d_1-mu).
```

Equations (5), (10), and (11) show that throughout the interval from `mu_0` to `mu_2mode`, both pole
distances are comparable to `d_1`. Hence `|rho'(mu)|=O(d_1^(-1))`; normalization of a two-coordinate
vector with bounded ratio is Lipschitz there. Equation (19) therefore gives

```text
distance(first-two direction at mu_0, first-two direction at mu_2mode)
 =O((mu_2mode-mu_0)/d_1)
 =O(lambda^(-7)).                                       (22)
```

Combining (21) and (22), and choosing the sign of `v_lambda`, proves (4).

### 5. The constrained spectral gap

Codimension-one min--max interlacing gives

```text
d_0<=mu_0<=d_1<=mu_1<=d_2.                              (23)
```

The upper bound `mu_1<=d_2<1` can also be seen by intersecting
`span{e_0,e_1,e_2}` with `M_lambda`, which leaves a two-dimensional trial space. Thus `mu_1` is a
discrete constrained eigenvalue rather than the essential value `1`.

Using `mu_1>=d_1` from (23) and (5),

```text
liminf (mu_1-mu_0)/d_1 >= 1-8/11=3/11,
```

which proves (6) and (7). This completes the proof.

## What is standard and what is claimed

- `[SEARCH]` The unconstrained prolate concentration problem and its diagonalization by prolate
  spheroidal functions.
- `[SEARCH]` Fuchs' fixed-index exponentially small concentration deficits.
- `[SEARCH]` Projection of a Rayleigh quotient to the nullspace of linear constraints, secular
  equations for a rank-one constraint, and codimension-one eigenvalue interlacing.
- `[SEARCH]` CCM's construction of the unique two-mode vanishing-integral seed and their
  prolate-to-Hermite convergence estimate.
- `[PROVED HERE]` The infinite-dimensional tail estimate (18)--(22) specialized to the prolate
  fixed-index hierarchy.
- `[PROVED HERE]` Canonical variational selection of the CCM seed with rate `O(lambda^(-7))`.
- `[PROVED HERE]` The exact limit `mu_0/d_1->8/11` and the asymptotic constrained-gap lower bound
  `3/11`.

## Novelty and significance audit

### Parent-theory gate

The general constrained-Rayleigh mechanism is old. Kennedy and Kabal's 1986 maximum-energy window
paper, for example, reduces prescribed spectral values and nulls to a projected concentration
operator. That parent does not supply the continuous fixed-aperture asymptotic proved here, identify
the `h_0`--`h_4` pair, control the infinite prolate tail, or derive the constants `8/11` and `3/11`.

### Literature gate through July 2026

Targeted searches covered:

1. the CCM papers and their cited prolate sources;
2. Groskin's May 2026 high-precision trigonometric-basis Galerkin study, which explicitly says that
   no prolate-basis implementation has yet been reported and supplies numerical rather than analytic
   convergence evidence;
3. continuous and discrete linearly constrained Slepian concentration;
4. zero-mean, zero-DC, prescribed spectral-null, and moment-constrained prolate windows;
5. constrained Rayleigh quotients, rank-one secular equations, and interlacing; and
6. exact searches for the `h_0`--`h_4` vanishing-integral combination and the constants in (5)--(6).

No equivalent theorem or stronger quantitative result was located. The closest direct parent is the
general constrained-window formulation, while the closest RH parent is CCM itself, which still calls
the two-mode seed an educated guess and does not give it a variational characterization or a gap.
The novelty label therefore passes provisionally and remains subject to independent specialist
review.

### Rediscovery gate

The theorem is not the generic fact that a linearly constrained Rayleigh quotient is a compressed
eigenproblem. Its non-parent content is the uniform asymptotic consequence of three interacting
facts: the zero-integral constraint has nonzero limiting coordinates on modes `0` and `4`, successive
positive-sign fixed-mode leakage scales differ by `lambda^8`, and the complete remaining constraint
vector has only the global mass bound (2). Those facts force the exact full constrained eigenvector,
not a truncated model, into the CCM two-mode direction and determine the rational constant `8/11`.

### Significance gate

Passed provisionally, at a moderate rather than decisive level. The result removes the arbitrariness
of the prolate seed and supplies an explicit surrogate gap. It does not compare the prolate leakage
operator with the Weil operator, does not prove simplicity of the true Weil ground state, and does
not establish convergence of its determinant to `Xi`. It advances one necessary input to the stated
CCM program but leaves the principal analytic bridge open.

## Exact remaining Connes-route core

There are two independent cutoffs: the arithmetic aperture `X=lambda^2` and the Galerkin dimension
`M`. For every finite pair for which the CCM lowest-eigenvalue hypothesis holds, the associated
determinant has real zeros in the spectral variable. In the zeta variable `s=1/2+iz`, its zeros
therefore lie exactly on `Re(s)=1/2`. Consequently the prime-clock energy on those zero fibers is
identically zero. The metric gate in the formalized logarithmic-boundary transfer theorem is
automatic for this family; finite self-adjointness supplies that gate but not the analytic gate.

The terminal CCM obligation is to choose a cofinal diagonal `M=M(X)`, normalize the determinants so
that the limit is nonzero, and prove locally uniform convergence to `Xi`. This is the missing
divisor-carrying statement. It must simultaneously justify the fixed-aperture Galerkin limit and
the growing-aperture limit.

Let `A_lambda` denote the true continuous Weil operator in the CCM normalization and let
`r_lambda=<A_lambda g_lambda,g_lambda>`. One possible producer of the required analytic convergence
is an estimate strong enough to compare the true Weil ground vector with `g_lambda`. A sufficient
Davis--Kahan-type input is a form-residual estimate

```text
||(A_lambda-r_lambda)g_lambda||
  =o(Gap_lambda),                                        (24)
```

where `Gap_lambda` is a rigorously established separation above the lowest Weil eigenvalue. The
prolate theorem proves the corresponding surrogate separation but does not identify
`Gap_lambda` for `A_lambda`.

Because the supports grow and the vectors approach the radical, ordinary fixed-support norm control
is not enough for the final determinant statement. The transfer must retain the weighted or
projective control needed for locally uniform Mellin-transform convergence on every closed substrip
of `|Im z|<1/2`. This is the analytic gate. Once it is proved for a cofinal CCM family whose finite
zeros are real, the metric defect is zero and the formalized boundary-transfer theorem yields RH.
The Davis--Kahan route is only one possible way to produce this convergence; a direct normal-family,
de Branges, or log-derivative argument would also suffice if it carries the full divisor.

## Lean decision

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateOperator.lean` now constructs the concrete
operator layer on the project's actual Fourier `L2` model. It proves that `P_a F P_a` preserves the
even carrier, is compact and self-adjoint, and that its concentration and leakage operators are
positive. The constrained carrier is exactly the intersection of the time-limited range of `P_a`
with the orthogonal complement of the central indicator; Lean proves this is equivalent to being
fixed by `P_a` and having integral zero. The compressed leakage is positive, is identity minus a
compact operator, and has quadratic form
`||f||^2-||P_a F P_a f||^2`. These theorems are unconditional.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateSignedSpectrum.lean` supplies the actual
signed compact spectrum of `P_a F P_a`: signed eigen-equations, orthogonality, physical-support
membership of every nonzero mode, decay of the signed eigenvalues, and the exact squaring relation
to concentration and leakage. The constrained compression also has unconditional greedy
concentration/leakage eigenmodes in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateConstrainedSpectrum.lean`.

The rank-one **secular equation** at the heart of §2 — that a constrained eigenvalue `μ ∈ (d_0, d_1)`
has coordinates `v_j = ℓ_j/(d_j − μ)` and solves `F(μ) = ∑_j ℓ_j²/(d_j − μ) = 0`, with `F` strictly
increasing on any pole-free interval, hence at most one root there — is formalized axiom-clean in
`GaloisForLFunctions.ProlateSecularEquation`: `secular_strictMonoOn` (strict monotonicity of `F` on
`(a,b)` when every pole `d_j ∉ (a,b)` and some `ℓ_{j₀} ≠ 0`) and `secular_root_unique` (the
constrained ground eigenvalue, where it exists, is simple).  This is the exact "Formula (13) makes
its eigenspace one-dimensional; `F` is strictly increasing … exactly one root" step, proved for the
full (arbitrary index set) constraint, not a finite-matrix shadow.  **Existence** of the constrained
ground eigenvalue is also formalized: `secular_exists_root` proves that for consecutive poles
`d a₀ < d b₀` (nothing strictly between, both with `ℓ ≠ 0`) the secular equation has a root in
`(d a₀, d b₀)`, via the pole limits `F(μ) → ∓∞` at the endpoints (`tendsto_const_div_sub_atBot/atTop`)
and the intermediate value theorem.  Together with `secular_root_unique` this gives the card's
"`C_λ` has a simple lowest eigenvalue `μ_0` in `(d_0, d_1)`" — existence and simplicity — without any
Fuchs/Hermite input.  The **two-mode trial value**
(eq. 12) is also formalized exactly: `twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁ = (ℓ₀²d₁+ℓ₁²d₀)/(ℓ₀²+ℓ₁²)`
with `twoModeSecularRoot_mem_Ioo` (it lies strictly in `(d₀,d₁)`, so `C_λ` has an eigenvalue below
`d₁`) and `twoModeSecular_eq_zero` (it is the exact root of the two-mode secular equation
`ℓ₀²/(d₀−μ)+ℓ₁²/(d₁−μ)=0`, i.e. `μ_2mode`).  The headline **constant `8/11`** (eq. 11) is formalized
by `ccm_groundState_weight_eq`: `a₀²/(a₀²+a₁²) = 8/11` for the prolate-to-Hermite limits
`a₀ = 2^{1/4}`, `a₁ = √3·2^{−5/4}` — the value `μ_0(λ)/d_1(λ)` converges to in (5).

The scientifically new asymptotic theorem `(4)`--`(7)` is not yet fully formalized. Its remaining
inputs are the classical identification and simplicity theorem matching the positive signed modes
with the `4j` numbering, Fuchs fixed-index asymptotics with normalization, prolate-to-Hermite
convergence, and the uniform infinite-tail secular estimate (existence of the root and its
`8/11`/`3/11` asymptotics on top of the now-formalized monotonicity/uniqueness).

## Gates

- [x] exact source-defined prolate operator and vanishing-integral constraint
- [x] complete infinite-dimensional paper proof
- [x] normalization audit between `chi_n` and `chi_n^2`
- [x] parent-theory separation from generic constrained Rayleigh quotients
- [x] targeted literature audit through July 2026
- [x] rediscovery attack
- [x] provisional novelty gate
- [x] provisional significance gate
- [ ] independent proof review
- [ ] independent literature review
- [ ] true Weil residual and spectral-gap transfer
- [ ] weighted/projective convergence sufficient for the regularized determinant
