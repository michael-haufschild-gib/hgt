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
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-restricted-summation-aperture-gauge.md`
shows that this additional scalar condition is gauge at
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

`formal/GaloisForLFunctions/RHTower/TwoModeFuchsLimit.lean` goes one step further.  Under the exact
Fuchs-rate model it proves `twoModeSecularRoot_fuchs_ratio_tendsto` for arbitrary increasing fixed
indices, then specializes it to the CCM pair as `ccm_twoMode_ground_leakage_ratio` with limit
`8/11`.  The theorem `ccm_twoMode_ground_gap_ratio` proves the complementary two-mode gap ratio
`3/11`.  Its quantified corollary `ccm_twoMode_ground_gap_eventually_ge` proves the paper's eventual
inequality form: every `c<3/11` is, for all sufficiently large apertures, a lower bound for the
two-mode gap after multiplication by the dominant Fuchs leakage.  These are genuine limit theorems,
not just arithmetic identities for the limiting weights.

The **uniform infinite-tail secular estimate is now formalized**, for the full infinite index
set, in `formal/GaloisForLFunctions/RHTower/ConstrainedProlateInfiniteSecular.lean`.  The exact
secular function `F(μ) = Σ_{j≥0} ℓ_j²/(d_j − μ)` (genuinely infinite: head plus `tsum` tail) is
proved summable, continuous, and strictly increasing on `(d_0, d_1)`; `infiniteSecular_exists_root`
and `infiniteSecular_root_unique` give the exact constrained ground root `μ_0` (existence by IVT
below the two-mode value, uniqueness by strict monotonicity — the card's §2 for the true infinite
problem, not a finite shadow); `infiniteSecularRoot_twoMode_gap` is exactly the card's tail
estimate `(18)` with the explicit constant `μ_2mode − μ_0 ≤ T·d_1²/(ℓ_0²(d_2 − d_1))`, `T = Σ_{j≥2}ℓ_j²`;
`infiniteSecular_other_root_ge` proves every competing secular zero is ≥ `d_1` (the interlacing
`(23)` at secular level).  The family theorem `infiniteSecularRoot_ratio_tendsto` then proves
`μ_0(λ)/d_1(λ) → a_0²/(a_0²+a_1²)` from the Bessel bound `(2)`, the scale separations, and the
coordinate limits `(10)` — i.e. the card's §3 in full — and its CCM instances
`ccm_infiniteSecularRoot_ratio_tendsto` / `_gap_ratio_tendsto` / `_spectralGap_eventually` give
`8/11`, `3/11`, and the quantified gap `(7)` for the exact optimizer.
`ConstrainedProlateFuchsModelTransfer.lean` discharges the entire leakage side for the concrete
Fuchs family `d_j = A_j λ^{8j+1}e^{−4πλ²}` (`fuchsRate_radial_struct`,
`fuchsRate_radial_tail_ratio_tendsto_zero`, `ccm_fuchsModel_infiniteSecularRoot_*`), assuming only
`A_j > 0` and the tempered growth `A_2 ≤ C^j A_{j+2}`.  All of this is axiom-clean.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlatePointwiseRepresentative.lean` now supplies
the missing source-side regularity interface for the **actual signed modes**, not a model family.
Every fixed signed value is eventually nonzero; its greedy mode then has norm exactly one and has a
canonical even compactly supported pointwise source.  The source is `C^∞` on the open aperture, its
Fourier representative is globally `C^∞`, and every iterated derivative is the exact Fourier
transform of the corresponding compact moment.  Lean also proves the literal normalization
`∫ ‖q_n‖² = 1` and exterior-energy identity
`∫_{(-∞,-a]∪(a,∞)} ‖Fq_n‖² = 1 - σ_n(a)²`.  These theorems remove all a.e., smoothness, and
normalization ambiguity before the remaining ODE/mode-identification argument.  They are
unconditional and axiom-clean.

The exact secular/Fuchs-model statements `(4)`--`(7)`, including the quantitative eigenvector rate,
are now formalized below.  What remains for the *true prolate operator* is the classical
identification layer: positive signed modes with the `4j` numbering, Fuchs fixed-index asymptotics
for the actual `χ_n(λ)`, and prolate-to-Hermite convergence `ℓ_j → a_j`.  The concrete Bessel bound
`(2)` is already discharged.

The sign-choice/metric form of `(4)` is now formalized.  The general geometry lives in
`formal/GaloisForLFunctions/HTGeometry/SignChoiceNormalizedDistance.lean`: for unit vectors
`min(‖u−w‖², ‖u+w‖²) = 2 − 2|⟪u,w⟫|`, so a vanishing angle *is* a vanishing sign-optimized
distance, with the explicit rate `‖u − σw‖² ≤ 2ε` for an angle deficit `ε`.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateHeadDistance.lean` instantiates this in the
head plane.  Taking the seed direction to be the *explicit* orthogonal vector `(−ℓ₁, ℓ₀)` reduces
the whole geometric step to the Lagrange identity
`(x₀ℓ₀+x₁ℓ₁)² + (x₁ℓ₀−x₀ℓ₁)² = (x₀²+x₁²)(ℓ₀²+ℓ₁²)`, so no span or dimension reasoning is needed.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateFullDistance.lean` assembles head and tail
in `lp 2`.  Since the seed is supported on the first two coordinates it pairs only with the head,
giving the factorization
`⟪V,G⟫²/(‖V‖²‖G‖²) = [⟪H,G⟫²/(‖H‖²‖G‖²)]·[‖H‖²/(‖H‖²+T)]`;
the first bracket tends to one by the head-defect collapse, the second by the tail-fraction
collapse together with `‖H‖² ≥ v₀²`.  All of this is axiom-clean.

The quantitative statement `(4)` is now formalized in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateFullDistanceRate.lean`.
`secular_defect_tail_bounds` proves simultaneously that the normalized head defect is at most
`(16/a₀⁴)(λd₁/(d₂-d₁))²` and the squared tail/head fraction is at most
`(4/a₀²)(λd₁/(d₂-d₁))²`.  `full_normalized_alignment_ge` transfers these literal infinite-vector
bounds to full `lp 2` alignment, and `min_norm_sub_normalize_le_of_inner_sq` converts the squared
alignment loss to the unsquared sign-optimized norm distance.  Finally
`fuchsRate_step4_tail_ratio_eventually_le` supplies the pointwise bound
`|λd₁/(d₂-d₁)| ≤ 2(A₁/A₂)λ⁻⁷`.  The capstone
`ccm_normalized_ground_distance_isBigO` therefore proves exactly
`min_σ ‖v̂_λ-σĝ_λ‖ = O(λ⁻⁷)` for the literal secular vector and same-aperture two-mode seed.
No quantitative prolate-to-Hermite convergence rate is used: the coordinate limits only provide
eventual nonvanishing and a fixed head floor.  Axiom audit: only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] exact source-defined prolate operator and vanishing-integral constraint
- [x] complete infinite-dimensional paper proof
- [x] normalization audit between `chi_n` and `chi_n^2`
- [x] parent-theory separation from generic constrained Rayleigh quotients
- [x] targeted literature audit through July 2026
- [x] rediscovery attack
- [x] provisional novelty gate
- [x] provisional significance gate
- [x] two-mode Fuchs-rate `8/11` ground and `3/11` gap limits formalized in Lean
- [x] eventual `c<3/11` two-mode gap lower bound formalized in Lean
- [x] exact infinite-dimensional secular root: existence, uniqueness, tail estimate `(18)`,
  competing-root interlacing, formalized in Lean (`ConstrainedProlateInfiniteSecular`)
- [x] exact-optimizer `8/11`, `3/11`, and quantified `c<3/11` gap under Bessel + coordinate-limit
  hypotheses formalized in Lean; leakage side discharged for the concrete Fuchs family
- [x] true-operator Bessel bound `(2)` formalized in Lean unconditionally:
  `Σ_n ‖⟨1_[-λ,λ], e_n⟩‖² ≤ 2λ` for the actual signed prolate modes, with the integral pairing
  identity and the injective-subfamily form (`ConstrainedProlateBesselBound`)
- [x] eigenvector convergence `(4)` in projective form: the exact eigenvector's tail fraction
  `Σ_{j≥2}v_j²/v_0² → 0` (`ConstrainedProlateSecularVector`) and its normalized head defect
  against the constraint direction `(ℓ_0,ℓ_1)` → 0 at rate `(λd_1/(d_2−d_1))²`
  (`ConstrainedProlateEigenvectorAngle`: `ℓ_0v_0+ℓ_1v_1 = −tail` exactly, `(22)`'s content) —
  together: the exact constrained ground direction converges to the two-mode seed direction
- [x] the normalized ℓ²-distance/sign-choice cosmetic form of `(4)` in Lean, for the CCM Fuchs
  family under exactly the Bessel + coordinate-limit hypotheses used by the other Fuchs-model
  gates above: `ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed`
  (`ConstrainedProlateFullDistanceCCM`) gives `min_σ ‖v̂_λ − σ ĝ_λ‖² → 0` for the full normalized
  `ℓ²` eigenvector against the normalized two-mode seed.  BOTH VECTORS ARE CONSTRUCTED, not
  assumed (`secularLp` via `memℓp_secularVector`, `twoModeSeedLp` via finite support), and the
  structural, tail-ratio, nonvanishing, membership and summability hypotheses are all DISCHARGED
  from the family data `A`.  Only `hsum`/`hbessel` and the coordinate limits `hl0`/`hl1` remain,
  the latter being the open prolate-to-Hermite gate below.  Axiom-clean
- [x] quantitative eigenvector rate `(4)` formalized without strengthening the coordinate inputs:
  `ccm_normalized_ground_distance_isBigO` proves the literal unsquared normalized distance is
  `O(lambda^(-7))`; `ccm_normalized_ground_distance_eventually_le` records an explicit constant
- [ ] remaining true-operator inputs in Lean: mode identification, Fuchs asymptotics,
  prolate-to-Hermite limits.  **Evaluation identity `(1)` is now formalized**, axiom-clean, in
  `formal/GaloisForLFunctions/RHTower/ConstrainedProlateEvaluationIdentity.lean`:
  `timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero` proves `∫ e = χ · e(0)` for the
  canonical compact representative of any nonzero time-band eigenmode at positive aperture, via the
  interior Fourier eigen-equation and `𝓕 g 0 = ∫ g`.  The same module proves the exact two-mode
  centre cancellation
  `S(0) = (χ₁ − χ₀) · e₀(0) · e₁(0)`
  (`timeBandTwoModeConstrainedSource_zero_eq`), which is the algebraic mechanism behind
  `g_λ(0) = O(d_1)` in `constrained-prolate-exterior-weil-leading-law.md` `(2)` — the centre value
  is governed by the **eigenvalue gap**, not by the eigenvalues themselves, and this is proved with
  no asymptotics at all.
- [ ] independent proof review
- [ ] independent literature review
- [ ] true Weil residual and spectral-gap transfer
- [ ] weighted/projective convergence sufficient for the regularized determinant

## Lean progress — the oscillator-ladder pin, and what the prolate-to-Hermite gate now needs

The open gate on this card is the pair of true-operator ℓ-side inputs: the prolate-to-Hermite
coordinate limits and the Fuchs identification.  Their common foundation is now formal, and the
last step turned out to be an identity rather than an asymptotic argument.

What the corpus already owned (no new work): the whole commuting-operator layer —
`HTGeometry/SturmSelfAdjoint.lean`, `HTGeometry/ProlateKernelSymmetry.lean`,
`RHTower/ProlateCommutationKernel.lean` (`prolateAction_bandEigen_eq_smul`: an eigenfunction of the
finite Fourier transform solves the prolate ODE), `RHTower/SlepianBandCommutation.lean`,
`RHTower/FuchsProlateScale.lean` (the exact scaling identity `prolateSLAction_sqrtScale`),
`RHTower/HermiteOscillatorEigen.lean` (`hermiteSLAction_hermiteFun`: eigenvalue `−(2n+1)`), and
`RHTower/ProlateHermiteRescale.lean`, whose
`exists_even_prolateHermiteRescale_of_signedMode` gives every live signed mode a smooth even global
profile whose Hermite rescaling satisfies, **with no convergence premise**,

```text
hermiteSLAction u + (c·s)·u = (ξ² u″ + 2ξ u′)/c ,      c = 2πλ² .
```

New (wired, axiom-clean):

```text
HTGeometry/WholeLineWronskianSymmetry.lean
    integral_deriv_eq_zero_of_tendsto_zero   a derivative whose primitive tends to 0 at ±∞
                                             integrates to 0 over the line
    hasDerivAt_wronskian                     (u′v − uv′)′ = u″v − uv″
    integral_secondDeriv_pairing_eq_zero
    integral_secondDeriv_mul_comm            ∫ u″v = ∫ u v″ for a vanishing Wronskian

RHTower/ProlateOscillatorLadderPin.lean
    hasDerivAt_hermiteFun, hasDerivAt_deriv_hermiteFun
    hermitePairing_pin (n) :
        hermiteSLAction u + μ·u = D  ⟹  (μ − (2n+1))·⟨u, φₙ⟩ = ⟨D, φₙ⟩
    abs_sub_oscillatorLadder_eq (n) :
        |μ − (2n+1)| = |⟨D, φₙ⟩| / |⟨u, φₙ⟩|
```

The `ξ²` potential cancels identically — it appears with the same sign on both sides of the
integration by parts — so no spectral theorem, no operator domain and no quasimode inequality is
used.  Applied to the prolate identity above,

```text
|c·s(c) − (2n+1)| = |⟨ξ²u″ + 2ξu′, φₙ⟩| / (c · |⟨u, φₙ⟩|) .
```

**Consequently the whole remaining analytic content of this card's prolate-to-Hermite gate is one a
priori bound**: that the defect pairing `⟨ξ²u″ + 2ξu′, φₙ⟩` stays bounded relative to `⟨u, φₙ⟩` as
the bandwidth grows.  That is a statement about a single rescaled profile against a single Gaussian
weight; it needs no expansion and no uniformity in the index.  With it, the eigenvalue is pinned to
the oscillator ladder at rate `1/c`, the same pairing pins the eigenvector, and
`ℓ_j = χ_{4j}·e_j(0)` with `χ → 1` delivers the coordinate limits `ℓ_j → |ĥ_{4j}(0)|` whose targets
`2^{1/4}` and `√3·2^{−5/4}` are already formal in `HermiteOriginConstraintTargets.lean`.

## Lean progress — the defect pairing needs no derivative bound at all

The note above reduced this card's prolate-to-Hermite gate to a single a priori bound on the defect
pairing `⟨ξ²u″ + 2ξu′, φₙ⟩`.  That bound is no longer needed in that form: the pairing transfers
entirely onto the Hermite side.

`GaloisForLFunctions/HTGeometry/WholeLineWronskianSymmetry.lean` (extended, wired):

```text
integral_deriv_mul_eq_neg     ∫ u′v = −∫ u v′ when u v → 0 at both ends
```

`GaloisForLFunctions/RHTower/ProlateDefectTransfer.lean` (wired):

```text
hermiteSqWeight n x           = x² φₙ(x)          (with its two derivatives)
hermiteLinWeight n x          = 2x φₙ(x)          (with its derivative)
integral_prolateDefect_transfer :
    ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²φₙ″ + 2ξφₙ′⟩
integral_prolateDefect_transfer_explicit :
    ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩
prolateLadder_pin_hermiteSide :
    (μ − (2n+1))·⟨u, φₙ⟩ = ⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩ / c
```

Two integrations by parts — one of second order against the weight `ξ²φₙ`, one of first order
against `2ξφₙ` — move both derivatives of the profile onto the Hermite factor, and
`φₙ″ = (ξ² − 2n − 1)φₙ` makes the surviving weight completely explicit.  The `4ξφₙ′` produced by the
second-order transfer and the `−2ξφₙ′` produced by the first-order one combine to `2ξφₙ′`, and the
two `±2φₙ` cancel.

**Consequence for this card.**  The distance from the rescaled eigenvalue `c·s(c)` to the `n`-th rung
of the oscillator ladder is now, exactly,

```text
|c·s(c) − (2n+1)| = |⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩| / (c · |⟨u, φₙ⟩|) ,
```

in which **no derivative of the prolate profile appears**.  What remains is a comparison of two
pairings of the profile against fixed Gaussian-decaying weights — the numerator against
`ξ²(ξ²−2n−1)φₙ + 2ξφₙ′` and the denominator against `φₙ` — plus the decay hypotheses that make the
two integrations by parts legitimate.  That is a non-degeneracy statement about one function against
one fixed weight, not an asymptotic expansion.

## Lean progress — the eigenvalue half of the prolate-to-Hermite gate closes

The residue recorded in the previous section was a lower bound on `|⟨u, φₙ⟩|`, uniform in the
bandwidth.  It is not an obstruction: the Hermite rescaling *flattens* the profile, so the pairing
has an explicit limit.

`GaloisForLFunctions/RHTower/ProlateCentreValuePairing.lean` (wired):

```text
tendsto_div_sqrt_atTop            ξ/√c → 0
tendsto_integral_rescaled_mul     ∫ Φ(ξ/√c) W(ξ) dξ ⟶ Φ(0) · ∫ W        (W integrable)
tendsto_zero_of_ladderPin
    d(c)·⟨u_c, V⟩ = ⟨u_c, W⟩/c ,  Φ(0)·∫V ≠ 0   ⟹   d(c) → 0
```

The pairing limit is dominated convergence with the two cheapest possible hypotheses on `Φ`:
continuity at the origin and boundedness.  Both are free — the profile is continuous by
construction, and `abs_le_of_bandTransform_eigen` makes it decay, hence bounded.

Applied to the ladder pin with `V = φₙ` and `W = ξ²(ξ²−2n−1)φₙ + 2ξφₙ′`, the denominator pairing
tends to `Φ(0)·∫φₙ` and the numerator pairing stays bounded, so

```text
c·s(c) − (2n+1) ⟶ 0 .
```

The nonvanishing hypothesis `Φ(0)·∫φₙ ≠ 0` is not an extra asymptotic input.  `∫φₙ ≠ 0` holds for
the even Hermite indices this card uses.  And `Φ(0) ≠ 0` follows from the data already in hand,
by ODE uniqueness rather than by assumption: the profile is **even**, so `Φ′(0) = 0`; the prolate
equation `(1 − x²)Φ″ − 2xΦ′ − c²x²Φ = χΦ` has leading coefficient `1` at `x = 0`, so the origin is
an ordinary point; hence `Φ(0) = 0` together with `Φ′(0) = 0` would force `Φ ≡ 0`, contradicting
`Φ ≠ 0`.

(An earlier draft of this note claimed `Φ(0) ≠ 0` was supplied by
`exists_even_prolateHermiteRescale_of_signedMode`'s hypothesis `evenProlateSignedValue a n ≠ 0`.
That is not so: `evenProlateSignedValue` is the signed *eigenvalue* `sgVal (evenTimeBandFourier a) n`,
not the centre value.  The uniqueness argument above is what supplies it.)

**Status of this card's gate.**  The *eigenvalue* half of the prolate-to-Hermite limit —
`c·s(c) → 2n+1`, equivalently the fixed-index prolate eigenvalue asymptotic at leading order — is
now a Lean theorem given the instantiation.  What the card still needs beyond it is the
*eigenvector* half, `ℓ_j(λ) → |ĥ_{4j}(0)|`, and the Fuchs identification of the leakage rates.

## Correction — the eigenvalue half is not closed by the centre-value pairing

An earlier note on this card recorded that the *eigenvalue* half `c·s(c) → 2n+1` "is now a Lean
theorem given the instantiation", via `RHTower/ProlateCentreValuePairing.lean`
(`tendsto_zero_of_ladderPin`).  That is wrong, and the reason is structural rather than technical.

`tendsto_integral_rescaled_mul` and `tendsto_zero_of_ladderPin` take **one fixed** profile `Φ` and
let the bandwidth act only through the rescaling `Φ(ξ/√c)`; the flattening that produces
`Φ(0)·∫V` in the limit is dominated convergence for that single function.  The prolate family does
not have that shape: its profile `Φ_c` is itself the `c`-dependent eigenfunction, so there is no
fixed `Φ` to rescale.  The two theorems remain correct and reusable, but they do not instantiate
here.

### What the eigenvalue half actually needs

With the window machinery now in place the missing input is one classical rigidity statement:

```text
if v ∈ L²(ℝ) is even and solves  v″ = (ξ² − μ) v  on all of ℝ,  then μ = 2n+1 for some even n,
and v is a multiple of the corresponding Hermite function.
```

Given it, both halves follow from the same argument.  Normalize `Ψ_c = u_c/u_c(0)` (legitimate:
`Φ(0) ≠ 0` is `SlepianKernelScaledFubini.value_zero_ne_of_even_joint_prolate_band_eigen`).  The
separation constants `μ_c` are bounded, so along any subsequence `μ_c → μ*`, and
`tendsto_prolateProfile_window` gives `Ψ_c → Ψ*` locally uniformly with `Ψ*″ = (ξ² − μ*)Ψ*`,
`Ψ*(0) = 1`, `Ψ*′(0) = 0`.  The normalized second-moment bound
`∫ξ²Ψ_c² ≤ μ_c ∫Ψ_c²` (now formal as `integral_rescaled_secondMoment_le`) makes the family tight, so
`∫_{-K}^{K}Ψ_c²` is bounded below a constant multiple of `∫Ψ_c²` uniformly, `Ψ* ∈ L²`, and the
rigidity statement forces `μ* = 2n+1` and `Ψ* = φ_n/φ_n(0)`.  Every subsequential limit is the same,
so the full limits hold — the eigenvalue half — and the coordinate limit then follows in the
scale-free form recorded above.

The corpus owns the oscillator ladder on Schwartz space
(`HTGeometry/SchwartzOscillatorAlgebra.lean`, `HTGeometry/HermiteOrthogonality.lean` with
`creationCLM`, `annihilationCLM` and the commutator `BA − AB = 4π`,
`HTGeometry/HermiteNumberOperator.lean`), but not the passage from *an `L²` solution of the ODE* to
that ladder, which is where the rigidity statement has to be built: `A = d/dξ + ξ` satisfies
`A†A = −d²/dξ² + ξ² − 1`, so `‖Av‖² = (μ−1)‖v‖²` forces `μ ≥ 1`, `Av` solves the same equation at
`μ−2`, and iterating must terminate, with `Av = 0` solved only by `Ce^{−ξ²/2}`.

## Lean progress — the card's named classical rigidity input is now a theorem

The statement this card records as "one classical rigidity statement" still missing —

```text
if v ∈ L²(ℝ) is even and solves v″ = (ξ²−μ)v on all of ℝ, then μ = 2n+1 for some even n,
and v is a multiple of the corresponding Hermite function
```

— is proved, unconditionally and axiom-clean, as

```text
RHTower/OscillatorEvenRigidity.even_integrable_solution_rung
```

Its supporting pieces, in the same module:

```text
aeval_hermite_neg_of_odd, odd_hermiteFun    the Hermite function of odd index is odd
integrable_hermiteFun_sq                    the Hermite function is square integrable
hermiteFun_nontrivial                       its value and derivative never vanish together
```

The proof runs through the chain built for this card:

- `OscillatorSpectralRigidity.exists_rung_of_integrable` puts `μ` on the ladder, `μ = 2n+1`;
- an even nontrivial solution cannot vanish at the origin, since evenness would kill its derivative
  there too;
- `OscillatorSolutionSpaceRank.eq_smul_of_integrable` — the square-integrable solution space at a
  rung is one dimensional, proved from the vanishing of the cross-Wronskian — makes `hermiteFun n`
  a multiple of `v`;
- if `n` were odd, `hermiteFun n` would be odd while `v` is even, forcing `hermiteFun n ≡ 0`, which
  `exists_hermiteFun_ne_zero` forbids.  So `n` is even.

The one-dimensionality step is where the real work was: `integrable_kinetic_add_moment` makes `v′`
and `ξv` square integrable (via the windowed virial identity, whose boundary term carries a
favourable sign), so the cross-Wronskian is integrable; being constant on a line of infinite
measure, it vanishes.

With this in hand the card's own recipe applies verbatim: normalize `Ψ_c = u_c/u_c(0)`, use
boundedness of the separation constants to take a limit, `tendsto_prolateProfile_oscProfile` for the
locally uniform convergence, `integral_rescaled_secondMoment_le` with
`integrable_sq_of_bounded_window_limits` for square integrability of the limit, and the rigidity
above to force `μ* = 2n+1` with `n` even and `Ψ* = φ_n/φ_n(0)`.  Every subsequential limit is the
same, so the full limit holds.

## Lean progress — the eigenvalue half, assembled for one family

`RHTower/ProlateWindowMassLimit.lean` (wired, axiom-clean):

```text
exists_evenRung_of_prolate_family
    for a family of normalized rescaled prolate profiles with
      • the rescaled normal form and the initial phase vector u(0)=1, u′(0)=0 on every window,
      • a uniform a priori phase bound B,
      • a uniform window-mass bound N,
      • separation constants tending to m and bandwidth tending to infinity,
    the limit satisfies  m = 2n+1  with  n  even.
```

This is the card's **eigenvalue half**, `c·s(c) → 2n+1`, assembled end to end for a single family.
Its proof is three lines because every step was built separately: `tendsto_prolateWindowMass` gives
the window-mass convergence, `integrable_sq_of_bounded_window_limits` turns the uniform bound into
square integrability of the limit profile, and `even_rung_of_integrable_oscProfile` — the rigidity
statement this card named as its missing classical input — puts the limit on the even ladder.

Every hypothesis is one the prolate family satisfies, and each has its own theorem in the tree:
`normalizedProlate_window_package` for the normal form and normalization,
`normalizedProlate_phase_le` for `B`, `normalizedProlate_total_mass_le` for `N`, and
`even_normalizedProlateProfile` for evenness.

The remaining `(α)` statement — that the `j`-th separation constant tends to `4j+1` — now follows by
applying this theorem to each of the `j+1` modes supplied by
`eventually_rank_highProlateSpan_even_ge`, separating their limits with
`false_of_orthogonal_same_limit` (whose orthogonality hypothesis is
`integral_normalizedProlate_mul_eq_zero` applied to
`integral_mul_eq_zero_of_not_proportional`), and closing with `not_injective_evenRung_below`.

## Lean progress — `(α)`'s lower half, fully assembled

`RHTower/ProlateWindowMassLimit.lean` (wired, axiom-clean):

```text
false_of_orthogonal_prolateFamily_below
    there is no family of j+1 pairwise orthogonal prolate mode families whose limiting
    separation constants all lie below 4j+1
```

Distinctness of the limits is now *derived* from the orthogonality rather than assumed, so the only
hypotheses left are ones the prolate modes satisfy:

```text
the rescaled normal form and normalization u(0)=1, u′(0)=0 on every window
                                  normalizedProlate_window_package
a uniform a priori phase bound B   normalizedProlate_phase_le
a uniform window-mass bound N      normalizedProlate_total_mass_le
evenness                           even_normalizedProlateProfile
pairwise O(K⁻²) window pairings    integral_mul_eq_zero_of_not_proportional
                                     → integral_normalizedProlate_mul_eq_zero
                                     → abs_window_pairing_sub_le_of_secondMoment
separation constants converging    exists_ultrafilter_tendsto_of_eventually_bounded
bandwidth escaping                 the family is indexed by bandwidth
```

Together with the upper half `eventually_rank_highProlateSpan_even_ge`, which supplies `j+1`
linearly independent — hence, by simplicity, pairwise orthogonal — even joint modes with separation
below `4j+1+ε`, this is `(α)`: the `j`-th even separation constant tends to `4j+1`.

Every theorem in the chain is unconditional and axiom-clean.  What the card still needs is `(β)`,
the Fuchs asymptotics identifying the true leakages `d_n(λ)` with the Fuchs family
`A_n λ^{2n+1}e^{−4πλ²}`; that is external and untouched.

## The polynomial factor of `(β)` is the logarithmic correction to the WKB action

A corpus audit locates `(β)`'s obstruction precisely, and removes the first half of it.

### Where the corpus already stands

The reduction of the leakage to an exterior/interior mass ratio is **already formal**, and was not
recorded on this card: `ConstrainedProlatePointwiseRepresentative`'s
`evenTimeLimitedFourierRepresentative_exterior_energy` gives, for every time-limited `f`,

```text
∫_{y ≤ −a} |q|² + ∫_{y > a} |q|²  =  ‖f‖² − ‖T_a f‖² ,       q = the Fourier representative,
```

and `evenProlateSignedFourierRepresentative_exterior_energy_eq_leakage` specializes it to a live
signed mode: the leakage `1 − σ_n(a)²` **is** the exterior energy of the mode's Fourier
representative.  So `(β)` was already an ODE statement, not an operator statement.  Downstream,
`ProlateTurningLayer` turns exact mass balance into a leakage bound:

```text
leakage_lower_of_radial_mass_bounds :
  outside = inside · leakage / value²,  outside ≥ 1/(32c²),  inside ≤ 4e(c/√s)e^{2c(1−s)}
    ⟹  leakage ≥ (√s/(256 e c³))·e^{−2c(1−s)} .
```

### Why that bound cannot reach Fuchs, and what the missing factor is

Both the interior bound and the endpoint bound above use the crude WKB estimate
`∫_{√s}^{b} √((y²−s)/(1−y²)) dy ≤ 1 − s` (`integral_prolateWKB_le_aperture`,
`exp_neg_aperture_le_endpoint`).  At a fixed mode `s ≍ (2n+1)/c`, so `e^{−2c(1−s)}` is a *constant*
times `e^{−2c}`, whereas the Fuchs leakage is `c^{n+1/2} e^{−2c}`.  The whole polynomial factor is
missing, and it is missing for a definite reason: the WKB action

```text
A(s) = ∫_{√s}^{1} √((y²−s)/(1−y²)) dy = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ
```

is not `1 − O(s)` but `1 + (s/4)·log s + O(s)`, and it is the *logarithmic* term that produces the
power of `c`:

```text
c·A(s) = c + (cs/4)·log s + O(cs) = c − ((cs)/4)·log c + O(1)      when c·s is bounded,
```

so `e^{−2cA(s)} = c^{(cs)/2} e^{−2c}·Θ(1)`, and with `c s = 2n+1` that is exactly `c^{n+1/2}e^{−2c}`.

### The sharp action, proved

`formal/GaloisForLFunctions/RHTower/ProlateWKBSharpAction.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
prolateAngleAction s = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ

prolateAngleAction_sub_bounds :
   0 ≤ 1 + (s/4)·log s − A(s) ≤ 3 s               for 0 < s ≤ 1
```

Both bounds are explicit and one-signed.  The proof:

* the substitution `y = sin θ` removes the endpoint singularity, so every integral in sight is of a
  continuous function on a compact interval;
* `sin θ − √(sin²θ − s) = s/(2 sin θ) + ρ`, `0 ≤ ρ ≤ s²/(2 sin³θ)` — proved as
  `sub_sqrt_sq_sub_bounds`, the two inequalities being `(u−w)² ≥ 0` and
  `s u² + s² − 2u³(u−w) = w(2u+w)(u−w)²`;
* the main term integrates **exactly**: `log tan(θ/2)` differentiates to `1/sin θ`
  (`hasDerivAt_log_tan_half`) and `tan(t/2) = √s/(1+√(1−s))` at the turning angle
  (`tan_half_arcsin_sqrt`), so
  `∫_t^{π/2} dθ/sin θ = −(log s)/2 + log(1+√(1−s))` (`integral_one_div_sin_eq`);
* the correction is `O(s)` by Jordan's inequality `sin θ ≥ 2θ/π` together with
  `arcsin √s ≥ √s`, giving `∫_t^{π/2} dθ/sin³θ ≤ π³/(16 s)` (`integral_one_div_sin_cube_le`);
* the three leftover terms `1−√(1−s)`, `(s/2)log(1+√(1−s))` and the correction are each nonnegative
  and each at most `s`, whence the one-sided form.

Getting the *sharp* constant of the `s·log s` term is the whole point: replacing the exact cosecant
antiderivative by the comparison `1/sin θ ≍ 1/θ` would leave a factor-`π/2` uncertainty in that
coefficient, which is a factor `c^{±(2n+1)/4}` in the leakage — enough to destroy the ladder.

### Transport to the band variable, and the improved endpoint bound

Same module:

```text
prolateWKBProfile s y = √((y²−s)/(1−y²))
prolateWKB_eq_mul_profile :   prolateWKB c (−s c²) y = c · prolateWKBProfile s y     (c ≥ 0)
integral_prolateWKBProfile_eq :
   ∫_{√s}^{b} prolateWKBProfile s = ∫_{arcsin √s}^{arcsin b} √(sin²θ − s)            (b < 1)
integral_prolateWKB_le_angleAction :
   ∫_{√s}^{b} prolateWKB c (−s c²) ≤ c · A(s)
exp_neg_angleAction_le_endpoint :
   Φ(√s)·exp(−c·A(s)) ≤ Φ(b)
exp_neg_sharp_le_endpoint :
   Φ(√s)·exp(−(c + (cs/4)·log s)) ≤ Φ(b)
```

The last two are the sharp replacements for the corpus's `exp_neg_aperture_le_endpoint`, whose
conclusion is only `Φ(√s)·e^{−c} ≤ Φ(b)`.  The gain is the factor `s^{−cs/4}`; squared, and with
`c s = 2n+1`, that is exactly the Fuchs power `c^{n+1/2}`.  The change of variables is done on
`[√s, b]` with `b < 1`, i.e. strictly inside the band where the integrand is continuous, which is
also the form in which the corpus's Riccati comparison consumes it; the endpoint limit `b → 1` is
`ProlateForbiddenEndpoint`'s business and is untouched.

### What `(β)` still needs

With the sharp action in hand, three items remain, and all three are ODE estimates on the same
solution:

1. **The endpoint upper bound.**  The corpus owns the Riccati *sub*solution direction
   (`prolateWKB_subsolution`, `prolateLogDeriv_le_prolateWKB`), which gives `Φ(1) ≥ …`.  The reverse
   needs a Riccati *super*solution — the Liouville–Green profile `√q + q′/(4q) − b/2` — so that
   `Φ(1) ≤ Φ(√s)·poly·e^{−c A(s)}`.
2. **The interior normalization from below.**  `integral_sq_le_turning_amplitude_envelope` bounds
   `∫_{−1}^1 Φ²` above by `4e(c/√s)Φ(√s)²`; the matching lower bound `∫_{−1}^1 Φ² ≥ κ (c/√s)^{-1}…`
   — really `∫_{−1}^1 Φ² ≍ Φ_max² c^{−1/2}` — is what fixes the remaining half-power.
3. **The exterior mass upper bound.**  Only `outside ≥ 1/(32c²)` is proved; the companion
   `outside ≤ C Φ(1)²/c` comes from the Bessel-type behaviour at the regular singular point, for
   which `ProlateTwoBranch` and the Dunster layer already supply the amplitude.

Items 1–3 together with `prolateAngleAction_sub_bounds` give the two-sided envelope, and the
`FuchsEnvelope` consumer tolerates a slack of `±3/2` in the exponent, so none of the three has to be
sharp in its constants — only in its power of `c`.

## `(β)` item 1 closed: the endpoint bound in the *decaying* direction

The previous entry listed three ODE estimates still needed for `(β)`.  The first — an upper bound
for the endpoint value with the sharp WKB rate — is now proved, and by an argument that needs no
approximation theory at all.

### Why the obvious route fails, and what replaces it

The corpus's endpoint bound `le_endpoint_prolateWKB` comes from the Riccati *sub*solution property
of the WKB profile: `v = −Φ′/Φ ≤ √q`, hence `Φ(1) ≥ Φ(y₀)·exp(−∫√q)`.  The reverse inequality
`v ≥ √q − …` cannot come from a supersolution — the profile `√q + q′/(4q) − b/2` is *not* one; its
Riccati defect changes sign at `2y² = 1 + s`, exactly where the corpus's outer band begins.

It follows instead from **positivity alone**.  Beyond the turning point the Sturm flux has one sign
(`deriv_nonpos_of_turning`), so `v ≥ 0` on the *whole* remaining band; and the profile `√Q` is a
repeller from below for `v′ = v² + Bv − Q`: once `v` is below `√Q` it decreases, and once it
decreases it falls faster, so it reaches `0` and then crosses it in bounded time.  A `v` that stays
nonnegative on a window therefore cannot have started far below `√Q`.

`formal/GaloisForLFunctions/HTGeometry/RiccatiNoDip.lean`, wired into the `HTGeometry` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
sub_sub_div_le_of_riccati_nonneg :
  v′ = v² + B v − Q  on [y₀,y₁],  v ≥ 0 there,  Q ≥ S² ,  0 ≤ B ≤ M
    ⟹  v(y₀) ≥ S − M − 2/(y₁ − y₀)
```

The proof is two applications of the corpus's `riccati_le_of_le_of_supersolution` against explicit
**affine** supersolutions: first the drop `m − κ(y − y₀)` with `κ = S² − Mm − m²`, which forces
`v` to reach `0` strictly inside the window, and then the descent `−λ(y − z)` from that zero, which
forces `v` below `0` — contradicting nonnegativity.  Both affine functions are supersolutions only
because of the algebra `m + M < S − 2/L ⟹ κ > 2S/L`, which is where the constant `2` in the
statement comes from.

### The prolate instance and the endpoint bound

`formal/GaloisForLFunctions/RHTower/ProlateEndpointUpperBound.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
prolatePotential_mono, prolateDrift_mono, prolateDrift_nonneg
    both Riccati coefficients are monotone on the nonnegative part of the band
prolateLogDeriv_nonneg
    beyond the turning point a positive mode has nonnegative Riccati derivative
prolateWKB_sub_le_prolateLogDeriv :
    prolateWKB c χ y₀ − 2y₁/(1−y₁²) − 2/(y₁−y₀)  ≤  prolateLogDeriv Φ y₀
prolate_endpoint_le :
    Φ b ≤ Φ a · exp(−∫_a^b (prolateWKB c χ t − 2(b+l)/(1−(b+l)²) − 2/l))
```

The last is the mirror of `exp_neg_aperture_le_endpoint`, in the direction the leakage upper bound
needs.  Its loss against the pure WKB rate is `(b−a)·(drift at `b+l` + 2/l)`, and both terms are
polynomial in the bandwidth once `l` is taken comparable to `1 − b`: the drift is `O(1/(1−b))` and
`2/l` likewise, so with `1 − b ≍ c^(−2)` the whole loss is `O(1)` in the exponent — no power of the
Gaussian clock is lost.  The integration step is
`GaloisForLFunctions.HTGeometry.le_mul_exp_integral_of_logDeriv_le'`, the windowed form added to
`EnvelopeFromLogDerivative.lean` alongside `mul_exp_integral_le_of_logDeriv_ge'` and
`exists_continuous_eqOn_Icc`.

### The action from below, with the endpoint tail

`ProlateWKBSharpAction.lean` gained the matching lower bound for the WKB integral, so the exponent
above is controlled by the sharp angular action rather than by the crude `c`:

```text
arcsin_le_pi_div_two_mul :   arcsin x ≤ (π/2)·x                        (Jordan, inverted)
angleAction_tail_le :        ∫_{arcsin b}^{π/2} √(sin²θ − s) ≤ (π/2)·√(1−b²)
sub_le_integral_prolateWKB :
    c·A(s) − c·(π/2)·√(1−b²)  ≤  ∫_{√s}^{b} prolateWKB c (−s c²)
```

With `1 − b ≍ c^(−2)` the tail `c√(1−b²)` is `O(1)`, so `∫_{√s}^{b} prolateWKB = c·A(s) + O(1)`
on both sides — `integral_prolateWKB_le_angleAction` above, and this below.

### Status of the three items

1. **Endpoint upper bound** — done, as above.
2. **Interior normalization from below** — open.  The corpus's
   `integral_sq_le_turning_amplitude_envelope` bounds `∫_{−1}^1 Φ²` above by `4e(c/√s)Φ(√s)²`,
   which is `c^(3/2)` where the truth is `c^(−1/2)`; the two-power gap is the largest single loss
   in the current chain and closing it needs the concentration of the mode in the allowed window
   `|y| ≤ √s` of width `≍ c^(−1/2)` together with the exponential decay just proved.
3. **Exterior mass upper bound** — open.  Only `outside ≥ 1/(32c²)` exists; the companion
   `outside ≤ C·Φ(1)²/c` comes from the Bessel behaviour at the regular singular point.

With the endpoint bound now two-sided at the sharp rate, items 2 and 3 are both statements about
*masses*, not about decay rates, and neither needs any further WKB input.

## `(β)` item 2: the band Sturm energy and the interior mass from below

The second of the three remaining estimates asked for a lower bound on the aperture mass in terms of
the mode's value at the turning point.  The obstruction was the *rate* at which the mode may fall
just past the turning point: the flux representation
`(1−y²)Φ′(y) = −∫_y^1 (χ + c²t²)Φ` gives only `|Φ′/Φ| = O(c²)` there, and a decay window of width
`c^(−2)` costs two powers of the bandwidth against the true width `c^(−1/2)`.

`formal/GaloisForLFunctions/RHTower/ProlateBandFluxEnergy.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`, replaces `O(c²)` by `O(c)`:

```text
prolateWeightedPotential c χ y = (1 − y²)(χ + c²y²)
prolateBandEnergy c χ Φ y      = ((1−y²)Φ′)² − (1−y²)(χ + c²y²)Φ²

hasDerivAt_prolateBandEnergy :   E′ = −P′·Φ²        (the two cross terms cancel identically)
prolateBandEnergy_one :          E(1) = 0           (the weight vanishes at the endpoint)
prolateBandEnergy_nonpos :       E ≤ 0 past the maximum of P
prolateBandEnergy_le_of_inner :  E(y) ≤ (P(ystar) − P(y))·Φ(y)²  below it
prolateFlux_sq_le :              ((1−y²)Φ′(y))² ≤ K·Φ(y)²        whenever P ≤ K on the band
```

The two branches are the same identity read in the two directions in which `P` is monotone.  Past
the maximum of `P` the energy increases and vanishes at the endpoint, so it is nonpositive there;
below the maximum the energy at the top is nonpositive and the increase of `P` bounds the rest, the
monotonicity of `Φ` turning the integrand `P′Φ²` into `P′Φ(y)²`.  Since
`max P = c²(1−s)²/4`, the resulting flux bound is `|(1−y²)Φ′| ≤ (c(1−s)/2)·Φ` — one full power of
`c` better than the flux representation, uniformly on the band and with no initial data.

Its two consequences, in the same module:

```text
neg_mul_le_deriv_of_fluxBound :  −(√K/(1−t²))·Φ(t) ≤ Φ′(t)
exp_mul_le_prolate :             Φ(a)·exp(−∫_a^b √K/(1−t²)) ≤ Φ(b)
mass_lower_of_fluxBound :
   (b−a)·(Φ(a)·exp(−∫_a^b √K/(1−t²)))² ≤ ∫_a^b Φ²
```

With `K = c²(1−s)²/4` and a window of length `b − a ≍ 1/c` the exponent is `O(1)`, so

```text
∫_a^b Φ² ≥ κ·c^(−1)·Φ(a)² ,
```

against the true `c^(−1/2)`: the loss is now `c^(1/2)`, down from `c^(3/2)` for the flux-representation
route and from `c^(2)` for the corpus's `integral_sq_le_turning_amplitude_envelope` used in reverse.
That is inside the `±3/2` slack the `FuchsEnvelope` consumer allows.

### Remaining

Only item 3 of the three: the exterior mass from above, `outside ≤ C·Φ(1)²/c`, which is the Bessel
behaviour at the regular singular point `y = 1` and for which `ProlateTwoBranch` and the Dunster
layer already supply the amplitude.  Items 1 and 2 — the endpoint bound in both directions at the
sharp WKB rate, and the interior mass from below — are proved.

## Precision accounting for `(β)`, and the correction it forces

The previous two entries recorded items 1 and 2 as "closed".  They are proved, but a precision
audit shows only item 2 is sharp enough for the `FuchsEnvelope` consumer.  Recording the arithmetic
so no later session re-derives it.

### The slack the consumer actually allows

`FuchsEnvelope`'s three conclusions use only `fuchsRate C (e j) λ < fuchsRate c (e j + 4) λ`, i.e.
that the *upper* power at one ladder index is below the *lower* power at the next.  In the aperture
variable the ladder step is `8`, and the aperture-weighted tail rate costs one more, so a two-sided
estimate with multiplicative slacks `c^{σ₊}`, `c^{σ₋}` around the true value is admissible exactly
when

```text
σ₊ + σ₋ < 7/2          (c = 2πλ², so a factor c^σ is λ^{2σ}).
```

### Item 2 is inside the budget

`mass_lower_of_fluxBound` with `K = c²(1−s)²/4` and window `[√s, √s + 1/c]` has
`∫ √K/(1−t²) = O(1)`, so `inside ≥ κ·c^(−1)·Φ(√s)²` against the true `c^(−1/2)`: `σ = 1/2`.

### Item 1 is not, and why

`prolate_endpoint_le_log` — the improved form, with the comparison window taken proportional to the
distance to the endpoint rather than fixed — has loss exactly

```text
∫_a^b 6/(1−t) dt = 6·(log(1−a) − log(1−b))            (integral_six_div_one_sub)
```

which is the best this method gives: optimizing the window fraction `θ` in
`2/θ + 1/(1−θ)` bottoms out near `5.83`, and pushing the no-dip constant `2` down to its floor `1`
only reaches `4`.  The endpoint bound must be carried to `1 − b ≍ c^(−2)` — any farther out and the
uncovered WKB tail `∫_b^1 √q ≍ c√(1−b)` itself blows up — so the loss is `(1−b)^(−6) ≍ c^(12)`.
That is `σ₊ ≈ 12`, far outside `7/2`.

The reason is structural: the no-dip bound `v ≥ √Q − M − 2/L` compares a profile `√Q ≍ c(1−t)^(−1/2)`
against a loss `≍ (1−t)^(−1)`, and the two cross exactly at `1 − t ≍ c^(−2)` — precisely the scale
the argument has to reach.  No choice of window repairs that; the method is sharp in the exponential
rate and inherently `c^(O(1))` in the prefactor.

So `RiccatiNoDip` and `prolate_endpoint_le_log` stand as unconditional theorems — uniform, with no
initial data and no approximation theory — but they are not the tool that closes `(β)`.

### What is the tool

The corpus already owns the sharp endpoint analysis, on the *radial* side, with explicit constants
and `O(1/c)` relative error — which is `σ = 0`:

```text
ProlateDunsterEndpointCoefficientBounds
    abs_radialProlate_regularCoefficient_crossing_le            |F_regular| ≤ 18/c
    abs_radialProlate_logCoefficient_sub_pi_div_four_crossing_le |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer
    abs_radialProlate_sub_regularModel_le
        the endpoint-normalized radial profile differs from the regular Bessel model by
        O(1/c) times the common Bessel amplitude, uniformly beyond the matching point
ProlateDunsterEndpointVolterra, ProlateDunsterEndpointWronskian, ProlateDunsterBesselOffDiagonal,
ProlateTwoBranch  (the Liouville–Green amplitude and its two-branch form)
```

These are unconditional and already carry the `1/c` relative precision that `(β)` needs.  So the
route for **item 3** — and for the sharp replacement of item 1 — is not new WKB theory but the
computation of the exterior mass of the *Bessel model*:

```text
∫_1^∞ (model)² ≍ R(1)²/c ,
```

after which `abs_radialProlate_sub_regularModel_le` transfers it to the actual profile with `O(1/c)`
relative error.  The model integral is elementary in the Liouville–Green variable: with
`z = κ√(2u)`, `u = t − 1`, `κ² = c²(1−s)`,

```text
∫_0^1 J₀(κ√(2u))² du = (1/κ²)∫_0^{κ√2} J₀(z)² z dz ≍ 1/κ ≍ 1/c ,
```

and the far field contributes `O(1/c)` through the `1/t` decay of the amplitude.  What that needs
from mathlib or from the corpus is `∫ J₀² z dz` — the Bessel Parseval/`J₀² + J₁²` identity — plus
the corpus's own amplitude bounds.

### Revised status of the three items

1. **Endpoint upper bound** — proved unconditionally at the sharp exponential rate with a
   `c^(O(1))` prefactor (`prolate_endpoint_le_log`); *not* sharp enough on its own, superseded for
   `(β)` by the Dunster transfer.
2. **Interior mass from below** — proved, `σ = 1/2`, inside the budget.
3. **Exterior mass** — open; reduces to the Bessel-model mass integral above, with the transfer
   already unconditional in the corpus.

## `(β)` item 3 closed: the exterior mass is `O(1/c)`

`formal/GaloisForLFunctions/RHTower/ProlateExteriorMassBound.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
radialProlateExteriorMassConstant = 9/10 + 2π·K² + 2T/5
integral_Ioi_profileDensity_le_half
integral_Ioi_crossing_radialProlate_sq_le :
    ∫_{x > 1 + 9/(8c²)} R² ≤ (2πK² + 2T/5)/c
integral_Ioc_one_crossing_radialProlate_sq_le :
    ∫_{1}^{1 + 9/(8c²)} R² ≤ 9/(2c²)
integral_Ioi_one_radialProlate_sq_le :
    ∫_{x > 1} R(x)² dx ≤ radialProlateExteriorMassConstant / c
```

for every endpoint-normalized (`R 1 = 1`) exact radial solution, `0 ≤ s ≤ 1/2`, `c ≥ 5`.  `K` is
`lgBesselCommonEnvelopeConstant` and `T` is `radialProlateDensityTransferConstant`.

No new analysis was needed: the corpus already owned both halves and they had not been combined.
`integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le` transfers the exact density
`c·R²` to the regular Bessel density in `L¹` with error `2T/c`, and
`integral_Ioi_radialProlateBesselDensity_le` dominates the Bessel density by a *bandwidth-free*
multiple of the arcsine profile density, whose total tail mass `integral_Ioi_profileDensity` is
`1/2`.  So the exact exterior density has total mass `O(1)`, and since the density carries the
factor `c`, the mass of `R²` itself is `O(1/c)`.  The collar `[1, 1 + 9/(8c²)]` between the singular
endpoint and the Dunster matching point is covered by `abs_radialProlate_le_two_endpoint` (`|R| ≤ 2`)
times its length, contributing `9/(2c²)`.

That is the sharp order: `σ = 0`.

## The single remaining bottleneck, stated exactly

With items 2 and 3 sharp, the leakage ratio `d/(1−d) = outside/inside` is controlled except for one
factor.  Normalizing `Φ(1) = 1`:

```text
outside ≤ C/c                                     (item 3, σ = 0)
inside  ≥ κ·c^(−1)·Φ(√s)²                          (item 2, σ = 1/2)
Φ(√s)  ≥ Φ(b)·exp(∫_{√s}^b prolateWKB − 6·log((1−√s)/(1−b)))   (item 1)
```

and `Φ(b) ≥ Φ(1) = 1` for free, because `Φ` is antitone past the turning point.  Every factor is
sharp except the last: item 1's loss `6·log((1−√s)/(1−b))` with `1 − b ≍ c^(−2)` is `c^(−12)`, and it
enters `inside` **squared**, so `σ₊ ≈ 24` against a budget of `7/2`.

So the whole of `(β)` now rests on one quantity:

> the barrier ratio `Φ(√s)/Φ(1)`, to relative precision `c^(±3/2)`.

Both directions of it are proved at the sharp exponential rate — `exp_neg_sharp_le_endpoint` below
and `prolate_endpoint_le_log` above — and both carry a `c^(O(1))` prefactor.  Closing the gap is the
band-side analogue of what the corpus's Dunster layer already does on the radial side: Liouville–Green
error control with an `O(1/c)` error-control function, rather than the crude Riccati comparison.  The
tools on the radial side that would be mirrored are

```text
CCMFirstRowDunsterModel      the Bessel model, its derivatives, and the common envelope constant
ProlateDunsterEndpointVolterra    endpoint-anchored Volterra transport
ProlateDunsterEndpointCoefficientBounds   |F_regular| ≤ 18/c,  |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer     the uniform O(1/c) transfer beyond the matching point
```

and the band-side model is not Bessel but parabolic-cylinder (Hermite) at the turning point
`y = √s`, with a Liouville–Green region between the two.  `HTGeometry.LiouvilleTransformation` and
`HTGeometry.LiouvilleGreenErrorBound` supply the transformation and the *oscillatory* Volterra error
bound already; what is missing is the **exponential** (barrier) analogue of
`abs_le_exp_of_oscillatoryLG`, with kernel `sinh` in place of `sin`.  That is one module of the same
shape as the oscillatory one, and it is the last unconditional input `(β)` needs.

## The barrier error bound — the last named input for `(β)`

The previous entry identified the remaining bottleneck as the barrier ratio `Φ(√s)/Φ(1)` to
relative precision `c^(±3/2)`, and named the missing tool: the **exponential** analogue of the
corpus's oscillatory Liouville–Green error bound, with kernel `sinh` in place of `sin`.  It is now
proved.

`formal/GaloisForLFunctions/HTGeometry/GronwallBackward.lean` and
`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenExponentialErrorBound.lean`, both wired into
the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
integral_comp_reflect
abs_le_exp_integral_of_volterra_bound_backward
continuous_integral_tail
abs_sub_one_le_exp_sub_one_of_volterra_bound_backward

expLGKernel u ξ t = (1 − exp(−2u(t−ξ)))/2
expLGKernel_nonneg, expLGKernel_le_half, abs_expLGKernel_le_half
IsExponentialLGSolution b u ψ V a :
    ∀ ξ ∈ [a,b],  V ξ = 1 + (1/u) ∫_ξ^b κ(ξ,t) ψ(t) V(t) dt
volterra_defect_of_exponentialLG
volterra_bound_of_exponentialLG
abs_le_exp_of_exponentialLG :
    |V ξ| ≤ exp((1/2u) ∫_ξ^b |ψ|)
abs_sub_one_le_exp_sub_one_of_exponentialLG :
    |V ξ − 1| ≤ exp((1/2u) ∫_ξ^b |ψ|) − 1
```

Two things make this the right statement rather than the naive one.  First, the anchor: on a
barrier the recessive branch accumulates from the *right*, so the Volterra equation integrates from
the far endpoint back, and the Grönwall inequality has to be reflected — that is
`GronwallBackward`, obtained from the corpus's forward inequality by the substitution
`u ↦ a + b − u` (`integral_comp_reflect`).  Second, the normalization: the raw kernel
`sinh(u(ξ−t))` is unbounded, and the entire content of writing `V(ξ) = e^{u(ξ−a)}W(ξ)` is that the
normalized kernel `e^{u(ξ−t)} sinh(u(t−ξ)) = (1 − e^{−2u(t−ξ)})/2` lies in `[0, 1/2]`.  The error
control is then the *mass* `∫_ξ^b |ψ|` of the perturbation, not a pointwise bound times the length —
which is what makes the estimate survive a barrier of length `≍ c`.

Applied to the prolate barrier after the Liouville transformation
(`HTGeometry.LiouvilleTransformation`), `ψ` is the LG defect `A''/A − g/f`, whose mass over the
barrier is `O(1/c)` away from the turning point, so the bound reads `|V − 1| ≤ e^{O(1/c)} − 1 =
O(1/c)` — precision `σ = 0`, against the `σ ≈ 12` of the Riccati route.

### What `(β)` still needs, after this

The pieces are now: sharp action (`prolateAngleAction_sub_bounds`), interior mass from below
(`mass_lower_of_fluxBound`, `σ = 1/2`), exterior mass from above
(`integral_Ioi_one_radialProlate_sq_le`, `σ = 0`), and the barrier error bound above (`σ = 0`).
What remains is *assembly*, in three steps, none of which needs a new estimate:

1. Perform the Liouville transformation on the prolate barrier explicitly — produce the `ξ`, `A`,
   `ψ` of `hasDerivAt_liouvilleTransform` for `q = (χ + c²y²)/(1 − y²)` — and check that the
   prolate mode's normalized transform satisfies `IsExponentialLGSolution`.
2. Bound the mass `∫ |ψ|` of the LG defect over `[y₀, 1 − δ]` by `O(1/c)`; this is the same
   computation the corpus already performs on the radial side in
   `CCMRadialProlateDefect.integral_volterra_exponent_le`.
3. Cross the turning layer at `y = √s`, where LG fails: the corpus's `ProlateTurningLayer` already
   propagates the amplitude across it at a fixed cost `exp(1)`, so this contributes `σ = 0`.

Step 2 is the only one with content, and its radial twin is already proved.

## The barrier Liouville–Green package is complete

The previous entry named "one module of the same shape as the oscillatory one" as the last
unconditional input.  It is built, and with it the barrier analogue of the corpus's oscillatory
Liouville–Green layer is complete end to end.

`formal/GaloisForLFunctions/HTGeometry/PerturbedBarrierVolterra.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
barrierCoshTail, barrierSinhTail, barrierKernelTail, barrierKernelTailDeriv
barrierKernelTail_eq          the separated form IS ∫_ξ^b sinh(u(ξ−t)) ψ W
hasDerivAt_barrierKernelTail       K′ = u(cosh·C − sinh·S)     (the lower-limit terms cancel)
hasDerivAt_barrierKernelTailDeriv  K″ = u²K − u ψ W            (via cosh² − sinh² = 1)
barrier_volterra_eq :
    W″ = (u² + ψ)W ,  W(b) = e^{−u(b−a)} ,  W′(b) = −u e^{−u(b−a)}
      ⟹  W ξ = e^{−u(ξ−a)} − (1/u)·∫_ξ^b sinh(u(ξ−t)) ψ W
isExponentialLGSolution_of_ode :
    hence  ξ ↦ e^{u(ξ−a)} W ξ  satisfies  IsExponentialLGSolution
abs_barrier_normalized_sub_one_le :
    |e^{u(ξ−a)} W ξ − 1| ≤ exp((1/2u)·∫_ξ^b |ψ|) − 1
barrier_two_sided :
    (2 − E)·e^{−u(ξ−a)} ≤ W ξ ≤ E·e^{−u(ξ−a)} ,   E = exp((1/2u)·∫_ξ^b |ψ|)
```

Three things had to be right.  The **anchor**: recessive data is imposed at `b`, and the Volterra
kernel integrates back from there, because forward integration of a recessive branch is unstable —
that is why `GronwallBackward` was needed.  The **separation**: `sinh(u(ξ−t)) = sinh(uξ)cosh(ut) −
cosh(uξ)sinh(ut)` splits the kernel integral into two ordinary tail primitives, so its first
derivative loses the lower-limit terms exactly (they cancel) and its second derivative is
`u²K − uψW`; the equation then follows from the corpus's uniqueness for `v″ = P v`
(`LinearSecondOrderUnique.secondOrder_eq_at`) applied to the difference against the zero solution.
The **normalization**: `e^{u(ξ−t)}sinh(u(ξ−t)) = −(1 − e^{−2u(t−ξ)})/2 ∈ [−1/2, 0]`, which is what
turns an unbounded kernel into a contraction and makes the error control the *mass* `∫_ξ^b |ψ|`
rather than a pointwise bound times the length — the difference between an estimate that survives a
barrier of length `≍ c` and one that does not.

`barrier_two_sided` is precisely the `σ = 0` replacement for `prolate_endpoint_le_log`: the relative
error is `E − 1`, and for the prolate barrier `∫|ψ| = O(1/c)` gives `E − 1 = O(1/c²)`.

### `(β)`: what is left

```text
sharp action                      prolateAngleAction_sub_bounds          ✔
interior mass from below          mass_lower_of_fluxBound        σ = 1/2 ✔
exterior mass from above          integral_Ioi_one_radialProlate_sq_le  σ = 0 ✔
barrier estimate, both sides      barrier_two_sided              σ = 0   ✔
```

Only the instantiation remains, and it is two steps:

1. **Liouville transformation of the prolate barrier.**  Produce `ξ = ∫√Q`, `A = Q^{1/4}`, and the
   defect `ψ = Q^{−1/4}(Q^{−1/4})″` for `Q = (χ + c²y²)/(1 − y²)`, and check the two identities of
   `HTGeometry.hasDerivAt_liouvilleTransform` (`X′² = 1/f(X)` and `A²X′` constant).
2. **The defect mass.**  `∫ |ψ| dξ = ∫ |Q^{−1/4}(Q^{−1/4})″| dy = O(1/c)` away from the turning
   point, because `Q ≍ c²` there so `Q^{−1/4} ≍ c^{−1/2}` and its second derivative is again
   `≍ c^{−1/2}`.  The radial twin of this computation is already proved as
   `CCMRadialProlateDefect.integral_volterra_exponent_le`.

The turning layer at `y = √s`, where Liouville–Green fails, is crossed by the corpus's
`ProlateTurningLayer` at the fixed cost `exp(1)`, i.e. `σ = 0`.

## The turning layer drops out of the leakage upper bound

A re-derivation of the assembly removes the hardest remaining region.  The previous plan anchored
the interior mass at the turning point `y = √s` and therefore had to cross the Airy layer, where
neither Liouville–Green nor the flux bound is sharp: the uniform flux bound `|(1−y²)Φ′| ≤ (c/2)Φ`
integrates to `c√s ≍ √c` over `[√s, 2√s]`, and the LG defect mass diverges like `τ^(−3/2)` as the
turning point is approached.

Anchor the interior mass at `2√s` instead.  Then:

```text
inside  ≥ κ·c^(−1)·Φ(2√s)²        mass_lower_of_fluxBound on [2√s, 2√s + 1/c],
                                   where ∫ √K/(1−t²) = O(1)
outside ≤ (C/c)·Φ(1)²             integral_Ioi_one_radialProlate_sq_le, homogeneous
Φ(1) ≤ Φ(1−ε)                     free: Φ is antitone past the turning point
leakage = outside·value²/inside   the exact mass balance
```

so

```text
leakage ≤ (C/κ)·(Φ(1−ε)/Φ(2√s))² ,
```

and the only analytic input left is the barrier ratio on `[2√s, 1−ε]` — **strictly inside the
region where Liouville–Green is valid**.  The Airy layer `[√s, 2√s]` never appears, and neither
does the endpoint collar `[1−ε, 1]`, because monotonicity of `Φ` supplies the inequality in the
direction the upper bound needs.

The two truncations cost nothing:

```text
∫_{√s}^{2√s} √q  ≈ (2√2/3)·c·s = (2√2/3)(2n+1) = O(1)
∫_{1−ε}^{1} √q   ≈ c√ε = O(1)     for ε ≍ c^(−2)
```

so `∫_{2√s}^{1−ε} √q = c·A(s) + O(1)` — the sharp action up to a bounded factor, `σ = 0`.  And the
LG defect mass on `[2√s, 1−ε]` is `O(1)`: near the turning point the integrand
`Q^{−1/4}(Q^{−1/4})″` scales as `c^{−1}s^{−1}τ^{−5/2}` against `dy = √s dτ`, and `c·s = 2n+1` is
bounded, so the mass is `C_n·τ₀^{−3/2}` with `τ₀ = 1`; near `y = 1` it is `c^{−1}(1−y²)^{−3/2}`,
integrating to `c^{−1}ε^{−1/2} = O(1)`.

### The scalar step, proved

`formal/GaloisForLFunctions/RHTower/ProlateLeakageUpperScalar.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
leakage_upper_of_mass_bounds :
    outside = inside·leakage/value² ,  L ≤ inside ,  outside ≤ U ,  value² ≤ 1
      ⟹  leakage ≤ U/L
leakage_upper_of_prolate_masses :
    with the exterior mass supplied by integral_Ioi_one_radialProlate_sq_le,
      leakage ≤ (radialProlateExteriorMassConstant / c) / L
```

This is the companion the corpus lacked: `ProlateTurningLayer.leakage_lower_of_radial_mass_bounds`
reads the same balance in the other direction.  Note that the concentration value only helps —
`value² ≤ 1` — so no lower bound on it is needed.

### `(β)`'s upper half, remaining

One item: instantiate `HTGeometry.barrier_two_sided` on `[2√s, 1−ε]`, which needs the Liouville
transformation of the prolate normal form
`Q̂ = (χ + c²y²)/(1−y²) + (1−y²)^(−2)` and the `O(1)` bound on `∫|Q̂^{−1/4}(Q̂^{−1/4})″|`.  Then
`Φ(1−ε)/Φ(2√s) ≤ E·exp(−∫_{2√s}^{1−ε}√Q̂)` with `E = O(1)`, and
`leakage ≤ C·e^{−2cA(s)} = C·c^(n+1/2)e^{−2c}` — the Fuchs upper bound.

The lower half needs the two reversed inputs: `outside` from below at the sharp order (the corpus
has only `≥ 1/(32c²)`, lossy by `c`) and `inside` from above (`integral_sq_le_turning_amplitude_envelope`,
lossy by `c²`).  Both are mass estimates, not decay estimates, and both are now the only places
where the turning layer still enters.

## Liouville–Green in the original variable — no change of variable, no inverse function

The obstruction to instantiating the barrier estimate was never the analysis: it was that Olver's
theorem is stated in the Liouville variable `ξ = ∫√Q`, whose inverse has no closed form, so applying
it requires constructing that inverse in Lean.  That detour is unnecessary.

Writing the exact solution of `Φ'' = QΦ` as `Φ = G·R` against the Liouville–Green approximant
`G = A e^{−Ξ}`, `A = Q^{−1/4}`, `Ξ' = A^{−2}`, the Wronskian `H = Φ'G − ΦG'` satisfies
`H' = −A''e^{−Ξ}Φ`, and the ratio satisfies `R' = H e^{2Ξ}/A²`.  A single integration by parts,
against the primitive `(e^{2Ξ(t)} − e^{2Ξ(y)})/2` of `e^{2Ξ}/A²` chosen to vanish at `y`, collapses
the nested integral to **one** Volterra equation with a bounded kernel — no Fubini, no change of
variable, the phase entering only as the explicit function `Ξ`.

`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenPhaseErrorBound.lean` and
`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenOde.lean`, both wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
lgPhaseKernel Ξ ξ t = (1 − exp(−2(Ξ t − Ξ ξ)))/2 ,   0 ≤ · ≤ 1/2 when Ξ ξ ≤ Ξ t
IsPhaseLGSolution b Ξ ψ R a :  R ξ = 1 − ∫_ξ^b lgPhaseKernel Ξ ξ t · ψ t · R t
phase_volterra_defect, phase_volterra_bound
abs_le_exp_of_phaseLG,  abs_sub_one_le_exp_sub_one_of_phaseLG,  phaseLG_two_sided

lgApprox, lgApproxDeriv, lgWronskian, lgRatio
hasDerivAt_lgApprox        G' = (A' − 1/A) e^{−Ξ}
hasDerivAt_lgApproxDeriv   G'' = (A'' + A^{−3}) e^{−Ξ} = Q G + A'' e^{−Ξ}
hasDerivAt_lgWronskian     H' = −(Φ · A'' · e^{−Ξ})
hasDerivAt_lgRatio         R' = H e^{2Ξ}/A²
isPhaseLGSolution_lgRatio  the Volterra equation, by the integration by parts above
lgRatio_two_sided :
    2 − E ≤ Φ(y)/(A(y)e^{−Ξ(y)}) ≤ E ,        E = exp(½ ∫_y^b |A A''|)
```

`A A'' = Q^{−1/4}(Q^{−1/4})''` is exactly Olver's error-control density, and the estimate is stated
with `y`-integrals throughout.  For the prolate barrier `∫|A A''| = O(1)` on `[2√s, 1−ε]`, so
`E = O(1)`: precision `σ = 0`.

### The remaining obstruction, stated exactly

`lgRatio_two_sided` describes the solution *normalized to the approximant at the right endpoint* —
the recessive branch.  The prolate mode is a different solution, and the Wronskian
`W = Φ'Φ_r − ΦΦ_r'` between them is constant, with

```text
Φ(b)/Φ(y) ≤ Φ_r(b)/Φ_r(y)      ⟺      W ≤ 0      ⟺      v ≥ w at one point,
```

`v = −Φ'/Φ` and `w = −Φ_r'/Φ_r`.  A *small* `W` is not enough: the dominant branch grows by
`e^{2Ξ(b)}`, so only the sign is usable.  And `v ≥ w` at a point is again a lower bound on `v` of
precision `O(1)` against `√Q` — which is what Liouville–Green itself would provide, so the argument
closes on itself.

What breaks the circle is the boundary condition the mode actually satisfies.  Note that
`Ξ(1) = ∫^1 √Q` **converges** (`√Q ≍ c(1−y)^{−1/2}`), so at `y = 1` the recessive/dominant
distinction degenerates — as it must, `y = 1` being a regular singular point where the natural basis
is (analytic, logarithmic), not (recessive, dominant).  The prolate mode is the analytic one, and
its decomposition in the Liouville–Green basis is fixed by matching at that point.

That is precisely what the corpus's Dunster layer already does on the *radial* side
(`ProlateDunsterEndpointCoefficientBounds`: `|F_regular| ≤ 18/c`, `|F_log − π/4| ≤ 141/c`).  The
band-side mirror of that layer — Frobenius/Bessel matching at `y = 1⁻` — is the one remaining input
for `(β)`'s upper half, and it is a construction of the same shape as one the corpus already owns.

## The bridge from the Liouville–Green branch to the actual mode, and the endpoint model identified

`lgRatio_two_sided` describes one distinguished solution — the one normalized to the approximant at
the right endpoint.  The bridge to an arbitrary solution of the same equation is the Wronskian, and
it is now formal.

`formal/GaloisForLFunctions/HTGeometry/DecayRatioComparison.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
solutionWronskian Φ Φ' Ψ Ψ' y = Φ' y · Ψ y − Φ y · Ψ' y
hasDerivAt_solutionWronskian, solutionWronskian_const     it is constant along v'' = P v
solutionWronskian_nonpos_iff :   W ≤ 0  ↔  Φ'/Φ ≤ Ψ'/Ψ
ratio_le_of_solutionWronskian_nonpos :
    W ≤ 0  ⟹  Φ(b)/Φ(a) ≤ Ψ(b)/Ψ(a)
```

So the leakage upper bound reduces to **one sign**: with `Ψ` the Liouville–Green branch and `Φ` the
prolate mode, `W ≤ 0` transfers the whole two-sided estimate to the mode.  Only the sign is usable —
on a barrier the two branches differ by `e^{2Ξ(b)}`, so a merely small `W` carries no information.

### What fixes the sign, computed

The sign is decided at `y = 1`, and the endpoint model is now identified explicitly.  Writing
`u = 1 − y` and `K = χ + c²`, the Sturm form `((1−y²)Φ')' = (χ + c²y²)Φ` becomes, to leading order,

```text
(u Φ_u)_u = (K/2) Φ ,
```

and the substitution `z = √(2K u)` — so `z ≍ 1` exactly when `1 − y ≍ c^(−2)`, the scale at which
the Liouville–Green window must stop — turns it into

```text
Φ_zz + (1/z) Φ_z − Φ = 0 ,
```

the **modified** Bessel equation of order zero.  So the band-side endpoint model is `I₀`, `K₀` — not
`J₀`, `Y₀`; the band side of the endpoint is the forbidden region, whereas the radial side that the
corpus's Dunster layer already treats is the allowed one.

The mode is analytic at `y = 1`, hence the `I₀` branch, and `I₀` is the branch that *grows inward* —
which is the Liouville–Green recessive branch.  So the sign is the expected one, and the content of
the remaining work is the quantitative matching at `z ≍ 1`.

Two consequences worth recording.  First, the normal-form potential

```text
Q̂ = (χ + c²y²)/(1−y²) − (1−y²)^(−2)
```

is **negative** for `1 − y² < 1/K`: the barrier ends at exactly the scale `c^(−2)`, and beyond it the
normal form is the Euler equation `W'' + W/(4(1−y)²) = 0` of an exponent-`(0,0)` singularity, whose
solutions are `√u` and `√u log u`.  That is why no crude comparison of `v` against `√Q̂` can decide
the sign there — both are `Θ(c²)` at the matching point and the constants decide.

Second, this is a construction of the same shape as one the corpus owns: the radial layer
(`CCMFirstRowDunsterModel`, `ProlateDunsterEndpointVolterra`,
`ProlateDunsterEndpointCoefficientBounds`, `ProlateDunsterUniformTransfer`) does exactly this with
`besselJ0` in place of `I₀`.  mathlib has neither; the corpus built `besselJ0` for the radial side,
and the band side needs `besselI0` built the same way.

### `(β)`'s upper half, remaining

```text
sharp action                     prolateAngleAction_sub_bounds              ✔
interior mass from below         mass_lower_of_fluxBound            σ = 1/2 ✔
exterior mass from above         integral_Ioi_one_radialProlate_sq_le  σ = 0 ✔
mass balance → leakage           leakage_upper_of_mass_bounds              ✔
Liouville–Green, original variable  lgRatio_two_sided                σ = 0 ✔
branch → actual mode             ratio_le_of_solutionWronskian_nonpos      ✔
```

One item: the modified-Bessel endpoint layer at `z = c√(2(1−y))`, giving `W ≤ 0`.

## The modified Bessel function of order zero, built

The endpoint model identified in the previous entry needs `I₀`, which mathlib does not have and the
corpus did not have either — it built `besselJ0` for the radial side and nothing for the band side.

`formal/GaloisForLFunctions/RHTower/BesselIZeroODE.lean`, wired into the `RHTower` umbrella, axioms
`[propext, Classical.choice, Quot.sound]`:

```text
besselI0 u            = (1/π) ∫_0^π cosh(u sin θ) dθ
besselI0Deriv u       = (1/π) ∫_0^π sin θ · sinh(u sin θ) dθ
besselI0SecondDeriv u = (1/π) ∫_0^π sin²θ · cosh(u sin θ) dθ

abs_sinh_le, cosh_le_cosh_of_abs_le, abs_mul_sin_le
hasDerivAt_besselI0, hasDerivAt_besselI0Deriv        differentiation under the integral
integral_sin_mul_sinh_eq                            the integration by parts
besselI0SecondDeriv_sub_besselI0
besselI0_ode :   I₀'' + I₀'/u − I₀ = 0
besselI0_zero, besselI0_pos, besselI0Deriv_nonneg, monotoneOn_besselI0
besselI0Deriv_le_besselI0,  besselI0_logDeriv_le_one :   I₀'/I₀ ≤ 1
```

The construction mirrors the corpus's `besselJ0` line for line with the circular functions replaced
by hyperbolic ones; the one structural difference is the domination.  `cos` is bounded, `cosh` is
not, so differentiation under the integral sign is justified on `Metric.ball u 1` with the bounds
`sinh(|u|+1)` and `cosh(|u|+1)` rather than on the whole line with the bound `1`.

`besselI0_logDeriv_le_one` is the one qualitative fact the matching will use: pointwise
`sin θ · sinh(u sin θ) ≤ cosh(u sin θ)` because `sin θ ≤ 1` and `sinh ≤ cosh`, so the analytic
branch's logarithmic derivative never exceeds that of `e^z`.

### What the matching still needs

With `I₀` in hand, the band-side endpoint layer is the mirror of the corpus's radial one:

```text
radial (allowed, J₀)                        band (forbidden, I₀)
CCMFirstRowDunsterModel                     the I₀ model at z = c√(2(1−y))
ProlateDunsterEndpointWronskian             endpoint Wronskian values
ProlateDunsterEndpointVolterra              endpoint-anchored transport
ProlateDunsterEndpointCoefficientBounds     |F_regular| ≤ 18/c, |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer               the uniform O(1/c) transfer
```

and its output is the sign `W ≤ 0` that `ratio_le_of_solutionWronskian_nonpos` consumes.  Note that
the comparison cannot be done by inspecting `I₀'/I₀` against the Liouville–Green profile directly:
in the `z` variable both are `1 + O(1/z)` at the matching point `z ≍ 1`, so the constants decide,
which is exactly what the Volterra transfer computes.

## The band-side comparison equation

`formal/GaloisForLFunctions/RHTower/BesselIZeroModel.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
besselIModel c ξ x            = I₀(c ξ x)
besselIModelDeriv, besselIModelSecondDeriv
hasDerivAt_besselIModel, hasDerivAt_besselIModelDeriv
besselIModel_ode :
    V'' + (ξ'/ξ − ξ''/ξ') V' − c² (ξ')² V = 0
```

exactly, for every `c` and every phase `ξ`, with nothing approximated: the second derivative
contributes `c²ξ'² I₀ − (cξ'²/ξ) I₀' + c ξ'' I₀'` by `besselI0_ode`, and the first-order coefficient
is exactly the negative of the two `I₀'` terms.

This is the band-side counterpart of `CCMFirstRowDunsterModel.lgBesselModel_ode`, with the sign of
the zero-order term reversed — the band endpoint is the forbidden region.  It is stated for an
arbitrary phase rather than for a fixed one, so the choice of band-side Liouville variable can be
made when the defect estimate is written.

### The band-side layer, remaining

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed, xiAmplitude         the band Liouville variable               —
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

whose output is the sign `W ≤ 0` consumed by `ratio_le_of_solutionWronskian_nonpos`.

## The band-side Liouville variable

`formal/GaloisForLFunctions/RHTower/BandEndpointPhase.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
bandEndpointPhase s y = ∫_{arcsin y}^{π/2} √(sin²θ − s) dθ
bandEndpointPhase_one, bandEndpointPhase_nonneg, bandEndpointPhase_pos
prolateWKBProfile_eq_div :   √((y²−s)/(1−y²)) = √(y²−s)/√(1−y²)
hasDerivAt_bandEndpointPhase :  Ξ_s' (y) = −√((y²−s)/(1−y²))
sq_prolateWKBProfile :          (Ξ_s')² = (y²−s)/(1−y²)
```

so `c²(Ξ_s')² = (χ + c²y²)/(1−y²)` exactly with `χ = −sc²` — the phase for which the modified-Bessel
model `I₀(c Ξ_s)` carries the right leading potential.

The point of the angular form is that it is not an improper integral at all: `∫_y^1 √((t²−s)/(1−t²))dt`
has an inverse-square-root singularity at the endpoint, but `∫_{arcsin y}^{π/2} √(sin²θ − s) dθ` is a
continuous integrand on a compact interval, and the `y`-derivative comes out by the chain rule
against `Real.hasDerivAt_arcsin`.  The same device removed the singularity from the sharp action
earlier on this card.

`Ξ_s` vanishes at `y = 1` and behaves like `√(1−s)·√(2(1−y))` there, so `c Ξ_s ≍ 1` exactly when
`1 − y ≍ c^(−2)` — the scale at which the Liouville–Green window stops and the endpoint model takes
over, which is what makes the two windows overlap.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed                      bandEndpointPhase, hasDerivAt_…           ✔
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The model drift is elementary — the square root cancels

The comparison equation's first-order coefficient is `Ξ'/Ξ − Ξ''/Ξ'`, and the second term looked as
though it would carry the square root of the WKB profile.  It does not.

`BandEndpointPhase.lean` (extended; wired, axioms `[propext, Classical.choice, Quot.sound]`):

```text
hasDerivAt_prolateWKBArg :
    d/dy [(y²−s)/(1−y²)] = 2y(1−s)/(1−y²)²
hasDerivAt_prolateWKBProfile :
    Ξ'' = −P' ,   P' = (2y(1−s)/(1−y²)²)/(2P)
bandModelDrift s y = y(1−s)/((1−y²)(y²−s))
secondDeriv_div_deriv_bandEndpointPhase :
    Ξ''/Ξ' = bandModelDrift s y
```

The cancellation is exact: `Ξ''/Ξ' = P'/P = (2y(1−s)/(1−y²)²)/(2P²)` and `P² = (y²−s)/(1−y²)`, so the
profile disappears entirely and the ratio is a rational function of `y` with the two poles one
expects — at the turning point `y² = s` and at the endpoint `y² = 1`.

Near the endpoint `bandModelDrift → 1/(2(1−y))` and `Ξ'/Ξ → −1/(2(1−y))`, so the comparison drift
`B_m = Ξ'/Ξ − Ξ''/Ξ' → −1/(1−y)`, whose contribution `B_m²/4 + B_m'/2 → 1/(4(1−y)²) − 1/(2(1−y)²)`
cancels the `−1/(1−y²)² → −1/(4(1−y)²)` of the true normal form.  That cancellation of the leading
`(1−y)^(−2)` singularities is exactly why the band defect is `O(1)` rather than `O(c²)`, and it is
now a computation on explicit rational functions rather than an asymptotic claim.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed                      bandEndpointPhase, hasDerivAt_…           ✔
xiSpeedDeriv                                  hasDerivAt_prolateWKBProfile,
                                              secondDeriv_div_deriv_…                   ✔
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The comparison defect: the algebraic collapse

`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenDriftAlgebra.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
lgDrift Ξ Ξ' D y = Ξ'(y)/Ξ(y) − D(y)
hasDerivAt_lgDrift :   B' = Ξ''/Ξ − (Ξ')²/Ξ² − D'
lgDrift_normalForm :   with Ξ'' = Ξ'·D,
    B²/4 + B'/2 = −(Ξ')²/(4Ξ²) + D²/4 − D'/2
lgDrift_normalForm_of_hasDerivAt
```

`B = Ξ'/Ξ − Ξ''/Ξ'` is the first-order coefficient of the comparison equation `besselIModel_ode`, and
`B²/4 + B'/2` is what it contributes on passing to normal form.  The identity says the cross terms
`Ξ'D/Ξ` cancel and — the point — **no `Ξ''/Ξ` survives**: the model's normal-form potential is built
from `(Ξ')²/Ξ²` and from `D` alone.

For the prolate band `D = bandModelDrift` is rational (the previous entry), so the whole comparison
carries exactly one transcendental ingredient, `(Ξ')²/Ξ²`.  Writing the defect against the true
normal-form potential `Q̂ = c²(Ξ')² − (1−y²)^(−2)` and noting that the two `c²(Ξ')²` cancel — that is
what the phase was chosen for — the defect is

```text
(Ξ')²/(4Ξ²) − 1/(1−y²)² − D²/4 + D'/2 ,
```

with no `c` in it at all.  At the endpoint each of the four terms is `Θ((1−y)^(−2))` — respectively
`1/16`, `−1/4`, `−1/16`, `+1/4` times `(1−y)^(−2)` — and they sum to zero.  That is the cancellation
that makes the comparison defect `O(1)` rather than `O(c²)`, and it is now an identity between
explicit functions rather than an asymptotic assertion.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed, xiSpeedDeriv        bandEndpointPhase + both derivatives      ✔
lgNormalFormDefect (its algebra)              lgDrift_normalForm                        ✔
its mass bound                                the O(1) mass bound                       —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The card's stated bottleneck is closed: the barrier ratio, two-sided

The bottleneck recorded above was

> the barrier ratio `Phi(y0)/Phi(1)`, to relative precision `c^(±3/2)`.

`RHTower/ProlateBarrierRatioTwoSided.lean` (wired, axiom-clean) delivers both directions with the
*same* sharp exponential:

```
prolateBand_sq_le_exp_bandPhase
    Phi(y0)^2  <=  C · exp(2 c Xi_s(y0) + Lambda)

prolateBand_barrier_ratio_two_sided
    exp(c Xi_s(y0) + 6 log((1-alpha)/(1-y0))) / (6 pi sqrt(c Xi_s(alpha)))  <=  Phi(y0)
      and the square bound above
```

with `C = 1 + (1-alpha^2)(barrier(alpha) + 6/(1-alpha))^2 / (c^2(alpha^2-s))` and
`Lambda = prolateScaleLog s y0 alpha = log((alpha^2-s)(1-y0^2)/((y0^2-s)(1-alpha^2)))`.

Since both bounds carry `exp(c Xi_s(y0))`, the relative precision is the product of the two
prefactors: `sqrt(C exp Lambda)` and `6 pi sqrt(c Xi_s(alpha))`.  With `y0 = 2 sqrt s`, `alpha` a
fixed collar edge, `cs = 2n+1` and `s ~ 1/c`,

```
exp Lambda = O(1/s) = O(c) ,     C = O(1) ,     c Xi_s(alpha) = O(c) ,
```

so the relative precision is `O(sqrt c) · O(sqrt c) = O(c)` — inside the required `c^(3/2)`.

The route that achieves this is *not* the parabolic-cylinder / Liouville-Green package the earlier
entry proposed.  It is the **Sturm amplitude envelope at a matched scale**
(`HTGeometry/SturmAmplitudeEnvelope.lean`): for `(pR')' + QR = 0` and any scale `K`,

```
G = R^2 + (pR')^2/K ,     |G'/G|  <=  sqrt K · |1/p - Q/K|  +  |K'|/K .
```

Taking `K = -Qp` in the band makes `1/p - Q/K = 2/p`, hence `sqrt K (2/p) = 2 c P(y)` — *exactly
twice the WKB rate* — and the entire extra cost is the logarithmic variation of the scale, two
elementary logarithms.  Taking `K = c^2 s` on the allowed interval `[0, 2 sqrt s]` gives
`|1/p - Q/K| = 1/(1-y^2) - 1 + y^2/s in [0,5]` and `sqrt K = c sqrt s`, so the turning layer is
crossed at cost `exp(10 c s)`, a constant for a fixed mode.  No turning-point model function is
needed at all: neither Airy, nor parabolic cylinder, nor a Liouville-Green error-control function.

Consequences already landed:

```
RHTower/ProlateApertureMassSharp.lean
    prolate_allowed_sq_le, sturmAmplitude_const_le_three_mul_band,
    prolateBandAmplitude_le_uniform, prolate_sq_le_aperture_envelope,
    integral_sq_le_aperture_envelope, integral_sq_le_exp_sharp_action_amplitude
RHTower/ProlateLeakageLowerSharp.lean
    integral_Ioi_radialProlate_sq_ge_half,
    prolate_leakage_ge_exp_sharp_amplitude, prolate_leakage_ge_explicit
```

`prolate_leakage_ge_explicit` is the leakage lower bound at the standard matching point
`y0 = 2 sqrt s`, entirely elementary in its constants:

```
besselEnergyFloor/(864 c)
  / (2 (2 (3C+1) exp(2c(1 + (s/4) log s) + log((alpha^2-s)/(3s)) + log((1-4s)/(1-alpha^2))
                      + 10 c s)))
    <=  leakage .
```

Both halves of `(beta)` are now Lean-proved, axiom-clean, and inside the precision budget
(`sigma_+ + sigma_- = 5/2 < 7/2`).

## `(beta)` delivered: the leakage, two-sided, at the sharp action

`RHTower/ProlateLeakageTwoSided.lean` (wired, axiom-clean):

```
prolate_leakage_two_sided

  besselEnergyFloor/(864 c)
    / (2 (2 (3C+1) exp(2c(1 + (s/4) log s)
                        + log((alpha^2-s)/(3s)) + log((1-4s)/(1-alpha^2)) + 10 c s)))
      <=  leakage  <=
  radialProlateExteriorMassConstant/c
    · ((6 pi sqrt(c Xi_s(alpha)))^2 exp(2 E) / (b - 2 sqrt s))
    · exp(-2(c Xi_s(2 sqrt s) + 6 log((1-alpha)/(1-2 sqrt s))))
```

with `E = (c b + 12)(b - 2 sqrt s)/(1 - b^2)` and `C` the anchor constant.  Both directions carry the
same exponential `exp(-2 c Xi_s(2 sqrt s))`, and `Xi_s(2 sqrt s) <= A(s) = 1 + (s/4) log s + O(s)`,
so with `cs = 2n+1` and `s ~ 1/c` the shared exponential is `exp(-2c) c^{n+1/2}` up to a bounded
factor.  The gap between the two prefactors is `c^{5/2}`, inside the card's budget of `7/2`.

The last new input was the interior mass from below, `RHTower/ProlateInteriorMassLower.lean`:

```
prolateFlux_sq_le_band            |(1-t^2) Phi'| <= (1-t^2)(barrier(t) + 6/(1-t)) |Phi|
one_sub_sq_mul_band_barrier_le    (1-t^2)(barrier(t) + 6/(1-t))  <=  c b + 12      (t <= b)
prolate_window_mass_lower         (b-y0)(Phi(y0) exp(-(cb+12)(b-y0)/(1-b^2)))^2 <= int_{y0}^b Phi^2
prolate_aperture_mass_lower       the same against the full aperture
```

At `y0 = 2 sqrt s` the barrier constant `c b + 12` is `O(sqrt c)` for a fixed mode, so a window of
width `1/(c b + 12)` costs a bounded exponential and contributes `Phi(y0)^2/(c b + 12)` — the true
order.  No turning-point model function (Airy, parabolic cylinder, Liouville-Green error control)
is used anywhere in either direction.

## Lean progress — `(11)` and the Gram-Schmidt property `(10a)` are theorems

`RHTower/HermiteContrastLadder.lean` (wired, axiom-clean).  Both are pure algebra in the centre
values, with no hypothesis beyond `a (k+1) != 0`, so they are unconditional:

```
contrastPartialSum a k = sum_{j<=k} (a j)^2                       S_k
contrastLadder a k     = (-a_0, ..., -a_k, S_k/a_(k+1), 0, ...)   w_k
rawContrast a m        = a_0 e_m - a_m e_0                        r_m

contrastLadder_inner_centre        <w_k, a> = 0
contrastLadder_inner_of_lt         <w_k, w_m> = 0   (k < m)
contrastLadder_inner_eq_zero       <w_k, w_m> = 0   (k != m)
contrastLadder_succ_ne_zero        w_k is not the zero vector
contrastLadder_inner_rawContrast        <w_k, r_m> = 0     for 1 <= m <= k
contrastLadder_inner_rawContrast_succ   <w_k, r_(k+1)> = a_0 S_(k+1) / a_(k+1)
```

Each identity is the same two-term cancellation: the head of `w_k` contributes `-S_k` and its single
tail entry contributes `+S_k`.  The last two are the Gram-Schmidt property in the sharp form: `w_k`
annihilates every earlier raw contrast and pairs nontrivially with the next one, which is exactly
what characterizes the `(k+1)`-st Gram-Schmidt vector of the ordered family `r_1, r_2, ...`.

The explicit combination realizing `w_k` inside `span{r_1, ..., r_(k+1)}` is

```
w_k = sum_{m=1}^{k} (-a_m/a_0) r_m  +  (S_k/(a_0 a_(k+1))) r_(k+1) ,
```

whose zero-coordinate is `-[-(S_k - a_0^2)/a_0 + S_k/a_0] = -a_0` as required.

Both pairings are stated as finite sums over any `range N` containing the supports, so no `l^2`
machinery is needed; the vectors have finite support by construction.

## Lean progress — `(4)` is a theorem for every `j`

`RHTower/HermiteCentreValueClosedForm.lean` (wired, axiom-clean) closes the card's `(4)`:

```
hermiteOriginValue_sq_two_mul
    hermiteOriginValue (2m)^2  =  sqrt 2 * centralBinom m / 4^m

hermiteOriginValue_sq_four_mul
    hermiteOriginValue (4j)^2  =  hermiteOriginValue 0 ^ 2 * binom(4j, 2j) / 16^j
```

i.e. `a_j^2 = a_0^2 q_j` with `q_j = binom(4j,2j)/16^j`, and `a_0^2 = sqrt 2` is the corpus's
`hermiteOriginValue_sq_zero`.  Only the corpus's own two-step origin recursion
`eval_zero_hermitePoly_add_two` and mathlib's central binomial recursion
`Nat.succ_mul_centralBinom_succ` are used; the induction works because the two ratios agree exactly:

```
a_{2m+2}^2 / a_{2m}^2                              = (2m+1)/(2m+2)
[centralBinom (m+1)/4^(m+1)] / [centralBinom m/4^m] = 2(2m+1)/(4(m+1)) = (2m+1)/(2m+2)
```

Every power of `pi` cancels between the squared origin value and the `L^2` normalisation, which is
why the closed form is rational times `sqrt 2`.

With this and `HermiteContrastLadder.lean`, the whole algebraic layer of the ladder card —
`(4)`, `(5)`, `(10)`, `(10a)`, `(11)` — is unconditional Lean.  What is left is analytic: the
prolate-to-Hermite convergence `(3)` and the compression spectrum statement `(8)`.

## Lean progress — the interlacing mechanism of `(8)`

`RHTower/SecularEquationInterlacing.lean` (wired, axiom-clean) proves the mechanism the card's `(8)`
runs on.  Compressing `diag(d_0, d_1, ...)` to the hyperplane orthogonal to `ell` gives the secular
equation `F(mu) = sum_j (ell_j)^2/(d_j - mu) = 0`, and:

```
secular d ell N mu            the secular function
secular_denom_ne              inside a gap every denominator is nonzero
secular_strictMonoOn          F is strictly increasing on (d_k, d_(k+1))
continuousOn_secular          and continuous there
tendsto_secular_atBot         F -> -infinity  at the left end of the gap
tendsto_secular_atTop         F -> +infinity  at the right end
exists_unique_secular_root    hence EXACTLY ONE root in each gap
```

This is the card's "there is exactly one constrained eigenvalue `mu_k(lambda)` in
`(d_k(lambda), d_(k+1)(lambda))`" — the interlacing half of `(8)` — for the scalar model, with no
hypothesis beyond `d` strictly increasing and the two adjacent `ell` entries nonzero.  The monotone
step is the identity

```
(ell_j)^2/(d_j - y) - (ell_j)^2/(d_j - x) = (ell_j)^2 (y - x) / ((d_j - x)(d_j - y)) ,
```

whose denominator is positive because inside a gap the two factors have the same sign, whichever
side of the gap the index falls on.

For the location of the root:

```
secular_smul            the equation is scale covariant, so the root may be studied in the
                        normalized variable theta = mu / d_(k+1)
limit_secular_root_iff  in the limit the equation degenerates to  -S/theta + T/(1-theta) = 0,
                        whose root is exactly  theta = S/(S+T)
```

With `S = S_k = sum_{j<=k} ell_j^2` and `T = ell_(k+1)^2`, the root is `S_k/S_(k+1)`, and the
coordinate limits `ell_j^2 -> A q_j` turn that into `Q_k/Q_(k+1) = theta_k` — the card's `(8)`.  What
remains between these and `(8)` is the uniformity: the passage from the exact equation at finite
`lambda` to the degenerate one, which is where the Fuchs separation `d_j/d_(j+1) -> 0` enters.

## Lean progress — `(8)`'s location statement, quantitatively

The item recorded above as remaining — "the passage from the exact secular equation at finite
`lambda` to the degenerate one" — is now a theorem.  Same module,
`RHTower/SecularEquationInterlacing.lean`:

```
secular_split               the three-block decomposition around the gap
secular_lower_block_le      lower block  <=  -S_k/mu
secular_lower_block_ge      lower block  >=  -S_k/(mu - eps d_(k+1))
secular_upper_block_bounds  upper block in  [0, T/((M-1) d_(k+1))]

secular_root_le             mu/d_(k+1)  <=  S_k/S_(k+1) + eps
le_secular_root             mu/d_(k+1)  >=  S_k/(S_(k+1) + T/(M-1))
```

where `S_k = sum_{j<=k} ell_j^2`, `T = sum_{j>k+1} ell_j^2`, and the two slack parameters are the
Fuchs separation itself:

```
d_j <= eps · d_(k+1)     for j <= k          (the lower modes are much smaller)
d_j >= M · d_(k+1)       for k+1 < j <= N    (the higher modes are much bigger)
```

As `eps -> 0` and `M -> infinity` both bounds converge to `S_k/S_(k+1)`, and the coordinate limits
`ell_j^2 -> A q_j` turn that into `Q_k/Q_(k+1) = theta_k`.  So the card's `(8)` is now:

- **interlacing** — `exists_unique_secular_root`, exactly one root per gap;
- **location** — `secular_root_le` and `le_secular_root`, the root pinned between two explicit
  expressions that squeeze to `theta_k` as the separation widens.

Both are unconditional and quantitative, with no limit hypothesis: they hold at every finite
`lambda` for which the two separation inequalities hold, which is what `(7)` supplies.

The proof of the lower bound splits on whether the root is already below `S_k/S_(k+1)`: if it is,
the singular term is bounded by `S_(k+1)/d_(k+1)` and the equation gives the bound directly; if it
is not, the bound is immediate because `S_k/(S_(k+1) + T/(M-1)) <= S_k/S_(k+1)`.
