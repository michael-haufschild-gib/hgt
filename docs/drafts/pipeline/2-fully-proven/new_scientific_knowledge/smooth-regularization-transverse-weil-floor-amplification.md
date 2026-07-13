# Smooth edge regularization forces transverse restricted-Weil floor amplification

- **ID:** `smooth-regularization-transverse-weil-floor-amplification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the closed restricted Weil form of Connes--Consani--Moscovici and Suzuki;
  `cofinal-two-edge-weil-completeness-landau-oscillation.md`; the exact one-sided transverse
  spectrum and negative-channel abscissa law for the sharp logarithmic rectangle
- **Statement:** The negative part of the true restricted-Weil spectral floor dominates the exact
  sharp rectangular detector after multiplication by its fixed mass `2L`. Consequently every
  off-critical transverse displacement forces exponential negative-floor amplification, and RH is
  equivalent to critical Dirichlet abscissa at most one for the sampled negative floor.

## 1. Setup

Let `Q_W^a` be the closed Weil form on `L2(-a,a)`, let `A_a` be its self-adjoint
compact-resolvent realization, and put

```text
lambda_0(a)
 =inf{Q_W^a(v)/||v||_2^2:
      0!=v in D(Q_W^a)},

eta(a)=max(0,-lambda_0(a)).                              (1)
```

The aperture spaces are embedded by zero extension. Hence `lambda_0` is nonincreasing and `eta`
is nondecreasing.

Fix `L>0`. For `a>=L`, let

```text
h_(L,a)=1_[a-L,a]+1_[-a,-a+L]                           (2)
```

and let `Q_L(a)` be its absolutely convergent zero-side divisor polarization. Its centered
Laplace transform is

```text
F_(L,a)(w)
 =exp(aw)A_L(w)+exp(-aw)A_L(-w),

A_L(w)=(1-exp(-Lw))/w,   A_L(0)=L.                      (3)
```

The sharp profile itself need not belong to the logarithmic form domain. The theorem therefore
does not insert `(2)` directly into the Rayleigh quotient. It first regularizes both edges inside
the aperture and then passes to the closed-form limit.

## 2. Inward edge regularization

For `0<epsilon<min(L,a-L)`, let

```text
kappa_epsilon^+(x)=epsilon^(-1)1_[-epsilon,0](x),
kappa_epsilon^-(x)=kappa_epsilon^+(-x),

h_(L,a,epsilon)
 =1_[a-L,a]*kappa_epsilon^+
  +1_[-a,-a+L]*kappa_epsilon^-.                         (4)
```

Both convolutions expand only toward the interior of `[-a,a]`. The two summands have disjoint
supports, are continuous piecewise linear, vanish at `+-a`, and belong to `H01(-a,a)`, hence to
`D(Q_W^a)`.

Put

```text
m_epsilon(w)=A_epsilon(w)/epsilon.                       (5)
```

Direct convolution gives

```text
F_(L,a,epsilon)(w)
 =exp(aw)A_L(w)m_epsilon(w)
  +exp(-aw)A_L(-w)m_epsilon(-w).                         (6)
```

For each `w`,

```text
m_epsilon(w)->1                                         (7)
```

as `epsilon->0+`. On the centered critical strip `|Re w|<=1/2`, the integral representation

```text
m_epsilon(w)=integral_0^1 exp(-epsilon*t*w)dt            (8)
```

gives the uniform bound `|m_epsilon(w)|<=exp(1/2)` for `0<epsilon<=1`.
Together with `|A_L(w)|=O_L(1/|w|)` and

```text
sum_(w in Z_Xi)|w|^(-2)<infinity,                        (9)
```

this supplies a summable majorant for the squared transforms. Dominated convergence in the
multiplicity-exact zero sum therefore gives

```text
Q_W^a(h_(L,a,epsilon))->Q_L(a).                          (10)
```

For `epsilon<=L`, one regularized edge consists of a ramp of length `epsilon`, a plateau of
length `L-epsilon`, and a descending ramp of length `epsilon`. Hence

```text
||h_(L,a,epsilon)||_2^2
 =2(L-epsilon/3)->2L.                                    (11)
```

## 3. Sharp trial-to-floor inequality

The variational definition `(1)` and admissibility of `(4)` give

```text
Q_W^a(h_(L,a,epsilon))
 >=lambda_0(a)||h_(L,a,epsilon)||_2^2.                   (12)
```

Letting `epsilon->0+` in `(12)` and using `(10)`--`(11)` proves the sharp bridge

```text
Q_L(a)>=2L lambda_0(a).                                  (13)
```

Taking negative parts yields the positive domination law

```text
Q_L(a)^-<=2L eta(a).                                     (14)
```

The constant `2L` is exactly the `L2` mass of the sharp two-edge profile; no regularization loss
remains.

## 4. Exponential floor amplification

Sample at logarithmic aperture

```text
a_n=(1/2)log n,
eta_L,N(n)=if n>=N then eta(a_n) else 0,                 (15)
```

where `N` is large enough that `a_n>=L`. Let

```text
delta_*
 =sup{Re rho-1/2:xi(rho)=0, Re rho>1/2},                (16)
```

with `delta_*=0` under RH.

The exact one-sided rectangular spectrum says that, for every `alpha>=0`,

```text
Q_L(a_n)>=-C n^alpha eventually
 iff delta_*<=alpha.                                    (17)
```

Combining `(14)` and `(17)` proves the following quantitative alternative.

### Theorem A: transverse floor amplification

If RH is false, then for every `0<=alpha<delta_*`, every `C>=0`, and every `N_0`, there is
`n>=N_0` such that

```text
eta((1/2)log n)>C n^alpha.                               (18)
```

Consequently

```text
limsup_(a->infinity) log(1+eta(a))/(2a)>=delta_*.        (19)
```

Under RH, `eta(a)=0` for every aperture. Therefore

```text
RH
 iff eta(a)=exp(o(a))
 iff limsup_(a->infinity)log(1+eta(a))/a=0.              (20)
```

Here `eta(a)=exp(o(a))` means that for every `epsilon>0` there are `C_epsilon,a_epsilon` such
that `eta(a)<=C_epsilon exp(epsilon*a)` for `a>=a_epsilon`.

#### Proof

If `(18)` failed, `(14)` would give an eventual lower bound
`Q_L(a_n)>=-2LC n^alpha`, contradicting `(17)`. This proves `(18)`. Taking logarithms along the
resulting cofinal samples gives `(19)`. If RH holds, Weil positivity makes every restricted floor
nonnegative and hence `eta=0`. If RH is false, `delta_*>0`, so `(19)` excludes subexponential
growth and excludes a zero logarithmic exponent. `QED`

## 5. Exact sampled floor-abscissa criterion

For a nonnegative nondecreasing sequence `b_n`, define

```text
beta(b)=limsup_(n->infinity)log(1+b_n)/log n.            (21)
```

If `b` is not eventually zero, dyadic blocking and the elementary upper comparison give

```text
sigma_abs(sum b_n n^(-s))=1+beta(b).                     (22)
```

Indeed, `b_n=O_epsilon(n^(beta+epsilon))` gives the upper bound. Conversely, convergence at a
real `sigma` and monotonicity give

```text
b_N sum_(N<=n<=2N)n^(-sigma)
 <=sum_n b_n n^(-sigma),
```

and the block on the left is bounded below by a positive constant times
`b_N N^(1-sigma)`. Thus `b_N=O(N^(sigma-1))`.

Apply this to `b_n=eta_L,N(n)`. Monotonicity follows from the nested restricted forms. Equations
`(18)`--`(22)` yield the exact endpoint theorem.

### Theorem B: Connes spectral-floor Dirichlet criterion

For every fixed `L>0` and every admissible logarithmic tail,

```text
RH
 iff sigma_abs(sum_(n>=1)eta_L,N(n)n^(-s))<=1.           (23)
```

More quantitatively, if RH is false, then

```text
sigma_abs(sum eta_L,N(n)n^(-s))>=1+delta_*.              (24)
```

Under RH the sequence is identically zero and the abscissa is `-infinity`.

This is strictly weaker as a target than a cofinal limit `lambda_0(a)->0`. The floor may be
estimated through a positive aggregate rather than pointwise evacuation. What makes the weaker
target complete is the transverse amplification law `(19)`: an off-line Xi divisor cannot produce
only a bounded persistent negative floor; it forces exponential negative mass along the sharp
cofinal detector.

## 6. Positive carrier statement for the Connes route

Every successful restricted-Weil or semilocal Connes realization is forced to carry a sampled
negative-floor channel whose critical Dirichlet cost is at most one. Equivalently, it must prove
subexponential growth of the actual negative floor. The source-to-floor bridge is explicit:

```text
finite prime--Gamma sharp source
 -> inward H01 regularization
 -> true restricted-Weil variational floor
 -> sampled negative-floor Dirichlet channel.            (25)
```

The first arrow preserves the sharp value in the closed-form limit and the second loses exactly
the fixed mass `2L`. Thus the finite prime--polar source criterion and the Connes spectral-floor
criterion are not merely adjacent RH equivalents: they are linked by the pointwise domination
`(14)`.

The remaining RH-bearing theorem is positive and source-specific:

```text
sigma_abs(sum eta((log n)/2)n^(-s))<=1,                  (26)
```

or any stronger source estimate implying subexponential growth of `eta(a)`.

## 7. Novelty and significance audit

### Parent material

- The existence and variational characterization of the restricted Weil operator are due to
  Connes--Consani--Moscovici and Suzuki.
- Domain monotonicity of the restricted floor is elementary.
- The sharp rectangular source spectrum is proved elsewhere in this project.
- Approximation by convolution and dominated convergence are standard.

### Candidate-new synthesis

The candidate-new theorem is the exact conjunction of these ingredients:

1. inward `H01` regularization of the nonsmooth sharp detector without aperture leakage;
2. lossless passage to the sharp value with limiting mass exactly `2L`;
3. pointwise domination of the sharp negative carrier by the true restricted spectral floor;
4. the transverse exponential lower law `(19)` for that floor; and
5. the single sampled spectral-floor abscissa criterion `(23)`.

Targeted searches through the current Connes--Consani--Moscovici, Suzuki, and finite
Guinand--Weil literature found restricted-floor criteria and finite spectral convergence
problems, but not this sharp-source-to-floor domination or the transverse exponential
amplification law.

### Significance

The theorem creates a direct operator consumer for the paper's strongest scalar invariant. It
also replaces the unnecessarily strong target `lambda_0(a)->0` by a critical positive aggregate
condition while remaining exactly RH-complete. This is a substantive strengthening of the main
paper narrative, but it does not estimate the floor and therefore does not prove RH.

## Lean decision

The scalar rectangular spectrum is already formalized. The missing internal certificate is the
inward-regularization limit and its variational consumer. It should be formalized before this
theorem is moved into the publication manuscript. The existing `TentMellinFactor.lean`,
`CCMRectangularTwoEdge.lean`, and dominated-tsum infrastructure contain the necessary analytic
building blocks; the restricted operator itself need not be reconstructed if the theorem is
stated through its variational lower-bound interface.

## Gates

- [x] sharp profile domain issue identified
- [x] inward aperture-preserving regularization constructed
- [x] transform and fixed-mass limits proved on paper
- [x] sharp trial-to-floor domination proved
- [x] transverse exponential floor amplification proved
- [x] sampled spectral-floor abscissa criterion proved
- [x] novelty/significance audit passed provisionally
- [ ] formalize the inward-regularization limit and variational consumer
- [ ] integrate the strengthened operator theorem into the publication manuscript
- [ ] prove the critical floor-abscissa estimate `(26)`
- [ ] RH
