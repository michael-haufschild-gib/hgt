# The finite-prime boundary layer converges to a zero-free symmetric Dickman law

- **ID:** `prime-boundary-symmetric-dickman-zero-free-law`
- **Stage:** 2-fully-proven / Lean finite core verified
- **Type:** THEOREM / INFINITELY DIVISIBLE PROBABILITY REFORMULATION
- **Scientific status:** `[PROVED; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `prime-superspace-wick-anisotropy-decompactification`; scale-invariant Poisson
  processes; separate from RHTower Routes A--D
- **Statement:** The universal `1/log N` prime-clock boundary layer is exactly a symmetric Dickman
  infinitely divisible field. Radial separation is its log moment-generating function and vertical
  clock separation is minus its log characteristic function. Both the finite and limiting
  characteristic functions are strictly positive, so the universal boundary layer cannot itself
  create zeta nodes.

## 1. Finite symmetric prime-jump field

For every prime `p<=N`, let

```text
K_p^+, K_p^- ~ Poisson(1/p)
```

be mutually independent. Put

```text
u_(p,N)=log p/log N,
X_N=sum_(p<=N) u_(p,N)(K_p^+-K_p^-).                  (1)
```

This is a symmetric infinitely divisible random variable with finite Lévy measure

```text
nu_N=sum_(p<=N) (1/p)(delta_(u_(p,N))+delta_(-u_(p,N))).   (2)
```

Although `nu_N(R)=2 sum_(p<=N)1/p` diverges with `N`, its quadratic mass remains finite and
converges:

```text
integral min(1,u^2) dnu_N(u)
  =2 sum_(p<=N)(log p/log N)^2/p
  ->1.                                                  (3)
```

## 2. Exact finite Wick--Lévy theorem

Let `R_N` and `V_N` be the radial and vertical prime-clock energies from the superspace theorem:

```text
R_N(r)=2 sum_(p<=N)(cosh(r log p)-1)/p,
V_N(h)=2 sum_(p<=N)(1-cos(h log p))/p.                 (4)
```

`[PROVED ON PAPER; FINITE ANALYTIC CORE PROVED IN LEAN]` For every real `c`,

```text
log E[exp(c X_N)] = R_N(c/log N),                      (5)

log E[exp(i c X_N)] = -V_N(c/log N).                  (6)
```

### Proof

For a Poisson random variable `K` of mean `lambda`,

```text
E exp(zK)=exp(lambda(exp(z)-1)).                       (7)
```

Independence and `(7)` give

```text
log E exp(c X_N)
  =sum_(p<=N)(exp(cu)-1+exp(-cu)-1)/p
  =2 sum_(p<=N)(cosh(cu)-1)/p,
```

which is `(5)`. Replacing `c` by `ic` gives

```text
log E exp(ic X_N)
  =2 sum_(p<=N)(cos(cu)-1)/p
  =-V_N(c/log N),
```

proving `(6)`. QED.

Equivalently, define the entire finite cumulant

```text
K_N(z)=2 sum_(p<=N)(cosh(z log p)-1)/p.                (8)
```

Then

```text
K_N(r)=R_N(r),
K_N(ih)=-V_N(h).                                      (9)
```

Lean proves `(8)`--`(9)` exactly, including the positivity and zero-freeness after exponentiation.

## 3. Scale-invariant Lévy limit

`[PROVED ON PAPER]` The positive halves of the Lévy measures satisfy

```text
sum_(p<=N)(1/p) delta_(log p/log N)
  -> 1_(0,1](u) du/u                                  (10)
```

vaguely on `(0,1]`.

### Proof

For `0<a<b<=1`, Euler--Mertens gives

```text
sum_(N^a<p<=N^b)1/p
  =log log(N^b)-log log(N^a)+o(1)
  =log(b/a)+o(1)
  =integral_a^b du/u+o(1).                             (11)
```

Interval convergence proves vague convergence away from zero. For Lévy test functions with
`f(u)=O(u^2)` at zero, the missing small interval is uniformly controlled by

```text
sum_(p<=N^delta)(log p/log N)^2/p=O(delta^2),          (12)
```

using the already proved susceptibility asymptotic. Letting `delta` tend to zero completes the
Lévy convergence. QED.

The symmetric limiting Lévy measure is therefore

```text
nu(du)=1_(0<|u|<=1) du/|u|.                            (13)
```

## 4. Symmetric Dickman limit

Let `D,D'` be independent Dickman subordinators at unit time, each with Lévy measure

```text
1_(0,1](u) du/u.
```

Then `X=D-D'` has the symmetric measure `(13)`. Its log moment-generating and characteristic
functions are

```text
log E exp(cX)
  =Phi_R(c)
  =2 integral_0^1 (cosh(cu)-1)/u du,                  (14)

log E exp(icX)
  =-Phi_T(c)
  =2 integral_0^1 (cos(cu)-1)/u du.                   (15)
```

Equations `(10)` and the Lévy continuity theorem, or directly convergence of `(6)`, prove

```text
X_N -> X in distribution.                             (16)
```

This identifies the two previously derived superspace profiles as two restrictions of one
infinitely divisible law.

The full cumulant tower is explicit:

```text
kappa_(2m)(X)=1/m,
kappa_(2m+1)(X)=0.                                    (17)
```

Indeed

```text
Phi_R(c)=sum_(m>=1)c^(2m)/(m(2m)!).                   (18)
```

Thus the boundary law is non-Gaussian but completely rigid at every order.

## 5. Zero-free theorem

`[PROVED ON PAPER; FINITE VERSION PROVED IN LEAN]` For every real `c`,

```text
phi_N(c)=E exp(icX_N)=exp(-V_N(c/log N))>0,            (19)

phi(c)=E exp(icX)=exp(-Phi_T(c))>0.                   (20)
```

Therefore neither the finite prime-jump field nor its universal thermodynamic limit possesses a
real characteristic node.

The squared coherent-state overlap in the critical window is exactly

```text
|<e(a_(N,t+c/log N)),e(a_(N,t))>|^2=phi_N(c).         (21)
```

So the positive prime boundary layer is not merely unlikely to generate a dark fringe: its
infinite divisibility forbids one structurally.

## 6. RH consequence

`[PROVED NO-GO]` No RH mechanism depending only on the universal prime-clock boundary law, its Lévy
measure, or its cumulants can recover the zeta divisor. Those data produce an exponential of a
finite Lévy exponent and hence a zero-free function.

The divisor must enter through data discarded by the universal limit. The remaining possibilities
are:

- the signed next-order fluctuation of the prime Lévy measure;
- the noncompact archimedean Gamma/theta weld;
- an amplitude-level object not representable by a positive infinitely divisible law; or
- a quantized invariant discontinuous under the Dickman limit but stable under the full completed
  source constraint.

This locates the missing information more sharply than saying only that Born probabilities are
phase-blind:

```text
leading scale-invariant prime field = symmetric Dickman = zero-free,
zeta nodes = completion-sensitive correction beyond that field.        (22)
```

## 7. Next mathematical object

The surviving residue is the renormalized signed Lévy defect

```text
Delta_N
  =sum_(p<=N)(1/p)
      (delta_(log p/log N)+delta_(-log p/log N))
   -1_(0<|u|<=1)du/|u|.                                (23)
```

Its unscaled vague limit is zero, but its first nonvanishing distributional normalization may
retain the explicit-formula zero spectrum. A viable next theorem must determine:

1. the correct normalization of `Delta_N`;
2. the topology in which a nonzero limit can exist;
3. whether the completed Gamma/theta correction cancels its deterministic boundary term; and
4. whether its remaining signed transform is zero-preserving for `Xi`.

This is not a flow. It is a fluctuation of the constraint carrier after the universal positive
phase has been factored out.

## 8. Parent and novelty boundary

Scale-invariant Poisson processes and Dickman approximation from normalized prime logarithms are
established parent theory. In particular, Bhattacharjee--Molchanov prove convergence to intensity
`c dt/t` and treat prime-logarithm examples; Arratia--Barbour--Tavare develop the scale-invariant
Poisson/Dickman framework. The symmetric difference and Wick interpretation are direct
specializations.

Therefore the result is a strong project bridge and no-go, not new scientific knowledge. The new
research question is the completed signed fluctuation `(23)`, not the leading Dickman law.

### Parent references

- C. Bhattacharjee and I. Molchanov, *Convergence to scale-invariant Poisson processes and
  applications in Dickman approximation*, <https://arxiv.org/abs/1911.06229>.
- R. Arratia, A. D. Barbour, and S. Tavare, *The Poisson--Dirichlet distribution and the
  scale-invariant Poisson process*, Combinatorics, Probability and Computing 8 (1999), 407--416.

## 9. Lean surface

`formal/GaloisForLFunctions/PrimeBoundaryDickmanWick.lean` proves:

- `primeClockCutoffEnergy_half_eq_cosh`;
- `primeBoundaryWickCumulant_ofReal`;
- `primeBoundaryWickCumulant_mul_I`;
- `primeBoundaryCharacteristic_eq_exp_neg_verticalEnergy`;
- `primeBoundaryCharacteristic_eq_ofReal_exp`;
- `primeBoundaryCharacteristic_re_pos`;
- `primeBoundaryCharacteristic_ne_zero`.

The finite entire-cumulant restriction and zero-free characteristic theorem are axiom-clean. The
probability-space construction and scale-invariant weak limit remain on paper because the current
formal tree has no downstream use for a full Lévy-process implementation.

## Gates

- [x] finite symmetric prime-jump field constructed
- [x] exact radial/characteristic Wick identities proved
- [x] scale-invariant Lévy convergence proved on paper
- [x] symmetric Dickman law identified
- [x] all cumulants computed
- [x] finite zero-free theorem formalized in Lean
- [x] limiting zero-free obstruction proved
- [x] parent theory audit completed; classified as bridge
- [ ] determine the first nonzero completed signed Lévy fluctuation

