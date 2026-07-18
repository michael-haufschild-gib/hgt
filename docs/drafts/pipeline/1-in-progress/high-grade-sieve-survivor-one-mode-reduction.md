# High-grade sieve-survivor one-mode reduction

- **ID:** `high-grade-sieve-survivor-one-mode-reduction`
- **Stage:** `1-in-progress`
- **Type:** CANDIDATE THEOREM + SOURCE CONJECTURE
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` `(AC24)`--`(AC25)`,
  `common-profile-boolean-anchor-curvature.md` `(CG1)`--`(CG7)`, and
  `squarefree-shear-kernel-signed-tensor.md` `(SG1)`--`(SG10)`
- **Statement:** Above the squarefree cutoff, the globally joined Boolean response has exactly
  one positive sieve-survivor direction and a power-small negative background; the live question
  is whether the physical interval source has a genuinely smaller coefficient in that one
  direction.

## Goal

Replace the many-sector signed response in `(AC25)` by one explicit, source-canonical coefficient,
without taking sectorwise absolute values or assuming an RH-equivalent estimate.  The finite
spectral reduction is useful only if the physical interval source supplies an independent law for
that coefficient.

The bold source conjecture under attack is:

```text
[CONJECTURE HGS-SOURCE]
For P={p:p<=D}, D asymp sqrt(M), and the physical Hilbert packet
  g_m=(log(m)/m) P_0 1_((-log(m/M),c-log(m/M)] intersect (0,A)),
the high-grade sieve-survivor amplitude Y_>(M,D) defined below has
  ||Y_>(M,D)||^2 <<_(A,rho) log(M)^b/M.
```

This must be derived from the interval/logarithmic source.  Merely naming the left side, or proving
its equivalence to `(AC25)`, is not a provider.

## Finite spectral candidate

Let `P` be a finite prime set, `Q=product_(p in P)p`, and use the normalized Fourier space on
`Z/QZ`.  Locally put

```text
A_p=|e_0><e_0|,
w_p=(1-p e_0)/p,
B_p=|w_p><w_p|,
T_p=A_p-B_p,
Delta_p=p^(-2)diag(2p-1,-1,...,-1).
```

For `S subset P`, with `q_S=product_(p in S)p`, put

```text
R_S=tensor_(p in S)T_p tensor tensor_(p notin S)A_p,
E_S=tensor_(p in S)Delta_p tensor tensor_(p notin S)A_p,
C_S=R_S-E_S.
```

The joined cutoff and centered high tail are

```text
J_D=sum_(q_S<=D)(-1)^|S|E_S + sum_(q_S>D)(-1)^|S|R_S,
C_D=sum_(q_S>D)(-1)^|S|C_S.
```

Write `H_U` for the tensor grade with `e_0^perp` precisely on `U`, and

```text
H_>D=directSum_(q_U>D)H_U,
P_>D=orthogonal projection onto H_>D,
w_>D=P_>D tensor_p w_p,
V=product_(p in P)(1-1/p).
```

The paper candidate is

```text
P_>D J_D P_>D=|w_>D><w_>D|,                            (HGS1)

P_>D C_D P_>D
 =|w_>D><w_>D|-directSum_(q_U>D)V^2/phi(q_U)^2 I_(H_U). (HGS2)
```

Consequently, whenever the high space is nonzero and `D>=2`, `(HGS2)` has inertia

```text
(1, dim(H_>D)-1, 0),                                   (HGS3)
```

its unique positive eigenvalue `lambda_D` obeys

```text
m_D-2V^2/D <= lambda_D <= m_D,
m_D=||w_>D||^2
   =V Prob(product_(p:X_p=1)p>D),  X_p~Bernoulli(1/p), (HGS4)
```

and every negative eigenvalue lies in `[-2V^2/D,0)`.  Thus the transverse background is already
power-small, while the only large direction is the projected ordinary-prime/sieve-survivor
carrier.

## Physical-space coefficient and logarithmic jet

For a residue class `x`, define the centered Bernoulli coordinate

```text
Y_p(x)=(1-p 1_(p|x))/(p-1)
```

and its high multiplicative chaos tail

```text
psi_(D,P)(x)=sum_(U subset P,q_U>D) product_(p in U)Y_p(x). (HGS5)
```

Up to the fixed unitary sign and normalization,

```text
w_>D(x)=Q^(-1/2)V psi_(D,P)(x).                         (HGS6)
```

For a Hilbert-valued source packet `G(x)`, the sole positive high-grade amplitude is therefore

```text
Y_>(G)=V sum_(x mod Q)psi_(D,P)(x)G(x),                 (HGS7)
```

with the harmless Fourier normalization suppressed.  The exact physical normalization and its
join with the Euler vacuum are part of the current audit.

For each fixed nonempty `U`, absolute convergence for `Re(s)>1` gives

```text
sum_(n>=1) product_(p in U)Y_p(n)n^(-s)
 =zeta(s) product_(p in U)(1-p^(1-s))/(p-1).            (HGS8)
```

Hence a grade `|U|=r` has a zero of order `r-1` at `s=1`.  Since `P` contains only primes
`p<=D`, every grade in `(HGS5)` has `r>=2`; the first logarithmic jet at `s=1` sees exactly the
two-prime grades.  This suggests, but does not yet prove for the clipped physical window, that the
one surviving positive direction is a localized semiprime boundary law rather than an arbitrary
all-grade covariance.

## Gates

- [x] 0 -> 1: source-pure finite definitions and a falsifiable physical-source conjecture
- [ ] Independently verify `(HGS1)`--`(HGS8)` and all normalizations
- [ ] Identify the exact `(AC25)` scalar/Hilbert coupling, including the separate Euler vacuum
- [ ] Hostile test: show whether clipping creates full-size higher-grade endpoint terms
- [ ] External novelty audit against biased Boolean Fourier analysis, Kubilius models, and sieve
  remainder decompositions
- [ ] 1 -> 2: dependency-closed paper theorem with no RH-equivalent estimate assumed
- [ ] 2 -> 3: one batched Lean formalization and one targeted serialized verification

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending source-coupling audit.
- **Strongest positive survivor:** at minimum `(HGS1)`--`(HGS4)` plus the exact logarithmic
  grade-selection law `(HGS8)`, subject to independent verification and novelty classification.
- **New insight:** potentially, all power-scale failure is confined to one explicit roughness
  innovation whose completed logarithmic jet is purely two-prime.
- **Status:** paper audit in progress; no Lean process started; no novelty claim made.

## Log

- 2026-07-18 — created directly in Stage 1 from the live `(AC25)` frontier after the physical
  anchor-sign conjecture was falsified.  Lean intentionally deferred until the source theorem and
  novelty verdict close on paper.

## 2026-07-18 independent audit: exact semiprime jet and clipping no-go

`[PAPER-PROVED] [HOSTILE AUDIT COMPLETE] [SEMIPRIME-ONLY PHYSICAL CLAIM FALSIFIED]`
`[EXACT POSITIVE SURVIVOR] [AC25 STILL OPEN] [NOT NEW SCIENTIFIC KNOWLEDGE]`

The finite spectral statement and the completed Dirichlet jet are correct, but they must not be
conflated with the physically clipped source.  The completed first logarithmic jet is exactly
semiprime-supported.  A finite physical packet instead has an exact semiprime term **plus an
explicit higher-grade dilation remainder**, and that remainder is not structurally small.

For a nonempty prime set `U subset P`, put

```text
f_U(n)=product_(p in U)Y_p(n),
q_U=product_(p in U)p.
```

For every positive integer `n`, finite inclusion--exclusion gives

```text
f_U(n)
 =1/phi(q_U) sum_(d|q_U)mu(d)d 1_(d|n).                (HGS9)
```

Let `g=(g_n)` be any finitely supported packet in a real or complex vector space and define its
multiplicative dilation response by

```text
A_d(g)=d sum_(m>=1)g_(dm),
Delta_U A(g)=sum_(S subset U)(-1)^|S| A_(q_S)(g).
```

Then `(HGS9)` gives the exact grade evaluation

```text
sum_n f_U(n)g_n=Delta_U A(g)/phi(q_U).                 (HGS10)
```

Because every prime in `P` is at most `D`, the high region `q_U>D` contains no singleton.  Thus
its complete source evaluation is exactly

```text
sum_n psi_(D,P)(n)g_n
 =sum_(p<q in P,pq>D)
    [A_1(g)-A_p(g)-A_q(g)+A_(pq)(g)]/((p-1)(q-1))
  +R_(>=3)(g),                                         (HGS11)

R_(>=3)(g)
 =sum_(U subset P,q_U>D,|U|>=3)
    Delta_U A(g)/phi(q_U).
```

This is the sharp semiprime-band localization available before an analytic estimate: the first
line is an explicit two-prime multiplicative second difference, while the second line is the
complete clipping obstruction.  It is stronger than a covariance restatement because every
source value and every dilation entering the two-prime term is displayed.

For the actual interval packet

```text
g_n=(log(n)/n)k_n,
k_n=P_0 1_((log(M/n),log(K/n)] intersect (0,A)),
```

its dilation response is the explicit Hilbert vector

```text
A_d(g)=sum_(m>=1) log(dm)/m k_(dm).                    (HGS12)
```

Consequently the semiprime summand in `(HGS11)` is

```text
1/((p-1)(q-1)) sum_(m>=1)1/m
 [log(m)k_m-log(pm)k_(pm)-log(qm)k_(qm)
   +log(pqm)k_(pqm)].                                  (HGS13)
```

No hidden probability or covariance remains in `(HGS13)`; it is the literal two-prime endpoint
correlation which would have to be joined to the Euler vacuum in `(AC25)`.

### Completed first-jet theorem

For `Re(s)>1`, `(HGS9)` gives `(HGS8)`.  Writing `s=1+epsilon`, the simple pole of zeta and the
local expansions `1-p^(-epsilon)=epsilon log(p)+O(epsilon^2)` give

```text
F_U(1+epsilon)
 :=zeta(1+epsilon) product_(p in U)(1-p^(-epsilon))/(p-1)
 =product_(p in U)log(p)/phi(q_U) epsilon^(|U|-1)
   +O(epsilon^|U|).                                    (HGS14)
```

Therefore the analytically completed raw `log(n)/n` pairing of the entire high tail is exactly

```text
-d/ds|_(s=1) sum_(U subset P,q_U>D)F_U(s)
 =-sum_(p<q in P,pq>D)log(p)log(q)/((p-1)(q-1)).       (HGS15)
```

Every grade of size at least three vanishes in `(HGS15)`.  This is a theorem about the globally
completed Mellin jet.  Replacing that completion by the physical interval packet replaces the
affine logarithmic response by `(HGS12)`, and the higher finite differences in `R_(>=3)` need not
vanish.

### Exact physical grade-three obstruction

The failure occurs for the complete physical packet, not only for arbitrary test data.  Take

```text
M=3, K=4, c=log(4/3), A>=log(2), P={2,3,5}, D=5,
a=log(3)/3, b=log(2)/2.
```

As in the aperture phase-law theorem, the only nonzero atoms are

```text
g_2=b k_2,  g_3=a k_3,
I_3=(0,c], I_2=(log(3/2),log(2)].
```

The centered interval vectors `k_2,k_3` are linearly independent: their intervals are disjoint and
the complement of their union has positive length.  Direct evaluation of the biased prime
coordinates gives

```text
sum_n f_{ {2,3} }(n)g_n=-b/2 k_2-a k_3,

sum_n f_{ {2,3,5} }(n)g_n
 =-b/8 k_2-a/4 k_3
 =1/4 sum_n f_{ {2,3} }(n)g_n !=0.                    (HGS16)
```

Thus physical clipping can retain a grade-three packet at a fixed fraction of a grade-two packet.
Equation `(HGS16)` falsifies any exact or purely structural semiprime-only reduction for the
physical source.  It does **not** falsify a possible large-`M` estimate for `R_(>=3)`; it proves
that such an estimate would be new analytic input rather than Boolean algebra, Gram geometry, or
Mellin completion.

### Spectral standardness and exact secular equation

On a high ANOVA grade `H_U`, the diagonal term in `(HGS2)` and the squared grade mass of `w_>D`
are

```text
d_U=V^2/phi(q_U)^2,
m_U=||P_U w||^2=V^2/phi(q_U).                           (HGS17)
```

Hence `(HGS2)` is the standard rank-one perturbation

```text
|w_>D><w_>D|-directSum_U d_U I_(H_U).
```

Its positive eigenvalue is the unique positive solution of the secular equation

```text
1=sum_(q_U>D)m_U/(lambda_D+d_U),                       (HGS18)
```

and its positive eigenvector is proportional, grade by grade, to

```text
(lambda_D+d_U)^(-1)P_U w.                              (HGS19)
```

Since

```text
sum_(q_U>D)m_U/d_U=sum_(q_U>D)phi(q_U)>1,
```

there is exactly one positive eigenvalue and no zero eigenvalue; all remaining eigenvalues are
negative.  Weyl monotonicity gives

```text
m_D-max_(q_U>D)d_U<=lambda_D<=m_D.
```

For squarefree `q`,

```text
q/phi(q)^2=product_(p|q)p/(p-1)^2<=2,
```

so `max d_U<=2V^2/D`, proving `(HGS3)`--`(HGS4)`.  The same formulas restricted to
`|U|=2` give the exact semiprime-band compression and secular eigenvector.

### External novelty verdict

The verdict is unambiguous:

- `(HGS1)`--`(HGS4)` and `(HGS17)`--`(HGS19)` are a project-specific packaging of standard
  rank-one perturbation/interlacing/secular-equation mathematics; see Bunch--Nielsen--Sorensen,
  [Rank-One Modification of the Symmetric Eigenproblem](https://geodesic.mathdoc.fr/item/NUMA_1978__31_132565/).
- The product grades and the Bernoulli `1/p` prime model are standard biased Fourier/Hoeffding and
  Kubilius structures; see Hoeffding,
  [A Class of Statistics with Asymptotically Normal Distribution](https://www.jstor.org/stable/2235637),
  Efron--Stein,
  [The Jackknife Estimate of Variance](https://doi.org/10.1214/aos/1176345462),
  O'Donnell, [Analysis of Boolean Functions](https://arxiv.org/abs/2105.10386), and Kubilius,
  [Probabilistic Methods in the Theory of Numbers](https://doi.org/10.1090/mmono/011).
- The one-positive Hessian signature also occurs in the much richer Lorentzian-polynomial theory
  of Branden--Huh,
  [Lorentzian Polynomials](https://annals.math.princeton.edu/2020/192-3/p04), but that theorem is
  only adjacent: `(HGS2)` is a mixed-sign rank-one perturbation, not a Lorentzian Hessian.
- `(HGS14)`--`(HGS15)` are elementary finite-Euler-product zero counting at the zeta pole.  The
  exact semiprime selection is useful, but it is not new analytic number theory.
- `(HGS11)`--`(HGS16)` are a new project-local obstruction and exact source normal form.  They
  identify the missing estimate sharply, but remain elementary inclusion--exclusion and therefore
  are classified `POSITIVE SALVAGE / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE`, not an external
  scientific discovery.

### Consequence for AC25

There is currently no proved identity identifying the globally joined scalar/Hilbert source in
`(AC25)` with `Y_>(g)`.  Therefore even `(HGS11)` is, at present, a finite-model decomposition and
not an AC25 reduction.  To obtain a genuine two-prime reduction of `(AC25)`, two independent gates
remain:

```text
(1) prove the exact AC25-to-Y_> source and Euler-vacuum join;
(2) prove R_(>=3)(g)<<_(A,rho)log(M)^b/M
    for the actual physical packet, after that same global join.
```

Only after both gates would `(HGS13)` be the sole surviving two-prime correlation.  The completed
jet `(HGS15)` cannot replace gate `(2)`, because `(HGS16)` proves that clipping destroys its
higher-grade annihilation.

## Audit log continuation

- 2026-07-18 — independently verified the finite inertia and secular equation; external audit
  classifies them as standard rank-one/product-space mathematics.
- 2026-07-18 — proved the exact semiprime second-difference plus higher-grade clipping remainder
  `(HGS9)`--`(HGS13)`.
- 2026-07-18 — proved the completed semiprime first-jet law `(HGS14)`--`(HGS15)` and the complete
  physical grade-three fixed-ratio obstruction `(HGS16)`.
- 2026-07-18 — `HGS-SOURCE` remains open; no Lean process was started in this audit.

## All-order positive survivor: completed-jet Boolean bandwidth

`[PAPER-PROVED] [EXACT HIERARCHY] [FORMALISATION CANDIDATE] [REDISCOVERED ALGEBRA]`

The first-jet semiprime law is the `k=1` member of an exact all-order hierarchy.  Let `gamma_j`
denote the Stieltjes constants in the convention

```text
zeta(1+epsilon)
 =1/epsilon+sum_(j>=0)(-1)^j gamma_j epsilon^j/j!.
```

For the globally completed source `(log(n))^k/n`, its finite-part dilation response at scale `d`
is

```text
P_k(log d)
 :=FP_(epsilon=0)
    (-1)^k (d/d epsilon)^k [d^(-epsilon)zeta(1+epsilon)],

P_k(L)
 =-L^(k+1)/(k+1)
   +sum_(j=0)^k binom(k,j)gamma_j L^(k-j).              (HGS20)
```

In particular `P_k` has degree exactly `k+1` and universal leading coefficient `-1/(k+1)`.
For a prime grade `U`, the completed grade evaluation is

```text
J_(k,U)
 =1/phi(q_U) sum_(S subset U)(-1)^|S|
    P_k(sum_(p in S)log p).                            (HGS21)
```

Boolean finite-difference annihilation now gives the sharp bandwidth and boundary coefficient

```text
J_(k,U)=0                                      if |U|>=k+2,

J_(k,U)=(-1)^k k!/phi(q_U)
          product_(p in U)log p                if |U|=k+1.  (HGS22)
```

Indeed, all terms of degree at most `k` in `(HGS20)` vanish on a cube of dimension `k+1`, while

```text
sum_(S subset U)(-1)^|S|
  (sum_(p in S)log p)^(k+1)
 =(-1)^(k+1)(k+1)! product_(p in U)log p.
```

Thus the completed value jet `k=0` sees no high grade, the first logarithmic jet `k=1` sees
exactly semiprimes, the second jet sees at most triple-prime grades, and generally the `k`-th jet
has Boolean interaction bandwidth `k+1`.  Physical clipping replaces the polynomial `P_k(log d)`
by the non-polynomial endpoint response `A_d(g)` and the forbidden higher grades reappear as its
higher multiplicative finite differences.

This hierarchy is a useful new project-level insight and a clean later Lean target: the tree
already formalises polynomial Boolean annihilation in
`GaloisForLFunctions/HTGeometry/ProuhetAlternating.lean`.  It is nevertheless a direct Laurent
expansion plus Prouhet finite differences, so its external novelty verdict remains
`REDISCOVERED / NOT NEW SCIENTIFIC KNOWLEDGE`.
