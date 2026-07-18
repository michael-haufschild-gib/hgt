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
