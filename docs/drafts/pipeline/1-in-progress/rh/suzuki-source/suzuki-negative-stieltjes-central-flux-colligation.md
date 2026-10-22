# Suzuki shift-spectral-mass central-flux selector

- **ID:** suzuki-negative-stieltjes-central-flux-colligation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed algebraic theorem
- **Source:** `docs/handover/sota-suzuki.md` §34--35
- **Statement:** If the correctly normalized prime--Gamma triangle jet is a negative Stieltjes
  function of form shift, Suzuki's central Herglotz threshold is exactly a chord-weighted spectral
  mass gap; this supplies an intrinsic nonescaping shift selector.

## Goal

Discharge the first open implication in normalized Suzuki jump route:

```text
prime--Gamma shift-resolvent structure
  -> select alpha,beta with Phi_norm<=XiC''(0)/XiC(0)
  -> normalized jump Pick kernel
  -> no nonreal Xi zero
  -> RH.
```

Construction is non-circular only if shift-variable measure comes from restricted prime--Gamma
operator before exterior quotient is identified with Xi divisor.

## Gates

- [x] 0 → 1 in-progress: source-pure conjecture, exact attack identity, hostile tests
- [ ] 1 → 2 fully-proven: prove shift-variable Weyl law and one mass-gap selector
- [ ] 2 → 3 formalized: source representation plus current algebraic Lean connector
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, novelty audit

## Corpus correction that determines right conjecture

For fixed aperture, corpus already proves

```text
q_norm,lambda^EG -> ell_a
  :=(1/(2a)) integral_0^(2a) g(t)dt,       lambda->-infinity. (C0)
```

At sufficiently small aperture `ell_a` lies above fixed negative Xi curvature

```text
c_Xi=XiC''(0)/XiC(0)<0.                                (C1)
```

Therefore earlier trial `q=kappa+L lambda-integral...` with `kappa=c_Xi` is falsified: finite
limit forces `L=0` and constant `ell_a`, not `c_Xi`. This is exactly why far-negative dyadic pairs
fail. Any viable conjecture must reproduce `(C0)` and select shifts away from that escape cone.

## Representation-free asymmetric selector `[PROVED HERE]`

Keep one admissible shift `beta` fixed and send only other shift to `-infinity`. Exact affine
identity is

```text
Phi(-L,beta)
 =[beta q(-L)+L q(beta)]/(beta+L)
 =q(beta)+beta[q(-L)-q(beta)]/(beta+L).                 (A1)
```

Thus every finite edge limit `q(lambda)->ell_a` gives

```text
Phi(-L,beta)->q(beta),                  L->infinity.   (A2)
```

Consequently one strict one-source inequality

```text
q_norm,beta^EG<c_Xi                                   (A3)
```

produces, for all sufficiently large `L`, a genuine two-shift central flux below `c_Xi`.  This
does not use Stieltjes representation. It is exact positive survivor of Section 35: two escaping
shifts forget source, but one fixed and one escaping shift retains fixed source value.

Central shift-selection frontier is therefore no longer vague “find a good pair.” It is enough to
find one admissible fixed shift satisfying `(A3)`. Full jump positivity remains separate.

## Ground-edge source target

Use exact source quotient

```text
q_norm,lambda^EG=N_a(lambda)/D_a(lambda)               (A4)
```

from `(S1)` below. Suppose restricted operator has simple even ground state `phi_0` at
`lambda_a`, source overlap is nonzero, and `beta` approaches floor from below. Resolvent pole
dominance gives

```text
q_norm,beta^EG ->
 r_a:=<phi_0,h_a>/(2<phi_0,1+x>).                      (A5)
```

Evenness removes odd terms: `<phi_0,x>=0`, while
`-H_g(a-x)+H_g(a+x)` is odd and `g(a-x)+g(a+x)` is even. Hence

```text
r_a=<phi_0,g(a-x)>/<phi_0,1>.                          (A6)
```

If `phi_0` is positive, `(A6)` is literal ground-state-weighted screw average on `[0,2a]`.
Therefore following one-point source theorem is sufficient for central RH sign:

```text
exists aperture a with simple positive even ground state and
<phi_0,g(a-x)>/<phi_0,1> < c_Xi.                       (A7)
```

Choose `beta` close enough to floor to get `(A3)`, then use `(A2)`.  The successor theorem
`suzuki-ground-edge-aperture-robin-obstruction.md` now excludes **every sufficiently small
aperture** from `(A7)`: continuity, `g(0)=0`, and `c_Xi<0` put the whole sampled profile uniformly
above `c_Xi/2>c_Xi`.  This includes the only chamber where published theory proves a positive
simple ground.  Viable selector must use a non-small aperture and cannot rely on continuation of a
positivity-preserving semigroup, which corpus already disproves past an explicit threshold.

The same successor removes positivity from necessary formulation.  For any even eigenmode put

```text
U_a(x)=integral_(-a)^a g(x-y)phi_a(y)dy,
M_a=integral_(-a)^a phi_a(y)dy.
```

From `-U_a''=lambda_a phi_a` and evenness,

```text
-2U_a'(a)=lambda_a M_a,
r_a=U_a(a)/M_a=-lambda_a U_a(a)/(2U_a'(a)).             (A8)
```

Thus oriented `M_a>0` gives exact boundary target

```text
U_a(a)<c_Xi M_a.                                        (A9)
```

This `SUZUKI-ROBIN-CROSSING` conjecture is current representation-free ground-edge frontier.

## Structured sufficient conjecture `[SUZUKI-SHIFT-WEYL-MASS]`

For one source-selected aperture, normalized Euler--Gamma jet on real resolvent half-line
`lambda<lambda_a` has representation

```text
q_norm,lambda^EG
  =ell_a-integral 1/(t-lambda) dmu_a(t),                (C2)
```

where `mu_a>=0` is source-constructed shift-variable spectral measure. There exist distinct
admissible negative shifts `alpha,beta` for which

```text
integral K(t;alpha,beta)dmu_a(t) >= ell_a-c_Xi.         (C3)
```

Conjecture has two independently falsifiable halves: negative-Stieltjes orientation `(C2)` and
nonescaping mass selector `(C3)`. Neither is inferred from RH or Xi zeros.

This conjecture is now optional structure, not necessary for central selector: `(A7)` bypasses it.
Its value is to turn one-point selection into positive spectral mass geometry that may extend to
full jump Pick kernel.

## Dependency-closed paper theorem `[PROVED HERE]`

Define

```text
K(t;alpha,beta)
  =(t-alpha-beta)/((t-alpha)(t-beta)).                  (T1)
```

Direct common-denominator algebra gives

```text
[beta/(t-alpha)-alpha/(t-beta)]/(beta-alpha)
  =K(t;alpha,beta).                                    (T2)
```

If `beta<0`, `alpha<t`, and `beta<t`, denominator is positive and

```text
t-alpha-beta=(t-alpha)+(-beta)>0,
```

so `K>0`. For a finite positive colligation

```text
q(lambda)=ell+L lambda-sum_j w_j/(t_j-lambda),
w_j>=0,
```

affine sewing cancels `L lambda` exactly and `(T2)` gives

```text
Phi(alpha,beta)
 =ell-sum_j w_j K(t_j;alpha,beta).                     (T3)
```

Hence for arbitrary target `c`, not only for Xi,

```text
Phi(alpha,beta)<=c
 iff
ell-c <= sum_j w_j K(t_j;alpha,beta).                  (T4)
```

Taking `c=c_Xi` proves central Herglotz threshold exactly from `(C3)`. This is not another
curvature estimate: it identifies complete spectral quantity and exact amount which source
selector must retain. Direct Neumann channel is absent because it is affine and cancels in `(T3)`.

## Why large-negative no-go is now explained, not contradicted

For dyadic `alpha=-2L`, `beta=-L` and fixed `t`,

```text
K(t;-2L,-L)=(t+3L)/((t+2L)(t+L)) -> 0.                (T5)
```

Thus fixed spectral mass becomes invisible as `L->infinity`, and `(T3)` returns to `ell_a`,
exactly corpus theorem `(C0)`. Successful selector must keep chord mass above positive gap
`ell_a-c_Xi`; mere admissibility cannot do that.

## Exact source operator test

Writing compact source explicitly gives a quotient of restricted resolvent matrix elements

```text
q_norm,lambda^EG=N_a(lambda)/D_a(lambda),
N_a(lambda)=<R_lambda e^x,h_a>,
D_a(lambda)=2<R_lambda e^x,1+x>,
R_lambda=(A_a-lambda)^(-1),                            (S1)

h_a(x)=g(a-x)-H_g(a-x)+g(a+x)+H_g(a+x).               (S2)
```

Formula `(S2)` follows by pairing distribution
`i(v_+'-v_+ +v_-'+v_-)` with `H_g(a-y)`, integrating derivative by parts, and reflecting
`v_-(y)=v_+(-y)`. It reproduces endpoint-atom convention because derivative is taken after zero
extension.

Resolvent identity gives first sign test for `(C2)`:

```text
q'(lambda)
 =[<R_lambda^2 e^x,h_a>D_a(lambda)
   -N_a(lambda) 2<R_lambda^2 e^x,1+x>]/D_a(lambda)^2.  (S3)
```

Negative-Stieltjes law requires numerator in `(S3)` nonpositive and all higher shift derivatives
to have corresponding alternating signs. This cross-Wronskian, not Donoghue positivity in
spectral variable `z`, is current operator frontier. Existing finite Donoghue measure concerns
`-iW_1/W_-1`, has opposite divisor, and cannot discharge `(S3)`.

The corpus successor
`../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-shift-spectral-monotone-likelihood-transfer.md`
now proves a sharper positive mechanism for first sign. If spectral expansions factor as

```text
D(lambda)=sum_j p_j/(t_j-lambda),
N(lambda)=sum_j p_j r_j/(t_j-lambda),       p_j>=0,     (S4)
```

put `s_j=(t_j-lambda)^(-1)` and `a_j=p_j s_j`. Then exact weighted-covariance identity is

```text
2(N'D-ND')
 =sum_(i,j) a_i a_j (r_i-r_j)(s_i-s_j).                (S5)
```

Since `s_j` decreases with spectral node `t_j`, an increasing response profile `r_j` makes every
term in `(S5)` nonpositive and proves `q'<=0`. Conversely two-dimensional diagonal examples with
decreasing `r_j` reverse sign even when operator, resolvent, weights, and vectors are positive.
Thus abstract self-adjoint positivity cannot prove `(S3)`; required source theorem is actual
Suzuki coefficient law `(S4)` plus monotone prime--Gamma response. Exact measure-theoretic
cross-Wronskian core is already formalized in `SuzukiShiftSpectralMonotoneRatio.lean`. Direct
ground inequality `(A7)` bypasses this all-mode law for central selector, though not necessarily
for full jump kernel.

## Hostile tests / falsifiers

- **Large-negative edge:** representation constant must be exact `ell_a`; setting it to `c_Xi`
  contradicts proved escape law.
- **Orientation:** any `lambda` where cross-Wronskian `(S3)` is positive kills `(C2)`.
- **Support:** nodes at or left of selected shifts can reverse kernel sign.
- **Mass:** positivity alone is insufficient; exact gap `(C3)` must hold.
- **Asymmetric selector:** failure of `(A7)` at every aperture kills representation-free central
  repair even if some local derivative signs hold.
- **Small-aperture chamber:** `(A7)` is now proved impossible for every sufficiently small positive
  ground, including published simple-positive range.
- **Boundary cancellation:** if oriented even ground has `M_a=0`, denominator pole cancels and
  next noncancelled mode must replace ground pole.
- **Abstract positivity:** two-point diagonal model reverses `(S3)` by reversing spectral response;
  source monotonicity/alignment is essential.
- **Quadrature:** representation is for `q_norm=-i q_phys`, never mixed physical triangle.
- **Orbit insertion:** FE--Schwarz fake divisor must fail `(S1)--(S3)` or source mass law; otherwise
  construction is circular.
- **Global jump:** central threshold is necessary, not sufficient. Full two-variable jump Gram
  kernel remains next theorem.

## Formal status

Finite positive colligations, exact affine-intercept decomposition, strict kernel sign, exact mass
gap equivalence, asymmetric fixed/escaping selector, and connector to Suzuki one-sided
Weyl-normalized central flux are formalized in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanStieltjesFlux.lean`.

Open: prove source quotient `(S1)--(S2)` in concrete operator model, establish shift-variable
Weyl law `(C2)` or falsify it via `(S3)`, and prove non-small-aperture Robin crossing `(A9)`.
Either `(A9)` or Stieltjes mass gap `(C3)` supplies central selector.  Full jump Pick positivity
remains required after either central theorem.

## Log

- 2026-07-22 — Created after one-sided phase correction reopened scalar jump route.
- 2026-07-22 — Global `constant=c_Xi` trial killed by corpus large-negative theorem; survivor
  sharpened to exact spectral-mass selector `(T4)` compatible with escape law `(T5)`.
- 2026-07-22 — Derived source resolvent quotient and cross-Wronskian falsifier `(S1)--(S3)`.
- 2026-07-22 — Proved asymmetric selector `(A1)--(A3)` and reduced direct source target to
  ground-state screw average `(A7)`; connected existing monotone-likelihood successor theorem
  `(S4)--(S5)` rather than duplicating it.
- 2026-07-22 — Hostile audit killed `(A7)` throughout all sufficiently small positive-ground
  apertures.  Positive survivor compresses signed even source average to exact boundary Robin
  ratio `(A8)` and relocates conjecture to non-small-aperture boundary crossing `(A9)`.
- 2026-07-22 — Screw-Cesaro curvature recurrence superseded central ground selector by producing
  central-valid large-aperture dyadic pairs unconditionally.  Full-frequency successor is exact
  Loewner growth gap in `suzuki-jump-kernel-loewner-growth-gap.md`; central Stieltjes/Robin work is
  now optional structure, not active RH bottleneck.
