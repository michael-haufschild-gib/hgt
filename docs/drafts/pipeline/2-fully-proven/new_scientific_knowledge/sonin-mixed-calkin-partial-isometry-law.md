# Mixed Sonin Calkin Gram entries are shell partial isometries

- **ID:** sonin-mixed-calkin-partial-isometry-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status banner:** `[NOVELTY UNVERIFIED]` The proof is complete. The result resolves the explicit
  multiplication-law conjecture in `sonin-two-scale-quadratic-corner-noncompact.md`; scientific
  priority remains subject to an independent audit of Sonin/prolate and Wiener--Hopf operator
  algebras.
- **Parents:** `sonin-euler-metric-corner-noncompact.md`,
  `sonin-two-scale-quadratic-corner-noncompact.md`

## Statement

Let `H=L^2(R)^ev`. For `t>0`, let `A_t` be multiplication by the indicator of `[-t,t]`, let
`R_t=F^*A_tF`, and let `Q_a` be the orthogonal projection onto

`ker(A_a) intersect ker(R_a)`.

For `r>1`, put

`L_r=(1-Q_a)(U_r+U_r^*)Q_a`,

where `(U_r f)(x)=sqrt(r)f(rx)`. Let `pi` be the Calkin quotient and write

`alpha_t=pi(A_t)`, `rho_t=pi(R_t)`.

For `0<s<t`, define the two-polarization shell projection

`Sigma(s,t)=(alpha_t-alpha_s)+(rho_t-rho_s)`.

For every `p,q>1`, set `m=min(p,q)` and

`G(p,q)=pi(L_p)^* pi(L_q)`.

Then `G(p,q)` is a partial isometry with exact initial and final projections

`G(p,q)^* G(p,q)=Sigma(a*q/m,a*q)`,

`G(p,q) G(p,q)^*=Sigma(a*p/m,a*p)`.                         (0)

Thus the mixed Gram entry transports a two-polarization shell of logarithmic thickness `log m`
from the `q` scale to the `p` scale. In particular,

`||G(p,q)||=1`.

When `p=q`, the Gram entry itself is the shell projection

`G(p,p)=Sigma(a,a*p)`.                                    (1)

When `p!=q`, its initial and final projections are different, so the mixed entry is a genuine
non-projection partial isometry.

## Proof

### 1. The Sonin projection has a Calkin complement formula

Every finite time--band block `A_s R_t` is compact. Hence

`alpha_s rho_t=0=rho_t alpha_s`                            (2)

for all finite positive `s,t`.

The strict prolate estimate gives `||R_a A_a R_a||<1`. Solving the two-projection correction by
the inverse of `1-R_aA_aR_a` shows that the projection onto
`range(A_a)+range(R_a)` differs from `A_a+R_a` by a compact operator. Therefore, with
`q_a=pi(Q_a)`,

`q_a=1-alpha_a-rho_a`.                                    (3)

### 2. The one-scale lower corner splits into two orthogonal polarizations

Write `u_r=pi(U_r)`. The exact support vanishings

`A_aU_r^*Q_a=0`, `R_aU_rQ_a=0`

and (3) give

`ell_r:=pi(L_r)=alpha_a u_r q_a+rho_a u_r^*q_a`.          (4)

The dilation covariance relations are

`u_r^*alpha_tu_r=alpha_(r*t)`,

`u_r rho_tu_r^*=rho_(r*t)`.                               (5)

All products between an `alpha` term and a `rho` term vanish by (2), including after dilation.

### 3. Formula for the mixed Gram entry

Put `delta=q/p`. Expanding (4), deleting the mixed polarizations with (2), and using (5) yields

`G(p,q)=q_a(alpha_(p*a)u_delta+rho_(p*a)u_(1/delta))q_a`. (6)

Let

`T_alpha=q_a alpha_(p*a)u_delta q_a`,

`T_rho=q_a rho_(p*a)u_(1/delta)q_a`.

The two summands and their initial and final spaces are orthogonal modulo compacts. Within the
physical polarization, (3) reduces `q_a` to `1-alpha_a`, so

`T_alpha=(alpha_(p*a)-alpha_a)u_delta(1-alpha_a)`.         (7)

Consequently

`T_alpha^*T_alpha
 =(1-alpha_a)(alpha_(q*a)-alpha_(q*a/p))(1-alpha_a)
 =alpha_(q*a)-alpha_(q*a/m)`,                              (8)

because compression by `1-alpha_a` replaces the lower endpoint `q*a/p` by
`max(a,q*a/p)=q*a/m`.

Similarly,

`T_alpha T_alpha^*
 =(alpha_(p*a)-alpha_a)(1-alpha_(p*a/q))(alpha_(p*a)-alpha_a)
 =alpha_(p*a)-alpha_(p*a/m)`.                              (9)

The Fourier polarization obeys the opposite dilation covariance, but the inverse dilation in
(6) reverses it again. The identical endpoint calculation gives

`T_rho^*T_rho=rho_(q*a)-rho_(q*a/m)`,                     (10)

`T_rho T_rho^*=rho_(p*a)-rho_(p*a/m)`.                    (11)

Adding the orthogonal physical and Fourier parts proves (0). Each right-hand side in (0) is a
nonzero projection because `m>1`; hence `G(p,q)` is a norm-one partial isometry.

### 4. Diagonal and off-diagonal cases

For `p=q`, equation (6) has `delta=1`. The two summands reduce directly to the physical and Fourier
shell projections, which proves (1).

For `p!=q`, the upper endpoints of the initial and final shells are respectively `a*q` and `a*p`.
Their difference is a nonzero time-shell projection, so the two projections in (0) cannot agree.

## Positive Euler metric source

On the concrete archimedean Hardy--Titchmarsh line, let

`C_r=(1-Pi_a)M_(w_r)Pi_a`,

where `w_r(s)=|1-r^(-1/2-is)|^2`. The exact source transport gives

`C_r` unitarily equivalent to `-r^(-1/2)L_r`.

Therefore the normalized mixed metric Gram entry

`sqrt(p*q) pi(C_p)^*pi(C_q)`

is unitarily equivalent to `G(p,q)` and has the same initial and final shell projections. The
unnormalized source entry has essential norm `(p*q)^(-1/2)`.

## Attack and exact scope

- `[PROVED]` The result is stronger than the exact mixed essential-norm theorem: it identifies both
  support projections and the precise shell transported by every ordered pair.
- `[PROVED]` The thickness depends on `min(p,q)`, not on `p*q` or `p/q`. The ratio `p/q` controls the
  displacement between initial and final shells.
- `[PROVED]` At `p=q` the Gram element is a projection; away from the diagonal it is a genuine
  partial isometry.
- `[PROVED]` The physical and Fourier summands are orthogonal only in the Calkin algebra. The
  finite time--band terms preventing exact orthogonality on `B(H)` are compact.
- `[PROVED]` This gives a constraint-side shell correspondence. It does not introduce a generator,
  infinitesimal scaling equation, or limiting flow.
- `[SEARCH]` Connes--Consani prove that an off-diagonal block of a triangular unitary associated to
  a quasi-inner phase ratio is a partial isometry. That theorem concerns a different Hardy
  decomposition and a unitary phase ratio; it does not give (0) for positive Euler metric corners.
- `[SEARCH]` Half-line translation and Wiener--Hopf algebras supply the parent model for the shell
  computation after logarithmic coordinates. The source-specific two-polarization identification
  and the endpoints in (0) were not located in the audited sources.
- `[OPEN CORE]` The higher multiplication law among three or more mixed Gram partial isometries is
  not determined here. Its overlap projections depend on three competing shell intervals and need
  not reduce to another single `G(p,q)`.

## Significance and novelty gate

- **SIGNIFICANT:** The result determines the full polar geometry of every entry of the Sonin Euler
  Calkin Gram matrix. It replaces the earlier scalar statement `||G(p,q)||=1` by an exact transport
  law and shows which shell survives every two-place metric interaction.
- **NOVELTY UNVERIFIED:** The calculation is source-specific but becomes elementary inside the
  Calkin time/frequency algebra once (3)--(5) are known. A broader Wiener--Hopf, Toeplitz--Hankel,
  and prolate operator-algebra audit is required before any priority claim. The defensible current
  statement is that the exact law was not found in the checked Sonin and semilocal primary sources.

## Lean target

The quotient can be avoided. Define compact congruence by

`S =_K T  iff  IsCompactOperator (S-T)`.

The formal target is to prove on the actual even Sonin carrier that

`G(p,q)^*G(p,q) =_K Sigma(a*q/m,a*q)`

and

`G(p,q)G(p,q)^* =_K Sigma(a*p/m,a*p)`.

The reusable exact two-projection resolvent formula and the compact congruence
`Q_a =_K 1-A_a-R_a` are now formalized in `SoninProjectionCalkin.lean`, including restriction to
the actual even carrier. The remaining target is the cutoff/dilation covariance and the two mixed
Gram compact-modulo products. No Calkin quotient or essential-norm API is required.

## Gates

- [x] 0 -> 1: exact mixed Calkin element and shell endpoints isolated
- [x] 1 -> 2: initial/final projection formulas proved on paper
- [ ] 2 -> 3: formalize both compact-modulo identities on the actual even Sonin carrier
- [ ] 3 -> 4: independent operator-algebra literature audit and standalone exposition
