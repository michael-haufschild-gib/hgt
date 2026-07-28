# Adelic m-free shell Fourier rank-one fracture

- **ID:** `adelic-mfree-shell-fourier-rank-one-fracture`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / `[SOURCE UNITARIZATION NO-GO WITH POSITIVE SURVIVOR]`
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW STRUCTURAL KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../3-formalized/high-exponent-shell-zero-free-common-divisor-law.md`;
  - `high-shell-critical-hardy-conormal-uniformization.md`;
  - `../3-formalized/not_new_scientific_knowledge/field-one-finite-adele-integral-bruhat-test.md`;
  - `../3-formalized/not_new_scientific_knowledge/field-one-finite-bruhat-l2-density.md`.
- **Statement:** The positive high-shell residue weights are exact finite-adele Haar shell
  masses. Additive Fourier transform produces an isometric reflected shell frame, but the
  incoming/outgoing cross-Gram is exactly rank one and carries only the Euler-pole residue
  direction. Every transverse high-shell direction is orthogonal to the reflected frame.

## Goal

The high-shell common-divisor theorem gives positive disjoint sources

```text
S_m(s)=zeta(s)H_m(s),
H_m(s)=1/zeta((m+1)s)-1/zeta(ms),                       (1)
```

and the critical Hardy card gives their canonical residue weights

```text
w_m=H_m(1)=1/zeta(m+1)-1/zeta(m).                       (2)
```

The exact RH-facing open core is a source-defined positive reflection unitarization of the
common-zero normal sequence `(H_m(rho))_m`. This card tests the most canonical candidate:
additive Fourier transform on the rational finite adeles.

The result is not a construction of the missing unitarization. It proves that bare adelic
Fourier transform sees only the one-dimensional pole mode and annihilates all incoming/outgoing
transverse incidence. Consequently a successful source graph must couple finite and
archimedean/Gamma channels before scalar tensor separation.

## Setup

Normalize additive Haar measure on

```text
Zhat=product_p Z_p
```

to have mass one, and choose the standard additive character for which

```text
Fourier(1_(Z_p))=1_(Z_p).                                (3)
```

For every integer `m>=2`, define the finite-adele m-free set

```text
E_m={x in Zhat : x_p notin p^m Z_p for every prime p}.   (4)
```

The sets are nested, `E_m subset E_(m+1)`. Put

```text
A_m=E_(m+1)\E_m,
e_m=1_(E_m),
a_m=1_(A_m)=e_(m+1)-e_m.                                (5)
```

For a finite prime packet `P`, let

```text
E_(m,P)
 ={x in Zhat : x_p notin p^m Z_p for p in P}.           (6)
```

Then `1_(E_(m,P))` is a compact-open finite-adele Bruhat--Schwartz function and these
indicators decrease pointwise to `e_m` as `P` exhausts the primes.

## Theorem A: exact adelic realization of the shell weights

For every `m>=2`,

```text
mu(E_m)=product_p (1-p^(-m))=1/zeta(m),                 (7)

mu(A_m)=1/zeta(m+1)-1/zeta(m)=w_m.                      (8)
```

The shell vectors are pairwise orthogonal and

```text
<a_m,a_k>=delta_(m,k) w_m.                              (9)
```

Moreover,

```text
1_(E_(m,P)) -> e_m in L2(A_f)                           (10)
```

cofinally over finite prime packets.

### Proof

At one prime, normalized Haar measure gives

```text
mu_p(Z_p\p^m Z_p)=1-p^(-m).                             (11)
```

For `m>1`, the Euler product converges absolutely, proving `(7)`. Nestedness gives `(8)`,
and the `A_m` are disjoint, proving `(9)`.

The squared `L2` distance in `(10)` is

```text
mu(E_(m,P))-mu(E_m)
 =product_(p in P)(1-p^(-m))-1/zeta(m),                 (12)
```

which tends to zero.

On a diagonally embedded nonzero rational, membership in `E_m` means precisely that the rational
is an integer and every prime valuation is less than `m`. Thus diagonal sampling of `e_m`
is the ordinary m-free indicator, and sampling `a_m` is the largest-prime-exponent shell
indicator from `(1)`.

## Theorem B: exact local Fourier law and cofinal reflected frame

At one prime,

```text
Fourier(1_(Z_p\p^m Z_p))
 =1_(Z_p)-p^(-m)1_(p^(-m)Z_p).                          (13)
```

Let `F` be the additive `L2` Fourier transform on the finite adeles, and define

```text
b_m=F(a_m).                                             (14)
```

Then `(b_m)` is another pairwise orthogonal shell frame with the same weights:

```text
<b_m,b_k>=delta_(m,k) w_m.                              (15)
```

### Proof

Self-dual normalization gives

```text
Fourier(1_(p^m Z_p))=p^(-m)1_(p^(-m)Z_p),               (16)
```

so subtraction proves `(13)`. Equation `(10)` and unitarity of `F` define the cofinal
Fourier images without treating the infinite Euler product as a Bruhat--Schwartz function.
Unitarity and `(9)` give `(15)`.

## Theorem C: incoming/outgoing cross-Gram is exactly rank one

For all `m,k>=2`,

```text
<e_m,F(e_k)>=1/[zeta(m)zeta(k)],                         (17)

<a_m,b_k>=w_m w_k.                                      (18)
```

Fix `M>=2` and normalize the frames by

```text
u_m=a_m/sqrt(w_m),
v_m=b_m/sqrt(w_m),              m>=M.                   (19)
```

Their cross-Gram is

```text
<u_m,v_k>=sqrt(w_m)sqrt(w_k).                            (20)
```

It has rank one and unique nonzero singular value

```text
W_M=sum_(m>=M)w_m=1-1/zeta(M)<1.                        (21)
```

If

```text
r_M=(sqrt(w_m))_(m>=M),
```

then every coefficient vector `c` with `<c,r_M>=0` satisfies

```text
<sum_m c_m u_m, v_k>=0 for every k>=M.                  (22)
```

Thus the whole transverse incoming shell space is orthogonal to the reflected shell space.

### Proof

First replace `e_k` by the finite-packet approximation `1_(E_(k,P))`. At a prime in `P`,
equation `(13)` is constant with value `1-p^(-k)` on
`Z_p\p^m Z_p`. At a prime outside `P`, the Fourier factor is `1_(Z_p)`. Therefore

```text
<e_m,F(1_(E_(k,P)))>
 =[product_p(1-p^(-m))] [product_(p in P)(1-p^(-k))].   (23)
```

Pass to the `L2` limit to obtain `(17)`. Taking the mixed finite difference

```text
(m+1-m)(k+1-k)
```

of the factorized right side gives `(18)`. Equations `(20)`--`(22)` are the rank-one
operator `r_M r_M^*`, and the telescope in `(21)` is exact.

## Tate--Mellin and common-divisor interface

For a finite prime packet `P`, tensor the finite-adele indicator with the standard
self-dual real Gaussian. Its Tate zeta integral is

```text
Gamma_R(s) zeta(s) product_(p in P)(1-p^(-ms)).         (24)
```

On `Re(s)>1`, the cofinal limit is

```text
Gamma_R(s) zeta(s)/zeta(ms).                            (25)
```

and the shell difference is

```text
Gamma_R(s) zeta(s)H_m(s).                               (26)
```

The right side supplies its meromorphic continuation. For `m>=12`, the existing shell theorem
proves that `H_m` is a unit on `Re(s)>1/2`. Hence at a nontrivial zeta zero `rho` of order `d`,
the first nonzero normal shell jet is

```text
[Gamma_R zeta H_m]^(d)(rho)
 =[Gamma_R zeta]^(d)(rho) H_m(rho).                     (27)
```

Thus `(a_m)` is not an auxiliary adelic family: its Tate--Mellin normal is exactly the
positive hypertranscendental common-divisor frame.

## No-go closure

- **Exact killing theorem/mechanism:** Equations `(18)`--`(22)` show that additive finite-adele
  Fourier transform couples the incoming and outgoing high-shell frames only through the
  one-dimensional residue vector `r_M`. Every shell-label direction orthogonal to the Euler-pole
  residue is exactly orthogonal to the entire reflected frame. Bare Fourier self-duality
  therefore cannot provide the positive Riesz identification of the transverse common-zero
  normals required by `high-shell-critical-hardy-conormal-uniformization.md`.
- **Strongest positive survivor:** The critical weights `w_m` are exact Haar masses of canonical
  finite-adele valuation shells, not merely prime-two asymptotics. Their additive Fourier images
  form an exact isometric reflected shell frame. The complete incoming/outgoing principal-angle
  operator is explicitly the rank-one contraction `r_M r_M^*`, with singular value
  `1-1/zeta(M)`.
- **New insight:** The pole/transverse split is geometric before analytic continuation.
  Finite-adele Fourier transform transports exactly the common Euler-pole mode and leaves all
  relative-HT shell directions mutually orthogonal. Tensoring with one fixed self-dual
  archimedean vector only multiplies `(18)` by a scalar and cannot change its rank. A viable
  RH source must therefore use a genuinely non-product prime--Gamma incidence, relative trace,
  or multiplicative-scattering graph that creates transverse cross-channel coupling before the
  fixed-current quotient.
- **Status:** Paper proof dependency-closed modulo standard finite-adele Fourier normalization.
  Internal exact/concept search found no shell-adelic realization or rank-one cross-Gram theorem.
  Initial literature search found the parent Tate local transform and the classical m-free Euler
  density, but no source combining them with largest-exponent shell residues, the common zeta
  divisor, or the rank-one fracture. External specialist novelty audit remains open. No Lean
  formalization is authorized before that audit.

## RH impact and exact next theorem

The zero-sensitive endpoint remains:

```text
Xi(rho)=0
 + source-positive identification of incoming and reflected transverse shell normals
 -> Re(rho)=1/2.                                        (28)
```

This card proves that neither finite-adele Fourier unitarity nor a separable tensor Gamma factor
can supply the second premise. The next admissible theorem must construct a coupled
prime--archimedean transform `U_cpl` whose cross-Gram on the shell frame has a nonzero transverse
part and whose Mellin action is the completed functional equation. It must be defined before a
zero is selected.

The first hostile test for any candidate `U_cpl` is exact:

```text
P_(r_M perp) [<a_m,U_cpl a_k>] P_(r_M perp) != 0.       (29)
```

If `(29)` fails, the candidate is another pole-only Fourier realization and cannot orient a
common zeta zero.

## Gates

- [x] 0 -> 1: source-pure finite-adele shell object and exact attack identified
- [x] Haar shell masses and orthogonality proved on paper
- [x] cofinal `L2` construction and local Fourier formula proved on paper
- [x] exact rank-one cross-Gram and transverse orthogonality proved on paper
- [x] Tate--Mellin identification with the positive HT divisor frame proved on paper
- [x] no-go closed with a nontrivial positive survivor and exact successor test
- [ ] independent specialist audit of infinite-product measurability and Fourier normalization
- [ ] exhaustive primary-literature novelty audit
- [ ] construct a source-defined non-product prime--Gamma transform satisfying `(29)`
- [ ] prove positive reflected conormal unitarization
- [ ] derive `Re(rho)=1/2` from every `Xi(rho)=0`
- [ ] formalize only after novelty and significance gates pass
- [ ] RH

## Log

- 2026-07-28 — Identified m-free finite-adele Haar sets, proved that their shell masses are the
  exact high-shell residue weights, and computed the full incoming/Fourier cross-Gram. The hoped
  bare Fourier unitarization fractures to rank one; the exact survivor is the adelic shell frame
  plus a transverse-coupling test for every future prime--Gamma completion.
