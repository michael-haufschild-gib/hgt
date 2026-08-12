# Ramification-diagonal Boolean descent and Route-E Schur-response law

- **ID:** `cfr-ramification-boolean-route-e-response`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SOURCE-FIRST NON-MELLIN TARGET RESPONSE
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LITERAL PRE-ZERO SHELL] [FINITE APERTURE] [SOURCE-FIRST NON-MELLIN RESPONSE] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `ramification-diagonal-boolean-descent-route-e-schur-response-law-formalized.md`
- **Statement:** Pullback along `k->k^m` produces squarefree Boolean support and hard-core exclusion. Its rank and logarithmic clock admit a natural parity--energy Schur capacity; differentiating that chosen capacity gives an exact coefficient-intervention response.

## Goal

Start from the literal pre-zero high-exponent shell and a source-native operation. Construct a
non-Mellin support/capacity organ and derive its response. Only after those derivations compare the
capacity with Route E. This establishes a source-first cross-organ law; it does not certify the
stronger epistemic condition that the target response was withheld throughout discovery.

## 1. Ramification diagonal and Boolean support

Fix `m>=2` and let

\[
 a_m(n)=\mathbf1_{\max_pv_p(n)=m}\qquad(n\ge2).
\]

Unitalize it by `tilde a_m(1)=1` and `tilde a_m(n)=a_m(n)` for `n>=2`. Let

\[
 \operatorname{pow}_m(k)=k^m.
\tag{RB.1}
\]

### Theorem 1.1 — exact squarefree pullback

For every `k>=1`,

\[
 \boxed{\widetilde a_m(k^m)=\mu(k)^2.}
\tag{RB.2}
\]

### Proof

At `k=1`, both sides are one by unitalization. For `k>1`,

\[
 \max_pv_p(k^m)=m\max_pv_p(k).
\]

This equals `m` exactly when every nonzero prime exponent of `k` equals one, equivalently when `k`
is squarefree. The squarefree indicator is `mu(k)^2`. `[PROVED HERE]`

Fix a finite prime set `F`, put `P_F=prod_(p in F)p`, and let `B_F` be the divisor poset of
`P_F`. The map

\[
 \Phi_{m,F}:B_F\longrightarrow\mathbb N,
 \qquad k\longmapsto k^m
\tag{RB.3}
\]

is a bijection onto the unitalized perfect-`m`-power slice of the active shell supported on `F`.
The Boolean cover `k->kp`, for `p not_dvd k`, becomes

\[
 k^m\longrightarrow p^mk^m.
\tag{RB.4}
\]

Attempting to occupy `p` again produces prime exponent `2m`, where `a_m` vanishes. Thus the positive
shell selects Boolean support and hard-core exclusion. It does **not** select exterior signs. The
labeled integer supplies the canonical `Z/2` grading

\[
 (-1)^{N(k)}=(-1)^{\omega(k)}=\mu(k).
\tag{RB.5}
\]

because `k` is squarefree on this slice, but the positive value `mu(k)^2` itself has forgotten the
sign. If one additionally chooses a total order on `F`, the standard oriented Boolean boundary is

\[
 \partial e_S=\sum_{p\in S}
 (-1)^{|\{q\in S:q<p\}|}e_{S\setminus\{p\}}.
\tag{RB.5a}
\]

That orientation depends on the chosen order and is not reconstructed from `(RB.2)`. The support
law is a non-Mellin relation organ; a signed incidence law needs this extra ordered/oriented datum.

Let `L` be the coefficient logarithmic operator `(Lf)(n)=-(log n)f(n)`. On the active slice,

\[
 N(k)=\omega(k),
 \qquad
 E(k)=\log k=-{1\over m}(L\widetilde a_m)(k^m).
\tag{RB.6}
\]

Boolean support, rank, and logarithmic clock are therefore recovered before Route-E scalarization.
Signed incidence is not.

## 2. A natural chosen positive quotient capacity from source rank and clock

Fix real `sigma` and a finite `F` with at least two primes. Put

\[
 \mathbb P_{F,\sigma}(k)=Z_F^{-1}k^{-\sigma},
 \qquad k\mid P_F.
\tag{RB.7}
\]

Equivalently, this is the Gibbs weight `exp(-sigma E(k))` of the source clock `(RB.6)`. If it is
viewed inside the original shell measure, it is the finite perfect-power slice at shell exponent
`sigma/m`; no global normalization is asserted there.

Write `B_p(k)=1_(p divides k)`. Then the `B_p` are independent Bernoulli variables with

\[
 q_p={p^{-\sigma}\over1+p^{-\sigma}},
 \qquad
 w_p=q_p(1-q_p),
 \qquad
 \lambda_p=\log p.
\tag{RB.8}
\]

Set

\[
 N=\sum_{p\in F}B_p,
 \qquad
 E=\sum_{p\in F}\lambda_pB_p,
\]

and

\[
 A=\operatorname{Var}N=\sum_pw_p,
 \quad
 B=\operatorname{Cov}(N,E)=\sum_pw_p\lambda_p,
 \quad
 C=\operatorname{Var}E=\sum_pw_p\lambda_p^2.
\tag{RB.9}
\]

### Theorem 2.1 — exact Schur capacity and Plücker formula

The minimum parity-grade variance modulo the source clock is

\[
 D_F:=\inf_{t\in\mathbb R}\operatorname{Var}(\pi N-tE)
 =\pi^2\left(A-{B^2\over C}\right),
\tag{RB.10}
\]

and

\[
 \boxed{
 D_F
 =\pi^2
 {\displaystyle\sum_{p<q}w_pw_q(\log p-\log q)^2
  \over
  \displaystyle\sum_pw_p(\log p)^2}>0.}
\tag{RB.11}
\]

### Proof

Expanding the quadratic gives

\[
 \operatorname{Var}(\pi N-tE)=\pi^2A-2\pi tB+t^2C.
\]

Its unique minimizer is `t=pi B/C`, yielding `(RB.10)`. The covariance Gram is

\[
 G_F=\sum_{p\in F}w_p
 \begin{pmatrix}1\\\lambda_p\end{pmatrix}
 \begin{pmatrix}1&\lambda_p\end{pmatrix}
 =\begin{pmatrix}A&B\\B&C\end{pmatrix}.
\tag{RB.12}
\]

The two-row Cauchy--Binet identity gives

\[
 \det G_F=AC-B^2
 =\sum_{p<q}w_pw_q(\lambda_p-\lambda_q)^2.
\tag{RB.13}
\]

Since distinct primes have distinct logarithms and every `w_p` is positive, `(RB.11)` follows.
`[PROVED HERE]`

## 3. Exact coefficient-intervention response

Let a real shell intervention `h` induce the diagonal Boolean score

\[
 r_h(k)=h(k^m),\qquad k\mid P_F,
 \qquad r_h(1)=0.
\tag{RB.14}
\]

For sufficiently small `epsilon`, define

\[
 \mathbb P_\epsilon(k)
 ={k^{-\sigma}(1+\epsilon r_h(k))
  \over\sum_{d\mid P_F}d^{-\sigma}(1+\epsilon r_h(d))}.
\tag{RB.15}
\]

For every finite observable `f`, direct differentiation gives

\[
 {d\over d\epsilon}\bigg|_{0}\mathbb E_\epsilon f
 =\operatorname{Cov}(r_h,f).
\tag{RB.16}
\]

Let

\[
 A_\epsilon=\operatorname{Var}_\epsilon N,
 \quad B_\epsilon=\operatorname{Cov}_\epsilon(N,E),
 \quad C_\epsilon=\operatorname{Var}_\epsilon E,
\]

and define

\[
 D_F(\epsilon)
 =\pi^2\left(A_\epsilon-{B_\epsilon^2\over C_\epsilon}\right)
 =\inf_t\operatorname{Var}_\epsilon(\pi N-tE),
 \qquad
 D_F'[h]={d\over d\epsilon}\bigg|_0D_F(\epsilon).
\tag{RB.16a}
\]

For sufficiently small `epsilon`, all finite atom weights remain positive. Since `F` contains at
least two primes with distinct logarithms, `C_epsilon>0` there.

Put

\[
 \beta={B\over C},
 \qquad
 R=(N-\mathbb EN)-\beta(E-\mathbb EE).
\tag{RB.17}
\]

### Theorem 3.1 — exact intervention response of the descended Schur capacity

The derivative of the optimized capacity is

\[
 \boxed{
 D_F'[h]=\pi^2\operatorname{Cov}(r_h,R^2).}
\tag{RB.18}
\]

### Proof

For arbitrary observables `X,Y`, differentiation using `(RB.16)` gives

\[
 {d\over d\epsilon}\bigg|_0\operatorname{Cov}_\epsilon(X,Y)
 =\operatorname{Cov}
   \bigl(r_h,(X-\mathbb EX)(Y-\mathbb EY)\bigr).
\tag{RB.19}
\]

Differentiate `D_F/pi^2=A-B^2/C` and use `beta=B/C`:

\[
 {D_F'[h]\over\pi^2}=A'-2\beta B'+\beta^2C'
 =\operatorname{Cov}(r_h,R^2).
\]

`[PROVED HERE]`

### Corollary 3.2 — aperture-compatible prime-additive intervention and finite-aperture response

For scores `s_p in R`, let

\[
 r_s(k)=\sum_{p\mid k}s_p.
\tag{RB.20}
\]

This is a literal finite-support shell intervention: define

\[
 h_s(k^m)=\sum_{p\mid k}s_p\quad(k\mid P_F),
 \qquad h_s(1)=0,
\]

and extend `h_s` by zero off the finite ramification slice. Then `r_(h_s)=r_s`.

This is the tangent of the factorwise fugacity change
`p^-sigma -> p^-sigma exp(epsilon s_p)`. Then

\[
 \boxed{
 D_F'[s]=\pi^2\sum_{p\in F}
 w_p(1-2q_p)s_p(1-\beta\log p)^2.}
\tag{RB.21}
\]

### Proof

The fugacity change gives `q_p'=w_ps_p` and
`w_p'=w_p(1-2q_p)s_p`. Differentiate the three sums in `(RB.9)`:

\[
 {D_F'[s]\over\pi^2}
 =\sum_pw_p'(1-2\beta\lambda_p+\beta^2\lambda_p^2),
\]

which is `(RB.21)`. `[PROVED HERE]`

The score family in `(RB.20)` is compatible under restriction of prime apertures. The scalar
response itself is a finite-aperture quantity and is not restriction-compatible, because `beta`
changes with `F`.

Only now compare with the target corpus. For `F={p:p<=Y}` and `1/2<=sigma<1`, `(RB.10)` is exactly
the finite Route-E parity--energy Schur capacity `D_Y` in
`../../1-in-progress/route-e-physical-shell-conditioned-parity-energy-regression-law.md`,
equations `(1)`--`(5)`. The asymptotics and physical Gaussian shell conditioning from that card
were not used above. Formulas `(RB.18)`--`(RB.21)` are exact new consequences for this descended
capacity and are absent from that cited Route-E card. This document does not certify an
epistemically withheld derivation of the target response.

## 4. Conjecture / proof / fail loops

1. **Prime skeleton alone selects exterior statistics.** Failed: the same one-particle clock has
   symmetric and exterior second quantizations. **Survivor:** the full shell and power pullback
   prove repeated occupancy inactive. They still do not orient the Boolean boundary.
2. **Directly restrict the high shell to squarefree integers.** Failed: for `m>=2` those supports
   are disjoint. **Survivor:** pull back along `k->k^m` before restriction.
3. **Every shell intervention is aperture-natural.** Failed: arbitrary interacting Boolean scores
   need not be compatible with marginalization. **Survivor:** `(RB.18)` is exact at fixed finite
   aperture; prime-additive score data in `(RB.21)` are factorwise and aperture-compatible.
4. **Finite Boolean descent repairs global normalization.** Failed: for `sigma<=1`,
   `prod_p(1+p^-sigma)` diverges. **Survivor:** every finite aperture is exact; cofinal admission is
   a separate CFR coordinate.
5. **The same construction predicts Stokes inertia.** Failed: Boolean support supplies no
   Puiseux contact/conormal. The exact cluster-split card proves common Euler/Gamma twists leave the
   Stokes port gap and inertia fixed. A source ramification-to-contact functor remains absent.

## 5. Existing source collision and scope

The publication-ready oriented source already contains a distinct power-supported signed stream
`mPart_m(mu)` with coefficient `mu(k)` at `k^m`. That stream is required if an intrinsic Möbius sign
is wanted; the ordered exterior boundary still needs an ordering/orientation datum. The present
result is not a priority claim for squarefree power support. Its CFR role is the exact
source-to-Boolean support map, the chosen Schur-capacity construction, and the derived response
`(RB.18)`--`(RB.21)`.

This theorem reaches a finite Route-E relation/capacity organ. It does not construct Route-E Hall
allocation, directed seam flux, the physical conditioned determinant, cofinal normalization, a
Stokes contact law, or three-organ coherence. It has no RH consequence.

## Lean-return notes

- `(RB.2)` is a natural-number valuation/squarefree lemma.
- Finite Boolean product and Bernoulli moments have extensive existing Route-E support.
- `(RB.13)` is a two-row Cauchy--Binet identity.
- `(RB.18)` is finite covariance differentiation.
- No Lean file has been written or built.

## Gates

- [x] literal pre-zero source operation
- [x] non-Mellin Boolean support/hard-core organ
- [x] natural source-derived positive capacity chosen and computed
- [x] exact new response derived for descended capacity
- [ ] epistemically withheld Route-E prediction certified
- [x] exact hostile scope and Stokes failure
- [ ] cofinal normalization
- [ ] second nonisomorphic organ from the same law event
- [ ] Lean formalization

## Log

- 2026-08-09 — full-shell ramification diagonal replaced the flat prime skeleton and produced the first literal CFR non-Mellin transition.
