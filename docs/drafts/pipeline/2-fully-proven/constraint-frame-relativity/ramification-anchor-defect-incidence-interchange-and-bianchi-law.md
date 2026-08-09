# Ramification anchor--defect incidence interchange and Bianchi law

- **ID:** `cfr-ramification-anchor-defect-incidence`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / NONFUNCTORIAL SUPPORT-QUOTIENT DEFECT
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HOSTILE-AUDITED] [SOURCE-NATIVE INCIDENCE] [NONZERO INTERCHANGE DEFECT] [EXACT BIANCHI] [ORDERED-FLAG STRICTIFICATION] [NOT INTRINSIC CURVATURE] [NOT RH] [NO LEAN WRITTEN OR BUILT]`
- **Statement:** Direct composite ramification incidence and literal whole-number stagewise
  incidence differ exactly when outer and latent-inner prime defects coexist. The defect has closed
  norm and boundary formulas and obeys an exact Bianchi identity. Retaining ordered Kummer
  first-failure layers restores strict composition, so the defect is observer nonfunctoriality,
  not intrinsic source curvature.

## Goal

Find a non-Fourier observer of ramification excess and test whether it produces genuine
interchange curvature. Use only valuation roles fixed by the source law: primes attaining maximal
ramification are anchors, and primes failing divisibility are defects.

## 1. Colored anchor--defect incidence

Fix a finite prime aperture `F`, an integer shell height `M>=2`, and a divisor `q>=2` of `M`.
For `N in A_M(F)`, define

\[
 H_M(N)=\{p\in F:v_p(N)=M\},
 \qquad
 D_q(N)=\{p\in F:q\nmid v_p(N)\}.
\tag{AI.1}
\]

The anchor set is nonempty. It is disjoint from `D_q`, because `q|M`. Use colored copies
`F^an,F^def` and the oriented edge space with basis `[a^an,p^def]`. Put

\[
 \partial[a^{an},p^{def}]=p^{def}-a^{an}.
\tag{AI.2}
\]

If `D_q(N)` is empty, set `J_q^M(N)=0`. Otherwise define the normalized complete bipartite current

\[
 J_q^M(N)={1\over|H_M(N)||D_q(N)|}
 \sum_{a\in H_M(N)}\sum_{p\in D_q(N)}[a^{an},p^{def}].
\tag{AI.3}
\]

### Theorem 1.1 — incidence detects exactly the support complement

For `M=qm`,

\[
 \boxed{J_q^{qm}(N)=0\quad\Longleftrightarrow\quad N\in P_q(A_m(F)).}
\tag{AI.4}
\]

When nonzero, `J_q^(qm)(N)` has edge `ell^1` norm one, total oriented edge mass one, and

\[
 \partial J_q^{qm}(N)=u_{D_q(N)}-u_{H_{qm}(N)},
\tag{AI.5}
\]

where `u_S` is the uniform probability vector on the indicated colored vertex set.

### Proof

Inside `A_(qm)`, all valuations are divisible by `q` exactly when `N` is a `q`-th power; its root
then lies in `A_m`. This proves `(AI.4)`. The current has `|H||D|` positive coefficients each equal
to `1/(|H||D|)`, proving its norm and mass. Applying `(AI.2)` and summing gives `(AI.5)`.
`[PROVED HERE]`

Thus this incidence is a non-Fourier quotient of the full Kummer residue observer. It remembers
only zero versus nonzero residue and the source role anchor versus defect.

## 2. Direct and literal stagewise transport

Fix `m,r,s>=2`. For `N in A_(srm)(F)`, put

\[
 O_s(N)=D_s(N),
 \qquad
 L_{s,r}(N)=D_{sr}(N)\setminus D_s(N)
 =\{p:s\mid v_p(N),\ sr\nmid v_p(N)\}.
\tag{AI.6}
\]

These sets are disjoint and

\[
 D_{sr}(N)=O_s(N)\sqcup L_{s,r}(N).
\tag{AI.7}
\]

Literal transport `T_s` carries an inner current from `K in A_(rm)` to `N=K^s`; it is zero when
`N` is not a global `s`-th power. Define

\[
 J_{m,q}:=J_q^{qm}
\tag{AI.7a}
\]

as a current field on `A_(qm)(F)`, and set

\[
 \Omega_{m;s,r}
 =J_{m,sr}-J_{rm,s}-T_sJ_{m,r}.
\tag{AI.8}
\]

This is a field of edge currents on `A_(srm)(F)`.

### Theorem 2.1 — exact interchange defect

Let `a=|H_(srm)(N)|`, `d=|O_s(N)|`, and `ell=|L_(s,r)(N)|`.

- If `d=0`, then `N` is an `s`-th power and `T_sJ_r=J_(sr)`, so `Omega(N)=0`.
- If `ell=0`, then `J_(sr)=J_s`, so `Omega(N)=0`.
- If `d,ell>0`, literal inner transport is gated off and

\[
 \boxed{
 \Omega_{m;s,r}(N)
 ={\ell\over d+\ell}
 \left(J_{L_{s,r}(N)}-J_{O_s(N)}\right).}
\tag{AI.9}
\]

Here `J_L,J_O` use the same anchor set and the indicated defect set. Consequently

\[
 \boxed{
 \|\Omega(N)\|_1={2\ell\over d+\ell},
 \qquad
 \|\Omega(N)\|_2=\sqrt{\ell\over a d(d+\ell)},}
\tag{AI.10}
\]

and

\[
 \boxed{
 \|\Omega(N)\|_\infty
 ={1\over a(d+\ell)}\max\left(1,{\ell\over d}\right).}
\tag{AI.11}
\]

Net edge mass is zero; positive and negative masses both equal `ell/(d+ell)`. Moreover,

\[
 \boxed{
 \partial\Omega(N)
 ={\ell\over d+\ell}(u_{L_{s,r}(N)}-u_{O_s(N)}).}
\tag{AI.12}
\]

### Proof

If `d=0`, every valuation is divisible by `s`, so the unique `s`-th root exists and its
`r`-defect set is exactly `L_(s,r)(N)=D_(sr)(N)`. If `ell=0`, the direct and outer defect sets
coincide. If both are nonempty, `N` is not an `s`-th power, so literal transported inner current is
zero. Uniform incidence on the disjoint union satisfies

\[
 J_{O\sqcup L}={d\over d+\ell}J_O+{\ell\over d+\ell}J_L,
\]

which proves `(AI.9)`. The two edge supports are disjoint. Their uniform-current squared norms are
`1/(ad)` and `1/(a ell)`, giving `(AI.10)`; the coefficient formulas give `(AI.11)`. Both currents
have mass one and the same anchor marginal, proving zero net mass and `(AI.12)`.
`[PROVED HERE]`

### Corollary 2.2 — unconditional nonzero witness

For three distinct primes `p_0,p_1,p_2 in F`, take

\[
 N=p_0^{srm}p_1^sp_2.
\tag{AI.13}
\]

Then

\[
 H=\{p_0\},
 \qquad O_s=\{p_2\},
 \qquad L_{s,r}=\{p_1\},
\]

and

\[
 \boxed{
 \Omega(N)={1\over2}([p_0,p_1]-[p_0,p_2])\ne0.}
\tag{AI.14}
\]

Its `ell^1` norm is one, its `ell^2` norm is `1/sqrt 2`, and its boundary is
`(delta_(p_1)-delta_(p_2))/2`. `[PROVED HERE]`

## 3. Exact Bianchi identity

For a third factor `t>=2`, literal transports satisfy `T_tT_s=T_(ts)`.

### Theorem 3.1 — three-stage interchange Bianchi law

\[
 \boxed{
 \Omega_{m;t,sr}+T_t\Omega_{m;s,r}
 =\Omega_{m;ts,r}+\Omega_{rm;t,s}.}
\tag{AI.15}
\]

### Proof

Expanding either side by `(AI.8)` gives

\[
 J_{m,tsr}-J_{srm,t}-T_tJ_{rm,s}-T_{ts}J_{m,r}.
\]

The two expressions are identical. `[PROVED HERE]`

Thus the nonfunctorial observer defect is composition-coherent. This is the usual `delta^2J=0`
mechanism, now evaluated on one literal arithmetic law event.

## 4. Hostile strictification and Kummer correction

The direct residue support has the exact filtered decomposition `(AI.7)`. A correctly Kummer-
refined stagewise observer therefore retains both the outer layer `O_s` and latent inner layer
`L_(s,r)` even when no global `s`-th root exists. Its incidence is

\[
 H(N)\times O_s(N)\ \sqcup\ H(N)\times L_{s,r}(N)
 =H(N)\times D_{sr}(N),
\tag{AI.16}
\]

so refined direct and stagewise incidence agree exactly.

For a factorization `q_k...q_1`, retain the ordered first-failure layers

\[
 \begin{aligned}
 E_0&=\{p:q_k\nmid v_p(N)\},\\
 E_1&=\{p:q_k\mid v_p(N),\ q_kq_{k-1}\nmid v_p(N)\},\\
 &\ \vdots\\
 E_{k-1}&=\{p:q_k\cdots q_2\mid v_p(N),\ q_k\cdots q_1\nmid v_p(N)\}.
 \end{aligned}
\tag{AI.17}
\]

They are disjoint and their union is the full product-defect set. Ordered defect flags compose
strictly by refinement and concatenation. The defect `Omega` is exactly the information lost when
this flag is replaced by literal whole-number gating plus flattened support.

There is a still deeper distinction. The residue extension

\[
 0\to\mathbb Z/r\to\mathbb Z/(sr)\to\mathbb Z/s\to0
\]

has a genuine carry class when `gcd(r,s)>1`, as proved in the Kummer-phase card. Support incidence
does not retain that class; it remembers only zero versus nonzero residue.

## 5. CFR consequence

This is the first explicit nonzero interchange defect in the ramification pilot, and it obeys an
exact Bianchi identity. It still does **not** count as intrinsic CFR field strength:

- `Omega=delta J` is an observer coboundary;
- ordered Kummer failure flags restore strict composition;
- the result depends on the literal whole-number transport gate and the chosen support quotient;
- no presentation/Morita invariance or second physical observer is proved.

Its correct status is a **nonfunctorial support-quotient calibration**. It predicts exactly when a
coarse incidence route creates apparent curvature from a flat source: outer and latent-inner
failure layers must coexist. This is a route-independent mechanism, but no identity with Route E,
Stokes, Mass boundary flux, or physical flux is asserted.

## 6. Conjecture / proof / fail loops

1. **Incidence composes strictly.** Failed for literal whole-number transport by `(AI.14)`.
   **Survivor:** exact interchange tensor `(AI.9)`.
2. **The defect is nonzero whenever direct excess is nonzero.** Failed. **Survivor:** it is nonzero
   exactly when outer and latent-inner prime layers coexist.
3. **Normalization alone creates the defect.** Failed: literal gating already loses latent support
   before normalization. **Survivor:** normalization turns support loss into a signed zero-mass
   redistribution with closed norms.
4. **The defect is intrinsic source curvature.** Failed: ordered Kummer flags strictify it and
   `Omega` is a coboundary. **Survivor:** it calibrates observer nonfunctoriality.
5. **Failure destroys coherence.** Failed by `(AI.15)`. **Survivor:** exact Bianchi identity.

## 7. Scope and boundaries

- Finite `F` makes every shell and edge space finite. No cofinal completion is used.
- Factors `m,r,s,t>=2` are load-bearing for the nonzero witness; the algebra extends to trivial
  factors with zero layers.
- Prime labels are not ordered. The two colors are source roles, not a chosen orientation order.
- The currents are finite combinatorial chains. “Flux” does not mean physical flux.
- No Dirichlet continuation, HT theorem, Stokes contact, Route-E equality, physical action, Xi
  condition, or RH result is asserted.
- No Lean file has been written or built.

## Lean-return notes

- Formalize the defect-set partition and atomwise current before norm formulas.
- Reuse generic clock-shadow/Bianchi parents for `(AI.15)` only after the literal instantiation is
  paper-audited.
- No Lean file has been written or built.

## Gates

- [x] source-native non-Fourier incidence observer
- [x] exact nonzero interchange defect and witness
- [x] closed norm and boundary formulas
- [x] exact Bianchi identity
- [x] ordered-flag strictification
- [x] hostile rejection as intrinsic curvature
- [ ] presentation-invariant curvature class
- [ ] non-Fourier observer carrying the Kummer extension class
- [ ] Route-E/Stokes/physical flux comparison
- [ ] Lean formalization

## Log

- 2026-08-09 — constructed after Kummer excess detection; hostile dual audit separated literal
  whole-number transport defect from correctly refined flat Kummer incidence.
