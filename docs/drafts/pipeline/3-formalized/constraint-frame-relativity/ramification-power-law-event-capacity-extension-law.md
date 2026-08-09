# Ramification-power law event, capacity response, and analytic excess law

- **ID:** `cfr-ramification-power-law-event`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / FIRST TWO-ORGAN SOURCE-LAW EVENT
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-NATIVE POWER MORPHISM] [TWO DISTINCT OBSERVER ORGANS] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `ramification-power-law-event-capacity-extension-law-formalized.md`
- **Statement:** The arithmetic power endomorphism `P_r(k)=k^r` is a genuine morphism from shell law `m` to shell law `rm`; it produces both a nonzero full-shell analytic excess and, at fixed observer temperature and aperture, a strictly changed Boolean Schur capacity for sufficiently large `r`.

## Goal

Pass the first nontrivial CFR law-formation test without returning to an RH endpoint. Use one
source-native morphism, defined before either target observer, and prove consequences in two
mathematically different organs:

1. a positive finite Boolean-capacity organ;
2. an additive Dirichlet/HT extension organ.

The result must distinguish observer indexing from observer values. Coefficient doctrine, aperture,
temperature, prolongation doctrine, and trivial history are held fixed; the shell support law
changes under an actual monoid endomorphism.

## 1. Source shell laws and the power morphism

For `m>=2`, define

\[
 a_m(1)=0,
 \qquad
 a_m(n)=\mathbf 1_{\max_p v_p(n)=m}\quad(n\ge2),
\tag{RP.1}
\]

For the finite Boolean observer only, adjoin the multiplicative unit by

\[
 \widetilde a_m=a_m+\mathbf1_{\{1\}}.
\tag{RP.1a}
\]

and let

\[
 S_m(s)=\sum_{n\ge1}a_m(n)n^{-s},
 \qquad \Re s>1.
\tag{RP.2}
\]

For an integer `r>=2`, let `P_r:N_{>=1}->N_{>=1}` be the multiplicative monoid endomorphism

\[
 P_r(k)=k^r.
\tag{RP.3}
\]

### Theorem 1.1 — exact ramification-law pullback

For every `k>=1`,

\[
 \boxed{a_{rm}(P_r(k))=a_m(k),
 \qquad
 \widetilde a_{rm}(P_r(k))=\widetilde a_m(k).}
\tag{RP.4}
\]

Let `ShellLaw` have as objects streams `a_l:N_(>=1)->{0,1}`. A morphism `a_u->a_v` is a
multiplicative monoid endomorphism `f:N_(>=1)->N_(>=1)` satisfying `a_u=a_v after f`. Identities
and composition are inherited from monoid endomorphisms. Thus `(RP.4)` defines a nonidentity
morphism `P_r:a_m->a_(rm)`.

### Proof

At `k=1`, the first pair is zero and the unitalized pair is one. For `k>=2`,

\[
 \max_p v_p(k^r)=r\max_p v_p(k).
\]

This equals `rm` exactly when `max_p v_p(k)=m`. This is `(RP.4)`. Multiplicativity and
`P_r(1)=1` are immediate. `[PROVED HERE]`

The morphism is source-native: it is the ordinary power endomorphism of the free commutative prime
monoid. Neither a capacity nor a Mellin transform enters its definition.

The source category is non-vacuous and composition is literal: `P_1=id`,
`P_s after P_r=P_(sr)`, and the shell levels compose as `m->rm->srm`. Equation `(RP.4)` is stable
under this composition.

## 2. Pushforward sublaw and nonzero analytic excess

Define the power-image stream

\[
 b_{m,r}(N)=
 \begin{cases}
  a_m(k),&N=k^r\text{ for some }k,\\
  0,&N\text{ is not an }r\text{-th power}.
 \end{cases}
\tag{RP.5}
\]

The root `k` is unique when it exists. Put

\[
 c_{m,r}=a_{rm}-b_{m,r}.
\tag{RP.6}
\]

### Theorem 2.1 — positive affine excess

The stream `c_(m,r)` takes values in `{0,1}`, is nonzero, and for `Re s>1` one has the exact
absolutely convergent decomposition

\[
 \boxed{
 S_{rm}(s)=S_m(rs)+C_{m,r}(s),
 \qquad
 C_{m,r}(s)=\sum_{N\ge1}c_{m,r}(N)N^{-s}.}
\tag{RP.7}
\]

### Proof

If `b_(m,r)(N)=1`, then `N=k^r` with `a_m(k)=1`. The proof of `(RP.4)` gives
`a_(rm)(N)=1`. Hence `0<=b_(m,r)<=a_(rm)` coefficientwise and `c_(m,r)` is `{0,1}`-valued.

It is nonzero: for

\[
 N_0=2^{rm}3,
\]

one has `a_(rm)(N_0)=1`, while `N_0` is not an `r`-th power because `v_3(N_0)=1`. Thus
`c_(m,r)(N_0)=1`.

For `sigma=Re s>1`, absolute convergence follows from

\[
 \sum_Nb_{m,r}(N)N^{-\sigma}
 \le\sum_Na_{rm}(N)N^{-\sigma}\le\zeta(\sigma),
 \qquad
 \sum_Nc_{m,r}(N)N^{-\sigma}\le\zeta(\sigma),
\]

because `0<=b_(m,r),c_(m,r)<=a_(rm)<=1`. Reindexing is therefore permitted:

\[
 \sum_Nb_{m,r}(N)N^{-s}
 =\sum_ka_m(k)(k^r)^{-s}
 =S_m(rs).
\]

Together with `(RP.6)` this proves `(RP.7)`. `[PROVED HERE]`

The excess is not a fitted remainder: it is the coefficientwise positive complement of the
literal power image inside the higher ramification shell. It becomes a quotient only after
passing to the free coefficient module.

## 3. Fixed-index positive-capacity response

Fix a finite prime set `F` with at least two elements and a temperature `tau>0`. On the
unitalized perfect-power Boolean slice `{k^m:k|P_F}`, use the ambient Mellin weight

\[
 (k^m)^{-\tau}=k^{-m\tau}.
\tag{RP.8}
\]

For `sigma>=0`, let

\[
 q_p(\sigma)={p^{-\sigma}\over1+p^{-\sigma}},
 \qquad
 w_p(\sigma)=q_p(\sigma)(1-q_p(\sigma)),
\tag{RP.9}
\]

and define the finite Boolean Schur capacity

\[
 D_F(\sigma)=\pi^2
 {\displaystyle\sum_{p<q}w_p(\sigma)w_q(\sigma)(\log p-\log q)^2
  \over
  \displaystyle\sum_pw_p(\sigma)(\log p)^2}.
\tag{RP.10}
\]

This is the capacity proved independently in the preceding ramification-diagonal card.

### Theorem 3.1 — one power event changes capacity

For every `sigma>0`,

\[
 0<D_F(\sigma)
 \le \pi^2\sum_{p\in F}p^{-\sigma}
 \le \pi^2|F|p_{\min}^{-\sigma},
\tag{RP.11}
\]

where `p_min=min F`. Consequently

\[
 D_F(\sigma)\longrightarrow0\qquad(\sigma\longrightarrow\infty).
\tag{RP.12}
\]

For every fixed `m>=2` and `tau>0`, there is an integer `r>=2` such that

\[
 \boxed{D_F(rm\tau)<D_F(m\tau).}
\tag{RP.13}
\]

Under the same source morphism `P_r`, the lower and upper perfect-power slices are identified by
`k^m->k^(rm)`, while their fixed-temperature capacities are respectively `D_F(m tau)` and
`D_F(rm tau)`. Hence the law event has a nonzero positive-organ response.

### Proof

Strict positivity is Theorem 2.1 of the ramification-diagonal card: every `w_p` is positive and
two distinct primes have distinct logarithms. The variational form gives

\[
 D_F(\sigma)=\pi^2\left(A-{B^2\over C}\right)\le\pi^2A,
 \qquad A=\sum_pw_p(\sigma).
\]

Writing `x=p^-sigma`, one has `w_p=x/(1+x)^2<=x`. This proves `(RP.11)` and `(RP.12)`.
Since `D_F(m tau)>0`, choose `r>=2` so large that

\[
 \pi^2|F|p_{\min}^{-rm\tau}<D_F(m\tau).
\]

Then `(RP.11)` gives `(RP.13)`. `[PROVED HERE]`

This theorem asserts existence of a strict response for sufficiently deep power events. It does
not claim monotonicity in every integer `r`.

### Theorem 3.2 — sharp depth scale and uniform jump threshold

Write the ordered aperture as `F={p_1<...<p_d}`, put `lambda_i=log p_i`, and define

\[
 c_F={\pi^2(\lambda_2-\lambda_1)^2\over4d\lambda_d^2},
 \qquad
 C_F^+={\pi^2d(d-1)\lambda_d^2\over\lambda_1^2}.
\tag{RP.14}
\]

Then for every `sigma>=0`,

\[
 \boxed{c_Fp_2^{-\sigma}\le D_F(\sigma)\le C_F^+p_2^{-\sigma},}
\tag{RP.15}
\]

and more sharply

\[
 \boxed{
 D_F(\sigma)\sim
 \pi^2{(\log p_2-\log p_1)^2\over(\log p_1)^2}p_2^{-\sigma}.}
\tag{RP.16}
\]

Let

\[
 J_F(\tau)=1+\left\lfloor
 {\log(C_F^+/c_F)\over\tau\log p_2}
 \right\rfloor.
\tag{RP.17}
\]

If depths `n>m` satisfy `n-m>=J_F(tau)`, then

\[
 D_F(n\tau)<D_F(m\tau).
\tag{RP.18}
\]

In particular, every power event `m->rm` with `(r-1)m>=J_F(tau)` has a strict negative capacity
response.

### Proof

For `sigma>=0`,

\[
 {1\over4}p_i^{-\sigma}\le w_i(\sigma)\le p_i^{-\sigma},
 \qquad w_1(\sigma)\ge w_i(\sigma).
\tag{RP.19}
\]

The function `x->x/(1+x)^2` is nondecreasing on `(0,1]`, because its derivative is
`(1-x)/(1+x)^3>=0`. Hence `p_1^-sigma>=p_i^-sigma` implies `w_1>=w_i`.

In `(RP.10)`, retain only the pair `(p_1,p_2)` in the numerator and bound the denominator above by
`d w_1 lambda_d^2`. This gives the lower bound in `(RP.15)`. For the upper bound, put
`W=sum_(i>=2)w_i`. Then

\[
 \sum_{i<j}w_iw_j
 \le\left(\sum_iw_i\right)W
 \le d(d-1)w_1p_2^{-\sigma},
\]

while the denominator is at least `w_1 lambda_1^2` and every squared clock gap is at most
`lambda_d^2`. This gives the upper bound.

As `sigma->infinity`, the denominator in `(RP.10)` is asymptotic to `w_1 lambda_1^2`, and the
unique leading numerator pair is `(1,2)`:

\[
 \sum_{i<j}w_iw_j(\lambda_i-\lambda_j)^2
 \sim w_1w_2(\lambda_2-\lambda_1)^2.
\]

Since `w_2~p_2^-sigma`, `(RP.16)` follows. Finally, `(RP.17)` makes

\[
 C_F^+p_2^{-n\tau}<c_Fp_2^{-m\tau}
\]

whenever `n-m>=J_F(tau)`. Apply `(RP.15)` to obtain `(RP.18)`. `[PROVED HERE]`

## 4. HT-organ separation

The publication-ready positive-shell theorem proves

\[
 \{\zeta\}\cup\{S_j:j\ge2\}
\]

jointly differentially algebraically independent over `C(s)`. In particular, for distinct `m`
and `rm`, the embedded marked analytic outputs `S_m` and `S_(rm)` satisfy no nonzero
differential-polynomial relation over `C(s)`. For `m>=12`, both also belong to the
zero-free-multiplier divisor-frame subfamily.

Precisely, on `Re s>1`,

\[
 H_j(s)={1\over\zeta((j+1)s)}-{1\over\zeta(js)},
 \qquad
 S_j(s)=\zeta(s)H_j(s).
\tag{RP.20}
\]

For `j>=12`, `H_j` extends holomorphically and zero-freely to `Re s>1/2`, and
`S_j^sharp=zeta H_j` denotes the resulting meromorphic continuation. Joint differential-algebraic
independence concerns these meromorphic carriers/germs; it does not assert convergence of the
original Dirichlet series in the critical strip.

This imported theorem is used only to classify the second response as a genuine HT-organ change;
the source morphism, excess formula `(RP.7)`, and capacity response `(RP.13)` were proved without
it. Exact parents:

- `docs/drafts/pipeline/4-publication-ready/positive-hypertranscendental-riemann-divisor-frame/main.tex`, Theorem `Zeta--shell differential freeness` and Theorem `Relative multiplier hypertranscendence`;
- `formal/GaloisForLFunctions/RHTower/HighExponentShellHypertranscendence.lean`, declarations `highExponentShellUpperEndCarrier_differentialIndependent_of_injective` and `highExponentShellUpperEndCarrier_differentialIndependent_twelve`.

The marking is load-bearing. Abstractly, the singly generated free differential extensions
`K_zeta<S_m>` and `K_zeta<S_(rm)>` are isomorphic by renaming a differential transcendental
generator. The theorem certifies nonreconstruction and distinct embedded source carriers, not
abstract nonisomorphism after forgetting coefficient support and the common meromorphic embedding.
Thus the card proves two distinct observer-doctrine responses. It proves no cross-doctrine
nonisomorphism theorem.

No Lean file was changed or built in this research step.

## 5. CFR consequence

This is the first literal event satisfying the nontrivial-event clause of repaired Gate 0 at
finite/source level:

- one source-native nonidentity morphism `P_r` is fixed before observer construction;
- coefficient doctrine, prime aperture `F`, temperature `tau`, prolongation doctrine, and trivial
  history indexing are unchanged;
- its positive Boolean observer changes by `(RP.13)`;
- its full-shell analytic observer acquires the nonzero affine excess `(RP.7)` and moves between
  differentially independent marked HT generators.

The event is not a relabeling of two route formulas. The same arithmetic power map produces both
responses. It supplies an actual source-law arrow missing from the earlier product atlas. It does
not construct the full law fibration `pi_law`, a constitutive section `kappa`, or complete Gate 0.

What remains open is equally important. This theorem does not prove the analytic excess `C_(m,r)`
hypertranscendental or a non-split `Ext` class. It also does not construct a third organ, comparison
curvature, signed Boolean orientation, Stokes contact response, cofinal normalization, physical
cost, source-nullity, or RH leverage. It proves a first two-organ constitutive event, not the CFR
field equations.

## 6. Conjecture / proof / fail loops

1. **Changing shell depth is only a relabeling.** Failed for power-related depths: `P_r` is an
   actual monoid endomorphism satisfying the exact pullback law `(RP.4)`. **Survivor:** use only
   morphisms induced by arithmetic operations, not arbitrary arrows between level labels.
2. **The power image exhausts the higher shell.** Failed at `2^(rm)3`. **Survivor:** the analytic
   excess `(RP.7)` is a nonzero positive affine extension.
3. **Boolean pullback makes every depth observationally identical.** Failed at fixed ambient
   temperature: its effective inverse temperature changes from `m tau` to `rm tau`, and a
   sufficiently deep event changes capacity. **Survivor:** normalized clock gauges may erase the
   event, while fixed ambient normalization detects it.
   Explicitly, if `tau_m=sigma_0/m`, then `(k^m)^(-tau_m)=k^-sigma_0` and every Boolean capacity is
   identical. Fixed `tau` is load-bearing for the response theorem.
4. **Capacity must change monotonically for every `r`.** Not proved and not needed. **Survivor:**
   positivity plus the explicit vanishing bound proves strict change for some arbitrarily deep
   event.
5. **Two-organ response solves a route endpoint.** Failed. The excess has no Stokes/contact or
   Cartier landing. **Survivor:** CFR now has one real law event on which a third-organ withheld
   test can be posed without inventing a source arrow.

## Lean-return notes

- Formalize the valuation identity `max v_p(k^r)=r max v_p(k)` and power pullback.
- Define the power-image support and prove strict inclusion using `2^(rm)3`.
- Formalize finite capacity upper bound and convergence only after paper audit.
- Existing shell differential-independence declarations are parents; do not duplicate them.
- No Lean file has been written or built.

## Gates

- [x] source-native nonidentity law morphism
- [x] exact pullback identity
- [x] nonzero analytic extension response
- [x] nonzero positive-capacity response for a sufficiently deep event
- [x] same observer indexing on both responses
- [x] no target formula used to define source morphism
- [x] third distinct observer-doctrine response (phase/history; Gibbs-determined, not independent)
- [x] flat Gibbs--clock comparison calibration
- [ ] first nontrivial comparison retaining analytic excess
- [ ] epistemically withheld target response
- [ ] cofinal/presentation-invariant field equation
- [ ] Stokes or RH leverage
- [ ] Lean formalization

## Log

- 2026-08-09 — constructed after hostile review required one actual law event rather than another observer tuple.
