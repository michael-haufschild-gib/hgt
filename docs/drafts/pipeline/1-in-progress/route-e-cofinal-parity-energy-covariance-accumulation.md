# Route E cofinal signed parity--energy covariance accumulation

- **ID:** `ROUTE-E-COFINAL-PARITY-ENERGY-COVARIANCE-001`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / `[OPEN CORE]`
- **Parent:** `rh-current-frontier-map.md`, `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **External audit:** intentionally omitted under current instruction; no priority claim permitted

## Frozen target

Let

\[
 S_y=\{p\text{ prime}:p\le y\},\qquad
 J_y(x)=\sum_{T\subseteq S_y}(-1)^{|T|}e^{-x\prod_{p\in T}p},\qquad
 Z_y(x)=\sum_{T\subseteq S_y}e^{-x\prod_{p\in T}p},
\]

and \(\psi_y=J_y/Z_y\).  Fix any aperture schedule satisfying, for all sufficiently small
\(x>0\),

\[
 (y(x)+1)x\ge 2\log(1/x).                               \tag{A0}
\]

**`COFINAL-SIGNED-COVARIANCE-ACCUMULATION`.**  For every \(\varepsilon>0\), there are
\(C_\varepsilon<\infty\) and \(x_\varepsilon>0\) such that

\[
 0<x\le x_\varepsilon
 \quad\Longrightarrow\quad
 |\psi_{y(x)}(x)|\le C_\varepsilon x^{1/2-\varepsilon}.  \tag{A1}
\]

The proof must proceed through the exact prime-insertion recurrence and retain its signed defect
forcing in the parity--energy covariance form

\[
 \Delta_{S,p}(x)=Z_S(x)Z_S(px)
 \int_x^{px}-\operatorname{Cov}_{S,t}((-1)^{|T|},E(T))\,dt. \tag{A2}
\]

No assumption equivalent to `(A1)`, no Mertens prefix bound, and no absolute-value replacement of
the signed accumulation is admissible.

## Why this target is sufficient

The positive partition satisfies \(Z_y(x)\le\sum_{n\ge1}e^{-nx}\ll x^{-1}\), so `(A1)` gives
\(|J_y(x)|\ll_\varepsilon x^{-1/2-\varepsilon}\).  The proved finite/infinite-volume bridge and
`(A0)` make the omitted tail \(O(x)\), hence the true Möbius--Laplace transform has every
strict-half bound.  Existing consumers then imply RH.

## Binding hostile gates

1. Derive the exact fully weighted Duhamel recurrence before proposing an inequality.
2. Check whether the proposed accumulation statistic is algebraically equal to the desired current.
   If so, verdict `CIRCULAR` unless an independently proved source inequality controls it.
3. Respect the alternating finite-volume jet
   \[
   \Delta'_{S,p}(0)=(p-1)2^{|S|}(-1)^{|S|+1}\prod_{q\in S}(q-1).
   \]
4. Reject termwise positivity, monotonicity, generic covariance inequalities, and MR fluctuation
   bounds unless they retain the coherent block mean.
5. No Lean work until a complete paper theorem survives these gates.

## Current status

- `[CONJECTURE]` `(A1)` is exactly the requested RH-strength cofinal bound.
- `[CORPUS]` `(A2)` and the alternating jet are unconditional Lean theorems in
  `RHTower/GibbsParityEnergyCovariance.lean`.
- `[OPEN CORE]` Find a non-circular cross-prime law controlling the signed weighted accumulation.

## Exact weighted recurrence `[PROVED HERE]`

Order the aperture primes as \(p_1,\ldots,p_k\), put
\(S_0=\varnothing\), \(S_j=S_{j-1}\cup\{p_j\}\), and write

\[
 Z_j(t)=Z_{S_j}(t),\qquad \psi_j(t)=J_{S_j}(t)/Z_{S_j}(t).
\]

At the fixed physical coupling \(x>0\), define

\[
 r_j=\frac{Z_{j-1}(p_jx)}{Z_{j-1}(x)},\qquad
 \alpha_j=\frac{1-r_j}{1+r_j},\qquad
 \beta_j=\frac{r_j}{1+r_j},                              \tag{A3}
\]

and retain the prime-dilation interval through

\[
 d_j=\psi_{j-1}(p_jx)-\psi_{j-1}(x)
    =\int_x^{p_jx}-\operatorname{Cov}_{S_{j-1},t}
       ((-1)^{|T|},E(T))\,dt .                            \tag{A4}
\]

The insertion laws \(J_j(x)=J_{j-1}(x)-J_{j-1}(p_jx)\) and
\(Z_j(x)=Z_{j-1}(x)+Z_{j-1}(p_jx)\) give, without discarding a sign or a
partition weight,

\[
 \boxed{\psi_j(x)=\alpha_j\psi_{j-1}(x)-\beta_jd_j.}       \tag{A5}
\]

Indeed, divide numerator and denominator by \(Z_{j-1}(x)>0\), substitute
\(\psi_{j-1}(p_jx)=\psi_{j-1}(x)+d_j\), and collect terms.  Since the
partition function is strictly decreasing, \(0<r_j<1\), hence

\[
 0<\alpha_j<1,\qquad 0<\beta_j<\tfrac12,
 \qquad \alpha_j=1-2\beta_j.                              \tag{A6}
\]

Let

\[
 A_{a:b}=\prod_{\ell=a}^{b}\alpha_\ell,
 \qquad A_{a:b}=1\quad(a>b).
\]

As \(\psi_0(x)=1\), induction in `(A5)` proves the fully unrolled law

\[
 \boxed{
 \psi_k(x)=A_{1:k}-
   \sum_{j=1}^{k}\beta_j A_{j+1:k}
     \int_x^{p_jx}-\operatorname{Cov}_{S_{j-1},t}
       ((-1)^{|T|},E(T))\,dt .}                           \tag{A7}
\]

This is the requested recurrence with every recurrence weight, dilation interval, and
finite-volume sign retained.

## Exact retained-mass law `[PROVED HERE]`

The positive recurrence weights in `(A7)` have a closed total mass:

\[
 \boxed{\sum_{j=1}^{k}\beta_jA_{j+1:k}
       =\frac{1-A_{1:k}}2<\frac12.}                       \tag{A8}
\]

Proof: `(A6)` gives

\[
 \beta_jA_{j+1:k}
   =\tfrac12(A_{j+1:k}-A_{j:k}),
\]

and the sum telescopes.  Thus coefficient growth is not the obstruction.  The forcing in
`(A7)` is a signed subprobability mean of the normalized-current changes across the actual
prime-dilation intervals.  Taking absolute values gives only

\[
 \left|\sum_j\beta_jA_{j+1:k}d_j\right|
 \le \frac{1-A_{1:k}}2\max_j|d_j|\le1,                  \tag{A9}
\]

which cannot approach a positive power of \(x\).

## Quadratic signed-energy survivor [PROVED HERE]

Taking a positive norm only after the signed insertion exposes an additional exact loss.  Define

\[
 \mathcal Q_S(x)=\frac{J_S(x)^2}{Z_S(x)}=Z_S(x)\psi_S(x)^2
\]
and
\[
 \mathcal D_{S,p}(x)=
 \frac{Z_S(x)Z_S(px)}{Z_S(x)+Z_S(px)}
   \bigl(\psi_S(x)+\psi_S(px)\bigr)^2\ge0.
\]

Polarization of \(J_{S\cup p}=J_S-J_S\circ p\) against
\(Z_{S\cup p}=Z_S+Z_S\circ p\) gives

\[
 \boxed{\mathcal Q_{S\cup p}(x)+\mathcal D_{S,p}(x)
       =\mathcal Q_S(x)+\mathcal Q_S(px).}               \tag{A9a}
\]

This is not an absolute-value estimate: the loss retains whether the normalized currents at
\(x\) and \(px\) have the same sign.  It identifies the only positive energy created by the signed
difference.  In particular,

\[
 \mathcal Q_{S\cup p}(x)\le \mathcal Q_S(x)+\mathcal Q_S(px). \tag{A9b}
\]

For \(r>0\), finite aperture makes all following integrals convergent.  Put
\[
 \mathscr E_r(S)=\int_0^\infty x^{r-1}\mathcal Q_S(x)\,dx,\qquad
 \mathscr D_r(S,p)=\int_0^\infty x^{r-1}\mathcal D_{S,p}(x)\,dx.
\]
Changing variables \(u=px\) in (A9a) yields the exact Mellin balance
\[
 \boxed{\mathscr E_r(S\cup p)+\mathscr D_r(S,p)
       =(1+p^{-r})\mathscr E_r(S).}                      \tag{A9c}
\]

Since \(\mathscr E_r(\varnothing)=\Gamma(r)\), iterating gives
\[
 \mathscr E_r(S_k)=
 \Gamma(r)\prod_{j=1}^k(1+p_j^{-r})
 -\sum_{j=1}^k\mathscr D_r(S_{j-1},p_j)
       \prod_{\ell=j+1}^k(1+p_\ell^{-r}).                \tag{A9d}
\]

For \(r>1\), discarding the dissipation already leaves a cofinally finite Euler ceiling.  At
\(0<r\le1\), the Euler baseline diverges and a source theorem must prove that the positive
same-sign dissipation saturates it to the required precision.  Thus squaring does not prove the
strict-half endpoint, but it converts the missing signed cancellation into a precise positive
coherence-saturation problem.  Antiscale coherence
\(\psi_S(px)\approx-\psi_S(x)\) is the exact escape mode.

## Circularity theorem `[PROVED HERE]`

Put

\[
 W_k(x)=\sum_{j=1}^{k}\beta_jA_{j+1:k}d_j.
\]

Equation `(A7)` is the exact identity \(\psi_k=A_{1:k}-W_k\).  Consequently, for every
nonnegative error budget \(\eta\),

\[
 \boxed{|W_k(x)-A_{1:k}|\le\eta
       \quad\Longleftrightarrow\quad |\psi_k(x)|\le\eta.} \tag{A10}
\]

In particular, a theorem called “signed covariance accumulation” whose conclusion is merely

\[
 |W_k(x)-A_{1:k}|\ll x^{1/2-o(1)}
\]

is not a producer for `(A1)`: it is `(A1)` written through the exact recurrence.  It becomes a
proof only if a separately stated source theorem controls the cross-prime signed mean before
`(A10)` is invoked.

There is also no gain from changing or averaging insertion orders.  For any two orderings
\(\sigma,\tau\) of the same aperture, endpoint invariance and `(A7)` force

\[
 W_k^{\sigma}(x)-W_k^{\tau}(x)
   =A_{1:k}^{\sigma}(x)-A_{1:k}^{\tau}(x).                \tag{A11}
\]

Thus all order dependence of the contraction baseline is exactly compensated by order dependence
of the accumulated covariance.  Permutation averaging cannot manufacture an endpoint estimate.

## Alternating-sign audit

For \(j>1\), the free-boundary jet in the parent theorem gives

\[
 d_j'(0)=(p_j-1)\psi_{j-1}'(0),\qquad
 \operatorname{sgn}d_j'(0)=(-1)^j.                       \tag{A12}
\]

Hence the forcing terms in `(A5)` alternate infinitesimally with finite volume.  This is a local
jet statement, not a uniform sign theorem on the moving intervals `[x,p_jx]`.  Its coefficient
contains \(\prod_{q\in S_{j-1}}(q-1)\), so its Taylor window collapses nonuniformly with aperture.
Using `(A12)` as though it oriented the physical cofinal terms would violate gate 3.

The failure is not merely a lack of uniformity in the proof.  It already occurs in the
two-prime gas.  For \(S=\{2,3\}\), put \(u=e^{-x}\).  Directly from the four configurations,

\[
 \psi_{\{2,3\}}(x)
 =\frac{1-u-u^2+u^5}{1+u+u^2+u^5}
 =1-\frac{2u(1+u)}{1+u+u^2+u^5}.                        \tag{A13}
\]

For
\[
 H(u)=\frac{u(1+u)}{1+u+u^2+u^5},
\]
exact differentiation gives
\[
 H'(u)=\frac{1+2u-4u^5-3u^6}{(1+u+u^2+u^5)^2}>0
 \qquad(0<u\le\tfrac12),                                \tag{A14}
\]
because \(4u^5+3u^6\le 11/64<1\).  Since \(u'=-u\), equations (A13)--(A14) imply
\[
 \psi_{\{2,3\}}'(x)>0\qquad(x\ge\log2).                  \tag{A15}
\]
Therefore every dilation increment
\(\psi_{\{2,3\}}(px)-\psi_{\{2,3\}}(x)\) is positive for \(p>1\) and
\(x\ge\log2\).  But its derivative at \(x=0\) is negative by (A12).  Thus the same
finite-volume forcing changes orientation with coupling.  No global alternating-sign pairing can
be inferred from the free-boundary jet.

## Hostile verdict and revised open core

The exact requested accumulation formula is now proved, but the requested strict-half estimate is
not: by `(A10)` that estimate is the RH-strength endpoint itself.  No corpus theorem supplies an
independent bound for its signed cross-prime mean.

What remains genuinely open is narrower than the original wording:

> **`WEIGHTED-PRIME-DILATION-INCREMENT-CANCELLATION`.**  Prove an arithmetic cancellation law for
> the signed variables \(d_j\) under the positive hazard weights
> \(\beta_jA_{j+1:k}\), using information not recoverable from the endpoint identity `(A7)`.

Any candidate must distinguish the actual prime prefixes from arbitrary bounded sequences, retain
the coherent low-frequency mode, and survive `(A11)` and the nonuniform-jet audit.  Generic
covariance inequalities, absolute moments, fixed-order Wold reporters, MR fluctuation estimates,
and insertion-order averaging fail those tests.

## Status after exact audit

- `[PROVED HERE]` fully weighted covariance recurrence `(A7)`.
- `[PROVED HERE]` exact retained forcing mass `(A8)`.
- `[PROVED HERE]` endpoint/accumulation equivalence and order-gauge law `(A10)`--`(A11)`.
- `[OPEN; RH-STRENGTH]` the numerical bound `(A1)`.
- `[NO THEATRE]` no claim that the exact representation proves its own endpoint estimate.
- `[PROVED HERE]` pointwise signed-energy polarization and nonnegative same-sign dissipation
  `(A9a)`--`(A9b)`; Mellin balance `(A9c)`--`(A9d)` is the paper corollary.
- `[LEAN]` unconditional finite laws in
  `RHTower/GibbsSignedCovarianceAccumulation.lean`; targeted build 8659/8659 passes; axioms only
  `propext`, `Classical.choice`, and `Quot.sound`; umbrella wired.

## 2026-08-06 critical-dissipation falsifier

Proposed bounded Mellin-energy deficit for every `0<r\le1` is false. Paper theorem
`ROUTE-E-CRITICAL-DISSIPATION-ANTISCALE-NOGO-001` proves that for every fixed `0<r<1`,

\[
 \mathscr E_r(S_Y)\to+\infty
 \qquad(S_Y=\{p:p\le Y\}).
\]

Proof uses exact source Mellin reporter

\[
 \mathscr E_r(S)\ge\frac{|\Gamma(r+it)|^2}{\Gamma(r)}
 \prod_{p\in S}\frac{|1-p^{-r-it}|^2}{1+p^{-r}}
\]

at `t=\pi/\log Y`. Every terminal prime has almost negative dilation phase, so normalized local
factors exceed one; Chebyshev supplies `\gg Y/\log Y` such primes, while loss from
`p\le Y^{3/4}` is lower order. Antiscale coherence is therefore attained cofinal resonance, not
merely logical escape.

This kills Mellin dissipation saturation as an all-`0<r\le1` producer but not pointwise target
`(A1)`. Surviving options: prove distinct `r=1` endpoint, project/renormalize moving
`1/\log Y` antiscale chamber before taking positive norm, or return to signed statistic cancelling
across terminal shells. Full proof and positive survivor:
`../5-failed/route-e-critical-dissipation-saturation-antiscale-resonance-no-go.md`.

Finite source factorization, exact dissipation null space, normalized local reporter, and terminal
window gain are Lean-certified in
`RHTower/GibbsCriticalDissipationAntiscaleResonance.lean`; targeted build `8859/8859` passes and
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-06 prime-sieve normalization cross-audit

The new prime-sieve Hilbert--Schmidt stack closes one exact part of the surviving `r=1` energy
normalization, but not the signed current.  For finite prime aperture `P`, write

\[
 a_P=\prod_{p\in P}(1-p^{-1}),\qquad
 B_1(P)=\prod_{p\in P}(1+p^{-1}),\qquad
 C_2(P)=\prod_{p\in P}(1-p^{-2}).
\]

Then

\[
 a_PB_1(P)=C_2(P)=\frac{T_2(P)}{T_2(\varnothing)},
 \qquad C_2(P_N)\longrightarrow T_2(\varnothing)^{-1}>0.       \tag{A16}
\]

Hence raw critical Euler growth is exactly reciprocal sieve-density growth times a regular
Hilbert--Schmidt factor.  The new sieve-operator convergence closes the `p^-2` factor.  It cannot
control the normalized `p^-1` source layer: multiplying by `a_P` erases source mass, while dividing
back restores the entire divergence.  The existing prime-valuation normalization-amplification
no-go makes this obstruction exact (`a_P/p` becomes `1/p`).

This rules out a false shortcut from sieve-density telescoping, determinant convergence, or generic
seminorm completion to `(A1)`.  It sharpens the possible positive continuation: construct a
source-defined **signed first-trace/Bockstein countertransport** from `(E-COV)` which cancels the
normalized `1/p` transition before positive norm and leaves the now-closed `p^-2` remainder.  Until
an explicit non-circular formula is produced, that is the same open
`WEIGHTED-PRIME-DILATION-INCREMENT-CANCELLATION` problem, not a solution.

For the Hall lane, `a_{P_{j-1}}/p_j` gives canonical scalar weights summing cofinally to one, but
does not supply their moving-window lift to `R_X^gr`, collision-quotiented interval Hall, or
cross-anchor incoming-load control.

Paper proof and unconditional Lean:
`../3-formalized/route-e-critical-gibbs-sieve-normalization-wall.md` and
`RHTower/GibbsCriticalSieveNormalizationWall.lean`.

## 2026-08-07 antiscale first-trace and batch-frame audit

The scalar first-trace continuation left by the sieve-normalization wall is now exactly classified.
For one insertion, let

\[
 a={\psi_S(x)-\psi_S(px)\over2},\qquad
 s={\psi_S(x)+\psi_S(px)\over2}.
\]

Then the normalized enlarged current is

\[
 \boxed{\psi_{S\cup p}(x)=a+\alpha_{S,p}(x)s.}            \tag{A17}
\]

The antiscale coordinate \(a\) is transmitted with coefficient exactly one.  If a scalar
normalization changes by \(q'=\lambda q\), \(\lambda\ne1\), its first-normal reader is

\[
 \boxed{
 {q\psi_S(x)-q'\psi_{S\cup p}(x)\over q-q'}
 =a+{1-\lambda\alpha_{S,p}(x)\over1-\lambda}s.
 }                                                         \tag{A18}
\]

Hence it restricts to the identity when \(\psi_S(px)=-\psi_S(x)\).  No scalar sieve-density,
Euler-baseline, or first-trace Bockstein can cancel exact antiscale coherence; viable
countertransport must be multichannel and cross-prime.

New character-distance theorems do supply one unconditional global multichannel fact.  For
\(\chi_t(p)=e^{it\log p}\),

\[
 \sum_{p\le z}{|1+\chi_t(p)|^2\over p}
 =2D(-1,\chi_t;p\le z)^2
 \ge2(\log\log z-7\log\log T-C)                           \tag{A19}
\]

uniformly on the corpus frequency window.  Thus a common Mellin phase cannot occupy the antiscale
null direction at all primes.  But this frame has the sharp ceiling

\[
 \sum_{p\le z}{|1+\chi_t(p)|^2\over p}
 \le4\sum_{p\le z}{1\over p},                             \tag{A20}
\]

with equality at \(t=0\).  Its entire mass is only logarithmic in \(\log z\), so independent
harmonic contraction recovers at most log powers—the already-known
\(\prod(p-1)/(p+1)\) baseline—not the missing physical power.

Changing prefixes are removed exactly by a finite batch law.  For disjoint \(S,P\), define

\[
 m_T=\prod_{p\in T}p,\quad
 w_T=Z_S(m_Tx),\quad
 g_T=(-1)^{|T|}\psi_S(m_Tx),\quad
 W=\sum_{T\subseteq P}w_T.
\]

Then

\[
 Z_{S\cup P}(x)=W,\qquad J_{S\cup P}(x)=\sum_Tw_Tg_T,
\]

and the order-free polarization is

\[
 \boxed{
 {J_{S\cup P}(x)^2\over Z_{S\cup P}(x)}
 +{1\over2W}\sum_{T,U}w_Tw_U(g_T-g_U)^2
 =\sum_Tw_Tg_T^2.
 }                                                         \tag{A21}
\]

Its residual vanishes exactly when one common prefix current follows the full checkerboard
\(\psi_S(m_Tx)=(-1)^{|T|}c\).  This is stronger infrastructure than the one-step escape
description: all insertion orders have one common batch residual.

**Revised first open premise.**
`GIBBS-MOVING-BOUNDARY-NONPRODUCT-FRAME`: prove that literal Gibbs batch weights at the moving
multiplicative cutoff have a nonproduct boundary-correlation component whose checkerboard
dispersion supplies the missing physical power beyond the harmonic ceiling \((A20)\).  Required
proof must control prefix stabilization, terminal high-frequency resonance, and boundary
correlation in one estimate.  A Bernoulli/pretentious product approximation cannot close Route E.

Paper and Lean:
`../3-formalized/new_scientific_knowledge/route-e-antiscale-first-trace-frame-law.md` and
`RHTower/GibbsAntiscaleFirstTraceFrame.lean`.  `OPEN-SOURCE-001` and RH remain open.

## 2026-08-07 parity-coarse batch rigidity

The \(2^{|P|}\)-leaf residual in (A21) now has an exact exhaustive two-class decomposition.
Write

\[
 W_\pm=\sum_{\substack{T\subseteq P\\ |T|\ {\rm even/odd}}}w_T,\qquad
 K_\pm=\sum_{\substack{T\subseteq P\\ |T|\ {\rm even/odd}}}
   w_T\psi_S(m_Tx),
\]

and let \(\mathcal V_\pm\) be weighted within-class variances of
\(\psi_S(m_Tx)\).  For \(P\ne\varnothing\), both class masses are positive.  Coarse
antiscale defect is

\[
 \mathcal C_{S,P}(x)
 ={W_+W_-\over W_++W_-}
 \left({K_+\over W_+}+{K_-\over W_-}\right)^2
 ={(W_-K_++W_+K_-)^2\over (W_++W_-)W_+W_-}.             \tag{A22}
\]

Exact two-class polarization gives

\[
 \boxed{
 {J_{S\cup P}(x)^2\over Z_{S\cup P}(x)}
 +\mathcal V_+(x)+\mathcal V_-(x)+\mathcal C_{S,P}(x)
 =\sum_{T\subseteq P}w_T\psi_S(m_Tx)^2.
 }                                                        \tag{A23}
\]

All three added terms are nonnegative.  Consequently, if batch residual is at most
\(\eta\), then separately

\[
 \mathcal V_+\le\eta,\qquad \mathcal V_-\le\eta,\qquad
 \mathcal C_{S,P}\le\eta.                                \tag{A24}
\]

Zero residual is equivalent to constancy of \(\psi_S(m_Tx)\) inside each parity class together
with opposite even/odd class means.  Thus no hidden fourth escape exists among individual
leaves: every near checkerboard must simultaneously satisfy same-parity rigidity and coarse
antiscale opposition.

This is a genuine reduction, not closure.  Revised source task is exhaustive disjunction:

> **GIBBS-PARITY-CLASS-RIGIDITY-BREAKING.**  At a cofinal moving batch, prove a
> physical-power lower bound for at least one of \(\mathcal V_+\), \(\mathcal V_-\), or
> \(\mathcal C_{S,P}\), relative to leaf energy in (A23), while retaining literal Gibbs
> weights and parity balance.

New Halász--GHS/Lorentzian prime-supported mean-square stack may help with frequency-averaged
same-parity variation, but its sharp Halász scale is only \(x^{1-o(1)}\).  It does not by itself
supply missing square-root exponent, nor control parity-mass collapse in (A22).  Creditable use
requires new conversion from its frequency average to one term of (A23) at physical-power
strength.

A further exact coordinate audit shows why “nonproduct boundary component” alone is too weak.
Set

\[
 A=K_++K_-,\qquad B=W_+-W_-,\qquad J=K_+-K_-,\qquad W=W_++W_-.
\]

Then two independent determinants are

\[
 D_{\rm anti}=WA-BJ=2(W_-K_++W_+K_-),\qquad
 D_{\rm np}=WJ-BA=2(W_-K_+-W_+K_-),                  \tag{A25}
\]

and

\[
 \boxed{\mathcal C_{S,P}={D_{\rm anti}^2\over W(W^2-B^2)}}. \tag{A26}
\]

Companion \(D_{\rm np}\) detects unequal unsigned even/odd response and vanishes for
parity-block product response. It does not enter (A26). Boundary nonproductness may therefore
sit entirely in antiscale direction and contribute no coarse dissipation. Revised premise
must prove **antiscale-transverse** boundary response—\(D_{\rm anti}\) at physical-power
strength—or one of within-parity variances. This strictly sharpens and supersedes bare
“nonproduct frame” wording.

Paper and unconditional Lean:
`../3-formalized/new_scientific_knowledge/route-e-parity-coarse-grained-batch-rigidity.md` and
`RHTower/GibbsBatchParityCoarseGraining.lean`.  Targeted build `9712/9712`; axioms only
`propext`, `Classical.choice`, and `Quot.sound`.  `OPEN-SOURCE-001` and RH remain open.

## 2026-08-07 static all-prime regular-kernel closure

Two cofinal recurrence theorems now remove the full static regular-kernel continuation, not only
one selected weight.  For arbitrary fixed nonnegative weights \(\omega_p\), set

\[
 \mathcal F_\omega(t)=\sum_p{\omega_p\over p}|1+e^{it\log p}|^2.
\]

If \(\sum_p\omega_p/p<\infty\), then for every \(\delta>0,T\) there is \(t>T\) with
\(\mathcal F_\omega(t)<\delta\).  If that mass is not summable, the form is already nonsummable
at \(t=0\), where every term is exactly \(4\omega_p/p\).  Hence no fixed nonnegative diagonal
all-prime weight is both everywhere finite and uniformly coercive.

The stronger cross-prime theorem removes regular off-diagonal repair.  For every arbitrary complex
kernel \(K_{pq}\) with

\[
 \sum_{p,q}|K_{pq}|<\infty,
\]

the complete ordered-pair form

\[
 \mathcal Q_K(t)=\sum_{p,q}K_{pq}(1+p^{it})\overline{(1+q^{it})}
\]

is absolutely convergent and, for every \(\delta>0,T\), has some \(t>T\) with
\(|\mathcal Q_K(t)|<\delta\).  Positivity, Hermitian symmetry, finite rank, and diagonality are not
used.  Proof chooses one finite pair head, recurs every prime in both coordinate projections to
phase \(-1\), and controls complete tail by entrywise absolute mass.

This is class closure, not `OPEN-SOURCE-001`.  Bare “off-diagonal” is no longer an adequate
survivor.  Revised hard core is:

> **GIBBS-MOVING-OR-SINGULAR-ANTISCALE-TRANSVERSE-SOURCE.**  Derive from literal ordinary-integer
> Gibbs/co-Poisson source either a moving boundary kernel tied to physical aperture, or a
> non-absolutely-summable singular cross-prime principal part with canonical source
> renormalization, and prove that it produces \(D_{\rm anti}\) or within-parity variation at
> physical-power strength before terminal antiscale resonance is scalarized.

Static diagonal and entrywise-absolutely-summable off-diagonal frames cannot meet that premise.
Signed nonquadratic cancellation across moving terminal shells remains logically outside these
theorems.  Paper and unconditional Lean:
`../3-formalized/new_scientific_knowledge/route-e-static-antiscale-frame-dichotomy.md`,
`../3-formalized/new_scientific_knowledge/route-e-static-absolute-kernel-recurrence.md`,
`RHTower/RouteEStaticAntiscaleFrameDichotomy.lean`, and
`RHTower/RouteEStaticAbsoluteKernelRecurrence.lean`.  Targeted builds pass `9719/9719` and
`9720/9720`; axioms only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-07 moving terminal-kernel inverse-square law

The first moving continuation is now quantitatively classified.  For \(Y>1\), let a complex
aperture-dependent kernel \(K^{(Y)}_{pq}\) be supported where both prime coordinates obey

\[
 0\le\log Y-\log p\le\eta\log Y.
\]

No positivity, Hermitian symmetry, diagonal structure, or aperture independence is assumed.  At
the explicit physical antiscale frequency \(t_Y=\pi/\log Y\), complete ordered-pair energy obeys

\[
 \boxed{
 \left|\sum_{p,q}K^{(Y)}_{pq}(1+p^{it_Y})
          \overline{(1+q^{it_Y})}\right|
 \le (\pi\eta)^2\sum_{p,q}|K^{(Y)}_{pq}|.
 }
\]

This follows from unit-circle chord bound
\(|1+p^{it_Y}|\le\pi\eta\) on terminal log-band and absolute `tsum` control.  Thus moving support
does not by itself escape antiscale coherence.  Uniform positive coercivity requires terminal
entrywise mass at least \(\gg\eta^{-2}\), or logarithmically cross-scale entries outside band.
For fixed-ratio terminal window \((Y/C,Y]\), \(\eta=(\log C)/(\log Y)\), so any such regular
kernel needs \(\ell^1\) mass \(\gg(\log Y)^2\); harmonic/logarithmic terminal mass is insufficient.

This sharpens current hard core again: a viable moving source must be **mass-divergent and
canonically renormalized**, or genuinely cross-scale, or signed/nonquadratic before norm.  Explicit
grade-recurrent cube relation's annular reservoir and source co-moving diffuse codiagonal pass this
necessary escape test only because they spread/migrate source mass; neither currently proves
antiscale-transverse physical capacity.  `OPEN-SOURCE-001` remains open.

Paper and unconditional Lean:
`../3-formalized/new_scientific_knowledge/route-e-moving-terminal-kernel-resonance.md` and
`RHTower/RouteEMovingTerminalKernelResonance.lean`.  Targeted build `9721/9721`; axioms only
`propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-07 terminal-leg and multilinear resonance closure

The previous inverse-square theorem left two escape labels too broad.  A cross-scale entry may
have one terminal coordinate and one remote coordinate; a signed nonquadratic source may have more
than two seam factors.  Both regular classes now have a complete physical-frequency bound.

If every nonzero entry of an entrywise absolutely summable complex kernel has **at least one**
coordinate in the terminal log-band, then at (t_Y=\pi/\log Y),

\[
 \boxed{
 \left|\sum_{p,q}K^{(Y)}_{pq}(1+p^{it_Y})
       \overline{(1+q^{it_Y})}\right|
 \le2\pi\eta\sum_{p,q}|K^{(Y)}_{pq}|.
 }
\]

The other coordinate is unrestricted.  Therefore terminal-by-remote cross-scale coupling still
needs ℓ1 mass (Ω_C(\log Y)) on a fixed-ratio terminal interval.  Remote-by-remote terms do
not represent a terminal boundary response without a separate source connector.

For an arbitrary finite leg set (I), every entrywise-ℓ1 signed monomial with one selected
terminal leg obeys

\[
 \left|\sum_aK_a\prod_{j\in I}(1+p_{a,j}^{it_Y})\right|
 \le\pi\eta,2^{|I|}\sum_a|K_a|,
\]

and if all legs are terminal the right side sharpens to

\[
 (\pi\eta)^{|I|}\sum_a|K_a|.
\]

Thus fixed-arity signed/nonquadratic terminal-shell sums are not an independent regular escape.
Survivors are now exact: canonical mass divergence/renormalization; a component with no terminal
leg plus a genuine cutoff connector; arity growing with aperture strongly enough to beat the
resonance factor; or relation-valued/pre-norm cancellation not reducible to an absolutely
summable monomial expansion.

The diffuse Fisher codiagonal remains a legitimate noncompact candidate because its mass migrates
in ordinary-integer index and its formula has no prime terminal seam.  The grade-recurrent cube
remains a legitimate growing-arity relation candidate.  Neither supplies the missing signed
physical connector: the former lacks a theorem into (D_{\rm anti}) or within-parity variation;
the latter lacks cross-anchor co-degree/interval Hall expansion and weighted endpoint flux.

**Revised exact hard core:**
`GIBBS-SINGULAR-OR-GROWING-ARITY-PHYSICAL-TRANSVERSE-SOURCE`.  Prove from one literal
ordinary-integer source either a canonically renormalized noncompact/mass-divergent carrier or the
physical capacity of the explicit growing-arity cube, and in either case derive
(D_{\rm anti}) or within-parity variation at physical-power strength with recurrence weights,
prime-dilation intervals, and alternating finite-volume signs retained.  `OPEN-SOURCE-001`, Route
E, and RH remain open.

Paper and unconditional Lean:
`../3-formalized/new_scientific_knowledge/route-e-terminal-leg-multilinear-resonance.md` and
`RHTower/RouteETerminalLegMultilinearResonance.lean`.  Targeted build `9722/9722`; axioms only
`propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-08 physical-shell parity--energy regression splice

New paper theorem **route-e-physical-shell-conditioned-parity-energy-regression-law.md**
constructs literal positive Gaussian shell before Euler parity scalarization.  Under independent
Euler occupancies,

\[
 N=\sum B_p,\qquad E=\sum B_p\log p,
\]

its exact antiscale residual is parity--energy Schur complement

\[
 D_Y=\pi^2\left(\operatorname{Var}N-
   \frac{\operatorname{Cov}(N,E)^2}{\operatorname{Var}E}\right)
 =\frac{\pi^2}{a^3}\frac{Y^a}{(\log Y)^3}(1+o(1)).
\]

At regression frequency and physical center, shell-conditioned odd determinant satisfies

\[
 \frac{|Z_Y^{\rm sh}|^2-|M_Y^{\rm sh}|^2}{(P_Y^{\rm sh})^2}
 =-X^{-\pi^2/(a^2(\log Y)^3)+o((\log Y)^{-3})}.
\]

This is an independent finite Euler source theorem, not equation (A10) rewritten.  It proves
conditioned odd-cube transversality but does not control prime-insertion variables \(d_j\) in
(A7), because Euler Bernoulli law and physical exponential Gibbs law are different measures.

Simplest descent is impossible.  A positive mixture of raw Laplace kernels is decreasing in
integer energy, whereas centered log shell increases below center.  Any signed shell
decomposition leaves exact off-diagonal polarization

\[
 |Z|^2-|M|^2
 =\iint\left(Z_y\overline{Z_z}-M_y\overline{M_z}\right)
       d\alpha(y)d\overline{\alpha}(z).
\]

Therefore revised independent source target is
**RECURRENCE-WEIGHTED-SHELL-COVARIANCE-ACCUMULATION**: derive from literal exponential Gibbs source
a lower frame law for this cross-shell kernel under actual recurrence weights and prime-dilation
intervals, before invoking (A7) or (A10).  Merely concluding

\[
 |W_k-A_{1:k}|\ll x^{1/2-o(1)}
\]

remains circular by existing theorem.

Lean corpus was inspected read-only.  No Lean edit or build was performed for this splice.

## 2026-08-08 source-faithful Euler-edge unit-shell splice

New paper theorem
`../2-fully-proven/new_scientific_knowledge/route-e-source-faithful-euler-tilt-unit-shell-law.md`
replaces abstract shell decomposition by exact identity.  Under Euler Bernoulli tilt
\(q_{p,\sigma}=p^{-\sigma}/(1+p^{-\sigma})\),

\[
 Z_S(x)=\mathcal P_{\sigma,S}\mathbb E_\sigma[e^{\sigma E-xe^E}],
 \qquad
 J_S(x)=\mathcal P_{\sigma,S}\mathbb E_\sigma[(-1)^Ne^{\sigma E-xe^E}].
\tag{A32}
\]

Physical multiplier is exact unit-log shell:

\[
 \frac{W(E^*+u)}{W(E^*)}=e^{\sigma(u+1-e^u)},
 \qquad E^*=\log(\sigma/x).
\tag{A33}
\]

For canonical cofinal aperture \(Y\asymp x^{-1}\log(1/x)\), its central tilt is forced to

\[
 \sigma_x=1+\frac{2\log\log Y}{(\log Y)^2}+O((\log Y)^{-2}).
\tag{A34}
\]

This invalidates fixed-\(\sigma<1\) broad-shell descent at actual aperture.  At moving Euler edge,
regression frequency obeys

\[
 t^*=\frac{2\pi}{\log Y}
      +O\!\left(\frac{\log\log Y}{(\log Y)^2}\right),
 \qquad
 t^*E^*=2\pi+o(1),
\tag{A35}
\]

and unconditioned all-cumulant antiscale amplitude is exactly

\[
 \left|\mathbb E_{\sigma_x}e^{i(\pi N-t^*E)}\right|
 =(\log Y)^{-2}e^{O(1)}.
\tag{A36}
\]

Thus raw parity is compatible with escape on physical unit shell, while Euler accumulation alone
stops at harmonic ceiling.  Missing theorem is neither diagonal broad-shell transversality nor
endpoint restatement (A10).  Analytic and incidence branches now meet in one source premise:

**UNIT-LOG-SHELL-E3-PARITY-CARLESON-AND-RECURRENCE-SEAM** -- within bounded physical log-product
shells, construct source-predeclared local \(E_3\)/reservoir relation, prove unit column load and
oriented seam flux, and transport same weights through exact prime-dilation recurrence before
forming endpoint current.

No Lean file was edited or built.

## 2026-08-11 exact Euler-gauge cancellation and endpoint-rate correction

The bare-source chi-square continuation is valid but not an RH-scale transport theorem. On the
critical unit shell its relative normalized error at the forced tilt is only controlled by

\[
 O\!\left(\frac{\log\log Y}{\sqrt{\log Y}}\right),
\]

which is far larger than (Y^{-1/2+o(1)}). The conjecture that absolute or relative contiguity would
move a critical proof of `(A1)` to the saddle therefore fails.

The literal physical source has exact cancellation. For every occupied subset (T),

\[
 \mathcal P_{\sigma,Y}\nu_{\sigma,Y}(T)
 e^{\sigma E(T)-xe^{E(T)}}=e^{-xm(T)}.                    \tag{A37}
\]

Consequently every predeclared normalized physical observable and relation flow is exactly
independent of Euler gauge. Critical and moving gauges are two factorizations of the same finite
Gibbs atoms, not two physical sources. This removes moving-tilt transfer and its second-moment
premise from the open core.

For a partial opposite-parity matching with normalized unmatched physical mass (u_X), whose
matched products satisfy (|m-n|\le H_X), pairwise polarization gives the exact receiver

\[
 \frac{|J_Y(1/X)|}{Z_Y(1/X)}
 \le u_X+\tanh\!\left(\frac{H_X}{2X}\right)
 \le u_X+\frac{H_X}{2X}.                                 \tag{A38}
\]

Thus (u_X\le X^{-1/2+o(1)}) and (H_X\le X^{1/2+o(1)}) suffice with no tilt loss. This does not
construct the matching: the joint breadth--rough short-interval incidence, column load,
zero/one-large-prime seam orientation, and recurrence compatibility remain the producer. The new
knowledge is exact removal of a false interface, not endpoint closure.

Lean corpus was inspected read-only. The atomwise core `(A37)` was already certified as
`routeEEulerTiltTerm_eq_gibbsTerm`; no Lean source was written during refactor.

## 2026-08-11 Deninger-vacuum and detailed-balance fracture

The strict Deninger adiabatic endpoint cannot absorb the physical vacuum by a finite recurrence.
If
\[
 F(t)=\sum_{j=1}^r c_j e^{-a_je^t},\qquad a_j>0\text{ distinct},
\]
then Meyer decay at the left collar makes the analytic germ
\(\sum_jc_je^{-a_jx}\) flat at \(x=0\).  Its first \(r\) Taylor equations form an invertible
Vandermonde system, so every \(c_j=0\).  In particular
\[
 J_S(x)=(-1)^{|S|+1}\prod_{p\in S}(p-1)x+O_S(x^2),       \tag{A39}
\]
and no nonempty finite aperture is in `DeningerExpSchwartz`.  A cutoff decomposes the vacuum into
a Meyer tail and one fixed compact collar; the collar inverse is exactly a smoothed Mertens sum.
This gives a dependency-closed domain classification, not source cancellation.

For the positive relation lane, every parity-flipping row proposal has an exact time-reversal
audit.  With \(Q(n,v)=w_nP(n,v)\), symmetric accepted conductance
\(C(n,v)=\min\{Q(n,v),Q(v,n)\}\), and total rejected mass \(R\),
\[
 R={1\over2}\sum_{n,v}|Q(n,v)-Q(v,n)|,
 \qquad |J|\le R.                                      \tag{A40}
\]
Thus strict-half closure by detailed balance requires edge log-likelihood defect
\(X^{-1/2+o(1)}\), not a qualitative or subpower comparison.  Current one-sided structured
\(E_3\) proposals have disjoint forward/reverse edge support, hence \(R\) equals full mass.
Surviving two-sided avenue must build reverse arithmetic support and the strict-half
Radon--Nikodym rate before `(A40)` is invoked, while retaining normalized seam flux.

Full proofs:
`../2-fully-proven/new_scientific_knowledge/route-e-deninger-vacuum-finite-dilation-fracture.md`
and
`../2-fully-proven/new_scientific_knowledge/route-e-opposite-parity-metropolis-rejection-law.md`.
No Lean source was edited or built during corpus refactor.

## 2026-08-11 Ramaré recombination and ternary recurrence splice

Exact integer reindexing changes the identity of the Gallagher residue. For
`k_n=omega_P(n)` and `c_P(n,m)=omega_P(gcd(n,m))`, the Ramaré bilinear polynomial is precisely the
Möbius polynomial on nonrough squarefree integers, while its square-multiple polynomial vanishes
termwise. The prime off-diagonal is

\[
 O_P(M,W)=\sum_{n,m}\mu(n)\mu(m)
 \left(1-{c_P(n,m)\over k_nk_m}\right)K_W(n,m).          \tag{A41}
\]

Its same-integer block collisions contribute

\[
 2W\sum_n(1-1/k_n)\le2WM,                               \tag{A42}
\]

and every coprime pair has coefficient exactly one. Hence prime spacing and common-prime incidence
cannot close the raw residue; the exact untouched analytic core is coprime Möbius near-diagonal
covariance. Correct sufficient target is affine `CWM+o(M^2)`, with diagonal constant retained.

The coprime sector has a new exact finite model. For a finite prime marker packet `Q`,

\[
 \mathcal T_Q(t)=\prod_{p\in Q}(1-p^{it}-p^{-it}).        \tag{A43}
\]

Its pointwise supremum `3^|Q|` is approached at arbitrarily large simultaneous antiscale
recurrences. Thus pointwise dissipation fails in the exact escape mode already identified by Route
E. In contrast, if `R_Q=prod_{p in Q}p`, then

\[
 \int_{-W}^{W}|\mathcal T_Q(t)|^2dt
 \le(2W+4R_Q^2(1+|Q|\log3))3^{|Q|}.                     \tag{A44}
\]

When `R_Q^2(1+|Q|)=O(W)`, near-maximal recurrence therefore has relative frequency measure
`O(3^{-|Q|})`. This is a finite-height, sign-retaining large-values law, not a pointwise
pretentious-distance restatement.

With actual reciprocal prime-dilation state weights `1,1/p,1/p`, the normalized alternating
character is

\[
 \Phi_Q(t)=\prod_{p\in Q}
 {1-p^{-1}e^{it\log p}-p^{-1}e^{-it\log p}\over1+2/p}.
\tag{A45}
\]

It still has cofinal antiscale recurrences of modulus one, but

\[
 \int_{-W}^{W}|\Phi_Q(t)|^2dt
 \le(2W+4R_Q^2(1+|Q|\log3))
 \prod_{p\in Q}{1+2/p^2\over(1+2/p)^2}.                \tag{A46}
\]

The product in `(A46)` is at most

\[
 \exp\left(2\sum_{p\in Q}p^{-2}-2\sum_{p\in Q}p^{-1}\right),
\tag{A47}
\]

so it vanishes with growing harmonic marker mass. Equations `(A45)`--`(A47)` prove critical
dissipation saturation with exact escape retained: uniform pointwise damping is false, while the
frequency weight of recurrence peaks tends to zero.

New hard target is
**TERNARY-MARKER-COFACTOR-FLATNESS-AND-RECURRENCE-SEAM**: tensor `(A44)` with actual
state-dependent rough-cofactor cutoffs and Ramaré/physical weights (using `(A46)` at reciprocal
marker density), obtaining `(A41)` with affine
strict-half budget plus unit column load and normalized prime-dilation recurrence seam. Turán rough
counts and Ramaré diagonal energy do not imply this statewise flatness.

Full proof:
`../2-fully-proven/new_scientific_knowledge/route-e-ramare-recombination-ternary-antiscale-law.md`.
No Lean source was edited or built.

## 2026-08-11 critical antiscale diffuse-codiagonal reduction

Read-only audit of the grown Fisher and antiscale corpus exposes a strictly weaker successor to
statewise cofactor flatness.

For every finite prime packet `Q`, exponent `r>0`, and

\[
 \Psi_{Q,r}(t)=\prod_{p\in Q}
   {1-p^{-r}e^{-it\log p}\over1+p^{-r}},
\]

the exact local deficit is

\[
 \left|{1-p^{-r}e^{-it\log p}\over1+p^{-r}}\right|^2
 =1-{p^{-r}|1+e^{it\log p}|^2\over(1+p^{-r})^2}.       \tag{A48}
\]

Thus simultaneous antiscale phase is the unique zero-dissipation torus point and is approached
cofinally. If `R_Q=prod Q`, separated divisor frequencies give

\[
 \int_{-W}^{W}|\Psi_{Q,r}(t)|^2dt
 \le\left(2W+4R_Q(1+|Q|\log2)\right)
 \prod_{p\in Q}{1+p^{-2r}\over(1+p^{-r})^2}.            \tag{A49}
\]

The product is at most

\[
 \exp\left(-\frac12\sum_{p\in Q}p^{-r}\right),         \tag{A50}
\]

so it vanishes for every `0<r<=1` along a prime exhaustion. This completes the exact critical
dissipation classification: no pointwise gap exists, but finite-height recurrence mass vanishes;
`r=1` is the sharp Euler boundary.

More importantly, sharp cofactor tensoring has an exact centered decomposition. For a finite
probability law `(w_s)`, a centered state family `sum_s w_s A_s=0`, and `|d_s|<=1`, define

\[
 O_w(A,d)=\sum_{s\ne q}w_sw_q(A_s+A_q)d_s,
 \qquad R_w(A,d)=\sum_sw_s^2A_sd_s.
\]

Then

\[
 \boxed{
 O_w(A,d)=\sum_sw_sA_sd_s-2R_w(A,d),
 \qquad
 |2R_w(A,d)|\le2w_{\max}\|A\|_{L^2(w)}.}               \tag{A51}
\]

For reciprocal ternary states `s=(a,b)`,
`w_(a,b)=1/(Z_Qab)` and `w_max=1/Z_Q<=exp(-sum_(p in Q)1/p)`. Therefore every arbitrary sharp
cofactor family splits into its state mean times `(A45)`, one centered off-diagonal reporter, and
an exponentially diffuse atomic collision. Uniform comparison of all `3^|Q|` cofactor blocks to
one common block is sufficient but no longer necessary.

The grown Lean corpus already proves the matching abstract operator bound. Any contraction-generated
joined reporter paired with the actual squarefree critical Fisher lower corner obeys

\[
 |\langle B,\operatorname{Reporter}\rangle_{HS}|^2
 \le\frac12\|B\|_{HS}^2,
\]

while limiting one-corner energy satisfies

\[
 \mathcal E_\downarrow(u)\le4(1-e^{-u}),
 \qquad \mathcal E_\downarrow(u)/u\to4.                 \tag{A52}
\]

Hence every genuinely contractive physical realization has abstract small-cutoff receiver
`sqrt(2(1-e^-u))<=sqrt(2u)`. This is a real square-root source law, not row/co-degree exponent
counting.

It does **not** yet prove `(A1)`: no theorem identifies the finite sharp Ramaré/unit-shell centered
reporter with this Fisher one-corner while preserving physical normalization. A vanishing source
expectation could erase the `sqrt(u)` gain. Revised hard target is

**CENTERED-COFACTOR-ONE-CORNER-CONTRACTION-AND-UNIT-SHELL-SEAM**: realize `(A51)` by a
source-predeclared `L^2` contraction for the actual finite physical atoms, compare its moving
corner energy to `(A52)` without inverse shell-probability loss, and carry the same reporter
through normalized zero/one-large-prime seam and exact signed recurrence.

Full proof and collision audit:
`../2-fully-proven/new_scientific_knowledge/route-e-critical-antiscale-diffuse-codiagonal-transfer-law.md`.
No Lean source was edited or built.

## 2026-08-11 Fisher gauge/clock mismatch and strict-right graph firewall

Further read-only audit of the grown Fisher corpus closes two false escapes from the centered
codiagonal frontier.

For finite reciprocal Euler law, signed unit state `psi`, centered log-energy variance `V`, and
critical Fisher connection `F`, exact energy is

\[
 \|F\|_{HS}^2=4(\sigma-1)^2V.
\tag{A53}
\]

Dividing by the Euler gauge gives

\[
 \|F/(\sigma-1)\|_{HS}^2=4V,
 \qquad
 |\langle(1-e)F e/(\sigma-1),\operatorname{Reporter}\rangle|
 \le\sqrt{2V}.
\tag{A54}
\]

At source-faithful tilt, `V=ell^2/2+O(ell log ell)`, so the gauge-neutralized universal bound grows
like `ell`. The apparent `sigma-1` saving is pure coordinate damping.

The corpus hard cutoff is not free: its clock is `(sigma-1) log n`. On the literal physical unit
shell,

\[
 u_{\mathrm{shell}}
 =(\sigma_x-1)\log(\sigma_x/x)+O(\sigma_x-1)
 ={2\log\ell\over\ell}+O(\ell^{-1}).
\tag{A55}
\]

Even granting a uniform finite-to-critical passage, the four-density one-corner profile at this
forced clock supplies only
`2 sqrt(log ell/ell)(1+o(1))`, not `X^(-1/2+o(1))`. Therefore the previous suggestion to choose
`u_X=X^(-1+o(1))` is invalid.

There is a genuine positive survivor. The new singular graph-normal source cancels the complete
Euler gauge and overlap exactly:

\[
 N_{\sigma,u}(\mathcal A_{\sigma,u}(x)-\mathcal A_{\sigma,u}(y))
 =\langle x-y,\eta_{\sigma,u}\rangle,
 \qquad \|\eta_{\sigma,u}\|\le1,
\tag{A56}
\]

for every complex inward node `Re u>=0`; the actual tangent simultaneously retains its completed
prime--Gamma Xi landing before normalization. This is exact coordinate covariance, but it is
strict-right. Its analytic node is `s=sigma+u(sigma-1)>1`. Reaching `Re s=1/2` forces `Re u<0`.
The Mellin-inversion temptation is also blocked exactly: realizing
`sum mu(n)n^(-s)` against normalized squarefree source requires observer squared norm

\[
 \mathcal Z_\sigma\sum_{n\ \mathrm{squarefree}}n^{\sigma-2\Re s},
\tag{A57}
\]

which diverges on `Re s=1/2`. Diffuse codiagonal recovery produces centered Fisher score, not this
raw scalar Möbius sum.

The former target
`CENTERED-COFACTOR-ONE-CORNER-CONTRACTION-AND-UNIT-SHELL-SEAM` is therefore sharpened to

**FINITE-PHYSICAL-CENTERED-CODIAGONAL-STRICT-HALF-AND-RECURRENCE-SEAM**:
construct strict-half corner energy or unit column capacity directly in the finite physical
relation, then retain normalized zero/one-large-prime seam flux and exact signed recurrence.
Universal Fisher cutoff tuning, graph-normal strict-right transport, statewise cofactor flatness,
prime spacing, and square-multiple control are no longer candidate producers.

Full proof and corpus trace:
`../2-fully-proven/new_scientific_knowledge/route-e-critical-antiscale-diffuse-codiagonal-transfer-law.md`.
Lean corpus was inspected read-only; no Lean source was edited or built.

## 2026-08-11 finite physical column-ANOVA identification

The abstract Fisher comparison is not needed for centered sharp columns. Let `rho_i` and `nu_i`
be literal pushed and positive target physical masses, with totals `P` and `N`. Set
`w_i=nu_i/N`, `r_i=rho_i/nu_i`, and `A_i=r_i-P/N`. Then `sum w_i A_i=0` and

\[
 \boxed{
 \chi^2(\rho\mid\nu)
 =N\sum_iw_iA_i^2+{(P-N)^2\over N}.}
\tag{A58}
\]

Thus centered physical codiagonal energy is exactly column-likelihood ANOVA

\[
 E_{\rm cent}=N\operatorname{Var}_w(r)
 =\chi^2(\rho\mid\nu)-{(P-N)^2\over N},
\tag{A59}
\]

not a universal critical-clock Fisher energy. For `N=X^(1+o(1))`, exact strict-half target is

\[
 E_{\rm cent}\le X^{o(1)}
 \quad\Longleftrightarrow\quad
 \operatorname{Var}_w(r)\le X^{-1+o(1)}.
\tag{A60}
\]

For every unit-modulus signed reporter `d`, Cauchy--Schwarz and centered codiagonal identity give

\[
 N|L_w(A,d)|\le\sqrt{NE_{\rm cent}},
 \qquad
 N|L_w(A,d)-O_w(A,d)|
 \le2w_{\max}\sqrt{NE_{\rm cent}}.
\tag{A61}
\]

Hence `(A60)` puts both centered score and atomic codiagonal correction at
`X^(1/2+o(1))`; maximum-state diffuseness is helpful but no additional power gap. Mean Euler
channel and moving seam remain separate.

Final hard target is now

**FINITE-PHYSICAL-COLUMN-ANOVA-STRICT-HALF-AND-SIGNED-RECURRENCE-SEAM**:
prove `(A60)` for one source-predeclared finite physical relation, then carry same likelihood-ratio
reporter through normalized zero/one-large-prime seam and exact alternating recurrence. This is
the non-circular part of global column chi-square; scalar term in `(A58)` is the signed mass
discrepancy itself and may not be assumed small.
