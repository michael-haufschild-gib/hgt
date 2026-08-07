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
