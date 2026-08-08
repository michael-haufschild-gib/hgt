# Route E critical half-density terminal-frame minimax law

- **ID:** `ROUTE-E-CRITICAL-HALF-DENSITY-TERMINAL-FRAME-MINIMAX-001`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED SHARP MINIMAX LAW]` / `[MASS-DIVERGENT SURVIVOR]`
- **Scientific status:** `[PAPER-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL PRIORITY UNCLAIMED]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** intentionally not started during corpus refactor

## 1. Result

Put (L=log X), and let

\[
 \mathcal P_X=\{p:\ X/e<p\le X\}.
\]

For (0<r\le1), define the moving antiscale frame

\[
 \mathcal F_{r,X}(t)
 =\sum_{p\in\mathcal P_X}p^{-r}|1+p^{it}|^2.             \tag{1}
\]

For (a\in[0,1)), set

\[
 W_a=\int_0^1e^{-av}\,dv,
 \qquad
 \mu_a={1\over W_a}\int_0^1v e^{-av}\,dv,
\]

and define the unnormalized terminal-position variance

\[
 \mathfrak v_a
 =\int_0^1e^{-av}(v-\mu_a)^2\,dv>0.                    \tag{2}
\]

The unconditional prime number theorem in the corpus implies that there is an absolute
constant (kappa>0) such that, for every fixed (0<r\le1),

\[
 \boxed{
 \lim_{X\to\infty}{L^3\over X^{1-r}}
 \inf_{|t|\le \exp(\kappa\sqrt L)}\mathcal F_{r,X}(t)
 =\pi^2\mathfrak v_{1-r}.}
                                                               \tag{3}
\]

In particular, with constants uniform for (0<r\le1),

\[
 c{X^{1-r}\over L^3}
 \le \inf_{|t|\le \exp(\kappa\sqrt L)}\mathcal F_{r,X}(t)
 \le C{X^{1-r}\over L^3}                                    \tag{4}
\]

for all sufficiently large (X).  At (r=1),
(mathfrak v_0=1/12), so the exact constant is (pi^2/12).

Every asymptotically minimizing frequency has, after passage to a sign subsequence,

\[
 t_X=\varepsilon\left({\pi\over L}
       +{\pi\mu_{1-r}\over L^2}\right)+o(L^{-2}),
 \qquad \varepsilon\in\{-1,1\}.                            \tag{5}
\]

Thus the familiar resonance (pi/L) gives the correct order but not the sharp constant.  The
unique second-order correction centers terminal log-position before squaring.

## 2. Source half-density corollary

The RHTower corpus identifies the reflected Deninger half-slope and Möbius--Fisher damping as

\[
 \kappa_p=p^{-1/2},
 \qquad
 d_p={\kappa_p\over1+\kappa_p^2}
     ={p^{-1/2}\over1+p^{-1}}.                              \tag{6}
\]

For fixed (0<q\le2), define

\[
 \mathcal H_{q,X}(t)
 =\sum_{p\in\mathcal P_X}d_p^q|1+p^{it}|^2.                \tag{7}
\]

Then `(3)` and the terminal uniformity

\[
 d_p^q=p^{-q/2}(1+O_q(X^{-1}))
 \qquad(p\in\mathcal P_X)                                  \tag{8}
\]

give the exact source-selected law

\[
 \boxed{
 \lim_{X\to\infty}{L^3\over X^{1-q/2}}
 \inf_{|t|\le \exp(\kappa\sqrt L)}\mathcal H_{q,X}(t)
 =\pi^2\mathfrak v_{1-q/2}.}
                                                               \tag{9}
\]

Two endpoints have different Route E meanings:

\[
 \inf_t\sum_{p\in\mathcal P_X}d_p|1+p^{it}|^2
 \sim \pi^2\mathfrak v_{1/2}{\sqrt X\over L^3},            \tag{10}
\]

whereas

\[
 \inf_t\sum_{p\in\mathcal P_X}d_p^2|1+p^{it}|^2
 \sim {\pi^2\over12L^3}.                                   \tag{11}
\]

The half-density level (q=1) retains square-root physical power.  The Fisher/Hilbert metric
level (q=2) retains no positive power of (X).  More generally, the exact power is
(X^{1-q/2}): squaring the source half-density is the sharp power-loss threshold.

## 3. Prime number theorem reduction

The corpus proves

\[
 \vartheta(y)=y+E(y),
 \qquad
 |E(y)|\le C_0y\exp(-c_0\sqrt{\log y})                    \tag{12}
\]

for all sufficiently large (y).  This is the theorem
`chebyshevTheta_sub_id_isBigO` in
`formal/GaloisForLFunctions/RHTower/Sieve/ChebyshevThetaBigO.lean`; the expanded sieve stack also
contains the corresponding prime-counting theorem and an explicit Chebyshev rate.  Only `(12)`
is used here.

Let

\[
 A_t(y)=|1+y^{it}|^2=2+2\cos(t\log y),
 \qquad
 h_{r,t}(y)={y^{-r}A_t(y)\over\log y}.                     \tag{13}
\]

Since the jump of \(\vartheta\) at a prime \(p\) is \(\log p\), Stieltjes summation gives exactly,
with the chosen half-open endpoint convention,

\[
 \mathcal F_{r,X}(t)=\int_{(X/e,X]}h_{r,t}(y)\,d\vartheta(y). \tag{14}
\]

On this interval, uniformly for (0<r\le1),

\[
 |h_{r,t}(y)|\ll {X^{-r}\over L},
 \qquad
 |h'_{r,t}(y)|\ll{(1+|t|)X^{-r-1}\over L}.                \tag{15}
\]

Integration by parts in `(14)`, followed by `(12)`, therefore gives constants (c_1,C_1>0)
such that

\[
 \mathcal F_{r,X}(t)
 =\int_{X/e}^{X}{y^{-r}A_t(y)\over\log y}\,dy
 +O\left({(1+|t|)X^{1-r}\over L}e^{-c_1\sqrt L}\right).   \tag{16}
\]

Indeed, each boundary term is
(O(X^{1-r}e^{-c_1\sqrt L}/L)), while the integral involving (E h') is bounded by interval
length (X) times
(O((1+|t|)X^{-r}e^{-c_1\sqrt L}/L)).  This accounts for every term; no short-interval PNT is
assumed.

Choose (0<\kappa<c_1).  Uniformly on
(|t|\le\exp(\kappa\sqrt L)), the error in `(16)`, after multiplication by
(L^3/X^{1-r}), is

\[
 O\left(L^2e^{-(c_1-\kappa)\sqrt L}\right)=o(1).           \tag{17}
\]

This is why the theorem reaches a subexponential frequency window.  It contains every fixed,
polylogarithmic, and usual Gamma-effective frequency range, but stops before the unconstrained
far-future Kronecker recurrences of a finite prime set.

## 4. Continuous terminal-band problem

Put (a=1-r) and substitute (y=Xe^{-v}) in the main term of `(16)`.  It becomes

\[
 M_{r,X}(t)
 =X^a\int_0^1 {e^{-av}\over L-v}
       |1+e^{it(L-v)}|^2\,dv.                              \tag{18}
\]

Define

\[
 I_{a,L}(t)=\int_0^1e^{-av}|1+e^{it(L-v)}|^2\,dv.          \tag{19}
\]

Because (L/(L-v)=1+O(L^{-1})) uniformly on (0\le v\le1), positivity gives

\[
 {L^3\over X^a}M_{r,X}(t)
 =L^2I_{a,L}(t)(1+O(L^{-1})).                              \tag{20}
\]

It remains to solve the minimax problem for `(19)`.

## 5. A global localization lemma

Discarding the positive weight costs at most (e^{-1}).  The exact unweighted integral is

\[
 \begin{aligned}
 I_{0,L}(t)
 &=\int_0^1|1+e^{it(L-v)}|^2\,dv\\
 &=2+4{\sin(t/2)\over t}\cos(t(L-1/2))                    \tag{21}
 \end{aligned}
\]

for (t\ne0), with the continuous value at zero.

For (0<|t|\le1), the elementary Taylor bound

\[
 {\sin(|t|/2)\over |t|/2}\le1-{t^2\over28}
\]

implies

\[
 I_{0,L}(t)\ge {t^2\over14}.                              \tag{22}
\]

For (|t|\ge1), `(21)` gives a positive absolute lower bound.  On
(1\le|t|\le2\pi), use monotonicity of (sin u/u) on ((0,\pi)); beyond (2\pi), use
(|\sin(t/2)|\le1).  Consequently there is (delta_0>0) such that

\[
 I_{a,L}(t)\ge e^{-1}\delta_0\qquad(|t|\ge1),             \tag{23}
\]

uniformly in (a\in[0,1)) and (L).

Equations `(22)`--`(23)` show that any sequence satisfying
(L^2I_{a,L}(t_L)=O(1)) must obey

\[
 t_L=O(L^{-1}).                                           \tag{24}
\]

Write (u_L=t_LL).  After passage to a subsequence, (u_L\to u_0).  If
(L^2I_{a,L}(t_L)) is bounded, dominated convergence in `(19)` gives

\[
 W_a|1+e^{iu_0}|^2=0,
\]

so

\[
 u_0=(2k+1)\pi                                             \tag{25}
\]

for some integer (k).  This proves that every bounded-energy sequence is forced into an odd
terminal resonance; no other common-phase escape survives in the PNT-controlled window.

## 6. Second-order minimization and exact constant

Set (Delta_L=u_L-u_0).  Since (u_L) is bounded, the phase relative to the odd resonance is

\[
 t_L(L-v)-u_0=\Delta_L-{u_Lv\over L}.                     \tag{26}
\]

For sufficiently large (L), the chord lower bound near zero and the weighted variance identity
give

\[
 \begin{aligned}
 I_{a,L}(t_L)
 &\gg\int_0^1e^{-av}
       \left(\Delta_L-{u_Lv\over L}\right)^2\,dv\\
 &=W_a\left(\Delta_L-{u_L\mu_a\over L}\right)^2
   +{u_L^2\over L^2}\mathfrak v_a.                       \tag{27}
 \end{aligned}
\]

Hence bounded (L^2I_{a,L}(t_L)) forces
(Delta_L=O(L^{-1})).  Put (b_L=L\Delta_L), pass to a further subsequence with
(b_L\to b), and multiply `(26)` by (L).  Uniform small-angle expansion now yields

\[
 \lim L^2I_{a,L}(t_L)
 =\int_0^1e^{-av}(b-u_0v)^2\,dv
 =W_a(b-u_0\mu_a)^2+u_0^2\mathfrak v_a.                  \tag{28}
\]

The right side is at least (u_0^2\mathfrak v_a\), and `(25)` gives

\[
 \liminf L^2I_{a,L}(t_L)\ge\pi^2\mathfrak v_a.           \tag{29}
\]

For the reverse inequality, choose

\[
 t_L^*={\pi\over L}+{\pi\mu_a\over L^2}.                 \tag{30}
\]

Then uniformly for (0\le v\le1),

\[
 L\bigl(t_L^*(L-v)-\pi\bigr)
 =\pi(\mu_a-v)+O(L^{-1}),                                 \tag{31}
\]

and therefore

\[
 \lim L^2I_{a,L}(t_L^*)
 =\pi^2\int_0^1e^{-av}(v-\mu_a)^2\,dv
 =\pi^2\mathfrak v_a.                                    \tag{32}
\]

Equations `(16)`--`(20)`, `(29)`, and `(32)` prove `(3)`.  Equality conditions in `(28)` force
(|u_0|=\pi) and (b=u_0\mu_a), proving `(5)`.

The uniform two-sided estimate `(4)` also follows directly.  The lower bound is supplied by
`(22)`--`(23)` and the compact odd-resonance analysis; the upper bound already follows from the
cruder choice (t=\pi/L), the chord estimate
(|1+p^{it}|\le\pi/L), and

\[
 \sum_{X/e<p\le X}p^{-r}\ll {X^{1-r}\over L},            \tag{33}
\]

uniformly for (0<r\le1).

## 7. Stability under the source damping

From `(6)`, for fixed (q\in(0,2]),

\[
 0\le p^{-q/2}-d_p^q\ll_q p^{-q/2-1}.                    \tag{34}
\]

Thus, uniformly in (t),

\[
 \left|\mathcal F_{q/2,X}(t)-\mathcal H_{q,X}(t)\right|
 \ll_q\sum_{X/e<p\le X}p^{-q/2-1}
 \ll_q {X^{-q/2}\over L}.                                \tag{35}
\]

After multiplying by (L^3/X^{1-q/2}), the last expression is
(O_q(L^2/X)=o(1)).  This proves `(9)` without changing the minimizing scale or constant.

## 8. Sharp bounded-reporter firewall

The threshold in `(10)`--`(11)` cannot be repaired by replacing a diagonal Fisher reader with a
uniformly bounded non-diagonal one.  On the finite terminal prime space, use the source Fisher
inner product

\[
 \langle z,w\rangle_{F,X}
 =\sum_{p\in\mathcal P_X}d_p^2\overline{z_p}w_p,          \tag{36}
\]

and put (z_X(t)_p=1+p^{it}).  For every bounded operator (B_X) on this Hilbert space,

\[
 |\langle z_X(t),B_Xz_X(t)\rangle_{F,X}|
 \le\|B_X\|\mathcal H_{2,X}(t).                          \tag{37}
\]

At the explicit terminal resonance (t_0=\pi/L), `(4)` and the chord upper bound give

\[
 \mathcal H_{1,X}(t_0)\ge c{\sqrt X\over L^3},
 \qquad
 \mathcal H_{2,X}(t_0)\le {C\over L^3}.                  \tag{38}
\]

Consequently, if a possibly aperture-dependent, non-diagonal reporter is coefficient-faithful to
the half-density frame even at this one physical frequency, in the sense that

\[
 |\langle z_X(t_0),B_Xz_X(t_0)\rangle_{F,X}|
 \ge c_0\mathcal H_{1,X}(t_0),                            \tag{39}
\]

then

\[
 \boxed{\|B_X\|\ge c_1\sqrt X.}                          \tag{40}
\]

This lower bound is sharp.  The unique positive diagonal multiplier (R_X) satisfying

\[
 \langle z,R_Xz\rangle_{F,X}
 =\sum_{p\in\mathcal P_X}d_p|z_p|^2
\]

has diagonal entries (d_p^{-1}=p^{1/2}+p^{-1/2}), hence
(|R_X|\asymp\sqrt X).  This is exactly the reflected WKB recovery already identified
locally in `DeningerMobiusCriticalWKBSeam.lean`; `(40)` proves that its cofinal singularity has the
minimal possible order for any coefficient-faithful Fisher-to-half-density reporter.

Thus no uniformly bounded positive, indefinite, diagonal, or non-diagonal operator on the
critical Fisher Hilbert completion can expose the square-root terminal frame.  A viable transfer
must be a genuinely unbounded graph with canonical domain/renormalization, or must act on signed
half-densities before Hilbert completion.

## 9. Conjecture--proof--failure loop

### Loop A: critical frame may require RH

`[CONJECTURE]` A uniform (p^{-1/2}) terminal-frame floor might require cancellation information
equivalent to RH.

`[FALSIFIED]` The summands are nonnegative.  Exponential-error PNT plus one continuous
terminal-band minimization proves a much stronger subexponential-frequency floor unconditionally.

### Loop B: inverse-square resonance only gives an upper obstruction

`[CONJECTURE]` The existing bound at (t=\pi/L) may be far from the actual minimax scale.

`[FALSIFIED]` The global localization lemma and second-order odd-resonance expansion prove the
matching lower bound and exact constant.  The inverse-square law is sharp for every
(p^{-r}), (0<r\le1), terminal frame.

### Loop C: canonical Fisher metric supplies square-root coercivity

`[CONJECTURE]` The already formalized local Fisher metric (d_p^2) may itself carry the missing
Route E power.

`[FALSIFIED]` Equation `(11)` is only (L^{-3}).  The square-root scale occurs one categorical
level earlier, at the half-density coefficient (d_p), as `(10)` shows.

### Loop D: half-density minimax closes Route E

`[CONJECTURE]` Equation `(10)` alone proves the Route E source estimate.

`[FALSIFIED]` The frame is a positive common-phase diagonal form.  It contains neither literal
Gibbs batch prefixes nor the alternating finite-volume determinant.  No proved map sends its
energy into (D_{\rm anti}), (mathcal V_+), or (mathcal V_-) while retaining recurrence
weights and prime-dilation intervals.  Calling `(10)` the missing accumulation theorem would be
theatre.

### Loop E: non-diagonal Hilbert reporter evades the square threshold

`[CONJECTURE]` Cross-prime matrix entries in a uniformly bounded Fisher-space reporter may lift
the harmonic (d_p^2) norm to the half-density (d_p) scale.

`[FALSIFIED]` Cauchy--Schwarz and the operator norm give `(37)` without any diagonal, positivity,
or kernel-summability assumption.  Equations `(38)`--`(40)` force sharp
(\sqrt X)-divergence of every coefficient-faithful reporter.

## 10. New universal interpretation

The recurrent terminal obstruction is not merely “insufficient prime mass.”  It is a categorical
order-of-operations law:

\[
 \boxed{
 \text{half-density transverse transfer first}
 \quad\text{or}\quad
 \text{squaring destroys physical power}.}
                                                               \tag{41}
\]

At the source-selected damping (d_p\asymp p^{-1/2}), terminal resonance costs exactly two
logarithms but leaves (sqrt X) mass.  Passing first to the Fisher/Hilbert metric replaces (d_p)
by (d_p^2\asymp p^{-1}); the same unavoidable inverse-square resonance then leaves only
(L^{-3}).  This explains why positive Hilbert-space completions repeatedly hit the harmonic
ceiling even though the underlying WKB half-density already has physical-power mass.

The result proves that the reflected WKB half-density is analytically strong enough to survive
all common Mellin phases in a frequency window far larger than Gamma requires.  It does **not**
prove that this half-density defines an admissible Route E energy.  The missing source theorem is
now narrower:

> **PRE-NORM-WKB-TO-GIBBS-TRANSVERSE-TRANSFER.**  Construct from the literal ordinary-integer
> Gibbs/co-Poisson source a signed, pre-Hilbert transfer of the canonical coefficients (d_p)
> into (D_{\rm anti}) or a within-parity variance before they are squared to (d_p^2), retaining
> recurrence weights, prime-dilation intervals, alternating finite-volume signs, and moving
> cutoff correlation.

Such a transfer would have the required (sqrt X/L^3=X^{1/2-o(1)}) analytic carrier.  Its
existence, admissibility, and normalization remain unproved.  Route E and RH remain open.

## 11. Relation to existing no-go theorems

1. There is no conflict with static all-prime recurrence.  The aperture moves with (X), and
   `(3)` restricts to (|t|\le e^{\kappa\sqrt L}).  A finite prime set still has arbitrarily late
   Kronecker returns.
2. There is no conflict with moving terminal-kernel resonance.  For the diagonal kernel
   (K_{pp}=p^{-r}), its entrywise mass is
   (asymp X^{1-r}/L); the inverse-square factor (L^{-2}) predicts exactly `(4)`.
3. There is no conflict with critical-dissipation saturation failure.  That theorem concerns a
   multiplicative Euler-product reporter and proves divergence for (0<r<1).  The present theorem
   concerns an additive positive terminal frame and determines its minimax size.
4. `MobiusCriticalPrimeBlockGammaBand.lean` controls a multiplicative critical prime-block
   product.  It does not contain the additive minimax law `(3)` or the half-density/Fisher
   threshold `(9)`.

## 12. Novelty and formalization notes

Internal searches across Route E paper cards and the HTGeometry, RHTower, HilbertMetric, and
QuantumAlg Lean trees found the upper inverse-square resonance law, harmonic first-trace frame,
critical product resonance, and reflected WKB/Fisher identities, but not the matching additive
minimax lower bound, exact variance constant, optimizer localization, or (q=2) threshold.

Broad external arXiv searches were performed during the parent Halász/Route E audit.  No external
priority claim is made here.  Scientific status is project-local `[PAPER-PROVED NEW KNOWLEDGE]`
until a dedicated publication-level collision audit is completed.

Future Lean formalization should reuse, not rebuild:

- `RHTower/Sieve/ChebyshevThetaBigO.lean` for `(12)`;
- `RHTower/Sieve/PrimeCountingBigO.lean` for terminal prime-mass corollaries;
- `RHTower/RouteEMovingTerminalKernelResonance.lean` for the resonance chord bound;
- `RHTower/DeningerMobiusCriticalWKBSeam.lean` for `(6)`;
- existing Stieltjes/Abel summation infrastructure in the sieve stack.

Required new formal blocks are a weighted prime Stieltjes estimate uniform in (t), the exact
integral identity `(21)`, odd-resonance localization, and the weighted-variance minimization
`(28)`.  No Lean file is created while the corpus is being refactored.
