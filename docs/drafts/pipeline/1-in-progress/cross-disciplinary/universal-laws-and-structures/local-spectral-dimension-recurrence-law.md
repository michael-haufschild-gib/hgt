# Local spectral-dimension recurrence law

- **ID:** `local-spectral-dimension-recurrence-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL MINIMAX RECURRENCE ASYMPTOTIC
- **Labels:** `[PAPER-PROOF CANDIDATE] [EXTERNAL PRIORITY COLLISION] [BRIDGE]`
- **Parent:** `recurrence-relation-lattice-universal-law`
- **Date opened:** 2026-07-31

## Public sentence

> The accuracy dependence of a local quantum return clock determines the
> dimension of the spectrum visible to that observer.

## Priority correction — 2026-07-31

The abstract \(N_p\)-to-small-target exponent is not headline novelty.
Rozovsky's fast-weight small-deviation theorem already gives, for independent
nonnegative coordinate losses with lower-tail exponent \(1/2\),
\[
 -\log {\mathbb P}\!\left(\sum_jp_jX_j<\eta\right)
 \sim\frac{C}{2(\nu+1)}
 \bigl(\log(1/\eta)\bigr)^{\nu+1}
\]
when the inverse weight count is asymptotic to \(C(\log u)^\nu\).
Aurzada proves the exact \(\nu=1\) exponentially weighted case.  The
projective quantum target and deterministic minimax squeeze below remain
useful recurrence infrastructure, but the exponent and coefficient are
classical small-deviation geometry.

The novel research target exposed by this collision is the Anderson
transfer itself: prove the local log-weight counting law, with explicit
constant, for a named random Schrödinger operator.  That problem is tracked
separately in `anderson-local-spectral-depth-law`.

## Frozen conjecture

Let \(p=(p_j)_{j\ge0}\) be a strictly positive probability sequence.  Put
\[
 a_j=-\log p_j,\qquad
 N_p(L)=\#\{j:a_j\le L\}.
\]
Assume that for some \(C>0\) and \(\nu>0\),
\[
 N_p(L)\sim C L^\nu\qquad(L\to\infty).
 \tag{1}
\]
For \(0<\eta<1\), define the least universal local recurrence deadline
\[
 T_p(\eta)=\min\left\{N\ge1:
 \begin{array}{l}
 \text{for every }\omega\in\mathbb R^{\mathbb N}
 \text{ there is }1\le n\le N\\[1mm]
 \displaystyle
 \left|\sum_{j=0}^{\infty}p_j e^{in\omega_j}\right|
 \ge1-\eta
 \end{array}\right\}.
 \tag{2}
\]
Then
\[
 \boxed{
 \log T_p(\eta)\sim
 \frac{C}{2(\nu+1)}
 \bigl(\log(1/\eta)\bigr)^{\nu+1}}
 \qquad(\eta\downarrow0).
 \tag{3}
\]
In particular,
\[
 \boxed{
 \nu=
 \lim_{\eta\downarrow0}
 \frac{\log\log T_p(\eta)}
      {\log\log(1/\eta)}-1.}
 \tag{4}
\]

There is also a population version.  Give
\(\mathbb T^{\mathbb N}\) product Haar measure and let
\(T_{p,q}(\eta)\) be the least \(N\) for which the set of phase packets
having a return by some \(1\le n\le N\) has Haar measure at least
\(q\), where \(0<q<1\) is fixed.  Then the sharper candidate law is
\[
 \boxed{
 \log T_{p,q}(\eta)\sim\log T_p(\eta)\sim
 {\cal H}_p(\log(1/\eta))}
 \qquad(\eta\downarrow0).
 \tag{4a}
\]
Thus the leading law is not an artefact of one adversarial spectrum:
every fixed nonzero phase-population quantile has the same asymptotic
clock as the worst packet.

The candidate invariant \(N_p\) is intrinsic to the observer's local
spectral measure.  It does not use ambient Hilbert-space dimension or a
chosen localization centre.

## Bounded-density actual-system extension

Let \((Z_j)_{j\ge0}\) be independent circle-valued random variables whose
densities \(f_j\) with respect to normalized Haar measure obey the uniform
bound
\[
 \|f_j\|_\infty\le B<\infty.
 \tag{4b0}
\]
For one sampled infinite phase packet define its actual first positive
stroboscopic return
\[
 \tau_{p,Z}(\eta)=
 \min\left\{n\ge1:
 \left|\sum_{j=0}^\infty p_j Z_j^n\right|\ge1-\eta\right\}.
 \tag{4b1}
\]
Then the dependency-closed paper proof gives, almost surely,
\[
 \boxed{
 \log\tau_{p,Z}(\eta)
 \sim {\cal H}_p(\log(1/\eta))
 \sim\frac{C}{2(\nu+1)}
 \bigl(\log(1/\eta)\bigr)^{\nu+1}.}
 \tag{4b2}
\]

Indeed, the \(n\)-th power map sends \(f_j\) to the average of \(f_j\)
over its \(n\) preimages, so the pushed-forward density is still bounded by
\(B\).  On a head of \(M=N_p(2L)\) coordinates, the joint density is at
most \(B^M\) relative to product Haar measure.  The early-hit bound (23)
therefore acquires only the factor \(B^M\):
\[
 {\mathbb P}(\tau_{p,Z}(e^{-L})\le N)
 \le
 N B^{N_p(2L)}N_p(2L)
 \exp\left[\frac\pi4-{\cal H}_p(L)+\frac L2\right].
 \tag{4b3}
\]
Because \(N_p(2L)=O(L^\nu)=o({\cal H}_p(L))\), this remains summable on
integer \(L\) when
\(N=\lfloor\exp((1-\epsilon){\cal H}_p(L))\rfloor\).
Borel--Cantelli supplies the almost-sure lower bound; the deterministic
universal recurrence theorem supplies the matching upper bound.  No
independence between different return times is used.

Thus exact uniform eigenphase disorder is not necessary.  Independence and
a uniform finite-density bound are enough for the same leading law.

The sharp hypothesis is weaker.  It is enough that the joint law on the
active head \(A_{2L}\) have density at most \(K(L)\) relative to finite
product Haar, uniformly after every positive integer power map, with
\[
 \log K(L)=o({\cal H}_p(L)).
 \tag{4b4}
\]
Then (4b3) holds with \(K(L)\) in place of \(B^{N_p(2L)}\).  This permits
correlated phase packets; bounded independent marginals are only one
sufficient construction.

The asymptotic is also genuinely post-exit.  Since \(p_0,p_1>0\), equality
\(\left|\sum_jp_jZ_j\right|=1\) forces \(Z_0=Z_1\).  Independence and absolute
continuity give probability zero to that event.  Almost surely
\[
 \eta_0=1-\left|\sum_jp_jZ_j\right|>0,
 \tag{4b5}
\]
so every return with \(\eta<\eta_0\) occurs after a demonstrated exit at
time \(1\).

## Exact Anderson-locality interface

Let the modes have localization centres \(y_j\) in a proper metric space,
fix an observation site \(x\), and write
\[
 r_j=d(x,y_j),\qquad a_j(x)=-\log p_j(x).
\]
Assume the centre-counting law
\[
 M_x(R)=\#\{j:r_j\le R\}\sim\kappa_xR^d
 \tag{4b}
\]
and the two-sided local log-weight law
\[
 \sup_{r_j\ge R}
 \left|\frac{a_j(x)}{r_j}-\lambda_x\right|
 \longrightarrow0,
 \qquad \lambda_x>0.
 \tag{4c}
\]
Then
\[
 N_{p(x)}(L)\sim
 \kappa_x\lambda_x^{-d}L^d,
 \tag{4d}
\]
and hence
\[
 \boxed{
 \log T_{p(x)}(\eta)\sim
 \frac{\kappa_x\lambda_x^{-d}}{2(d+1)}
 \bigl(\log(1/\eta)\bigr)^{d+1}.}
 \tag{4e}
\]
The same leading law holds for every fixed Haar quantile.

If eigenfunction amplitudes have local decay
\(|\psi_j(x)|=\exp[-r_j/\xi_x+o(r_j)]\), then
\(p_j(x)=|\psi_j(x)|^2\) has
\(\lambda_x=2/\xi_x\).  In that case the leading coefficient in (4e)
is
\[
 \frac{\kappa_x}{2(d+1)}
 \left(\frac{\xi_x}{2}\right)^d.
 \tag{4f}
\]

Equations (4b)--(4c) are a deterministic two-sided profile, not a claim
that ordinary Anderson dynamical localization already proves them.
More precisely, a uniform bound
\(p_j(x)\le A e^{-\lambda r_j}\), together with
\(M_x(R)=O(R^d)\), gives only \(N_{p(x)}(L)=O(L^d)\).
It cannot give equality: arbitrarily small local eigenfunction weights can
remove nominally nearby modes from every finite-resolution observation.

## Why this is the missing merger

For a site state \(x\) in a pure-point Hamiltonian,
\[
 p_j(x)=\langle x,\Pi_jx\rangle
\]
is exactly the local spectral weight and
\[
 \left|\sum_jp_j(x)e^{-itE_j}\right|^2
\]
is its survival probability.  Exponentially localized eigenmodes with
polynomial spatial volume growth naturally give polynomial growth of
\(N_{p(x)}(L)\).  Under a two-sided regular local spectral profile, the
exponent \(\nu\) is the spatial localization dimension.  Equation (4) then
states that the local recurrence clock carries a universal
``space dimension plus one'' exponent.

This reorganizes three layers:

1. the projective recurrence minimax law supplies the universal clock;
2. localization controls the distribution of visible spectral weights;
3. for one fixed deterministic Hamiltonian, the relation lattice determines
   the smaller phase orbit and must be analysed before a Haar lower law can
   be transferred.

Consequently, \(T_p\) is a universal minimax deadline, not the measured
return time of every fixed physical Hamiltonian.  The Haar-quantile statement
is a population theorem.  An actual-system law requires an additional
phase-distribution theorem, supplied exactly by the iid-Haar spectrum in the
Blaschke-dressed atomic model.

The extra \(+1\) has a structural origin: \(N_p(L)\) counts visible phase
coordinates, while synchronizing each active coordinate to fidelity
resolution \(\eta\) costs one further logarithmic scale.

## Exact analytic mechanism

Define the infinite reverse-water entropy at logarithmic level \(L\) by
\[
 {\cal H}_p(L)
 =\frac12\sum_j(L-a_j)_+.
 \tag{5}
\]
Counting by layers gives the exact identity
\[
 \boxed{
 {\cal H}_p(L)=\frac12\int_0^L N_p(u)\,du.}
 \tag{6}
\]
Thus (1) implies
\[
 {\cal H}_p(L)\sim
 \frac{C}{2(\nu+1)}L^{\nu+1}.
 \tag{7}
\]

At water level \(\lambda=e^L\), the total distortion is
\[
 \eta_p(L)
 =
 e^{-L}N_p(L)+
 \sum_{a_j>L}e^{-a_j}.
 \tag{8}
\]
Regular variation gives
\[
 \eta_p(L)\sim C e^{-L}L^\nu,\qquad
 L\sim\log(1/\eta_p(L)).
 \tag{9}
\]
The conjecture is therefore reduced to the exact infinite-packet minimax
squeeze
\[
 \log T_p(\eta)
 =
 {\cal H}_p(\log(1/\eta))+o\!\left(
 {\cal H}_p(\log(1/\eta))\right).
 \tag{10}
\]

## Internal frontier

- `[CORPUS]` Finite weighted minimax recurrence is squeezed around exact
  reverse-water entropy by
  `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich` in
  `ProjectiveWeightedFloquetRecurrence.lean`.
- `[CORPUS]` The upper rounding remainder can depend only on selected active
  coordinates by
  `exists_projectiveWeightedCoherence_selectedSupport_recurrence` in
  `ProjectiveWeightedHaarQuantileActiveSupport.lean`.
- `[CORPUS]` The matching Haar population lower bound is
  `measure_projectiveWeightedCoherence_hitThrough_le` in the same module.
- `[CORPUS]` Countably infinite pure-point survival recurrence with a finite
  visible head and certified tail is proved in
  `SummableLocalizedSurvivalRecurrenceLaw.lean`.
- `[CORPUS]` Exponential localization and polynomial localization volume
  already give the upper scale
  \(\log T=O((\log(1/\eta))^{\nu+1})\) in
  `FiniteAndersonLocalizedResolutionScaleLaw.lean`.
- `[LOCAL-RESEARCH]` No current theorem supplies the matching localized
  lower bound or reconstructs \(\nu\) from the recurrence clock.

## External frontier

- `[LITERATURE]` Campos Venuti, *The recurrence time in quantum mechanics*,
  arXiv:1509.04352, estimates average recurrence density for rationally
  independent generic spectra, primarily through a Gaussian approximation
  and inverse-purity effective dimension.
- `[LITERATURE]` Anikushin, arXiv:1710.03043, studies inclusion lengths of
  quasiperiodic almost-periodic functions through Diophantine dimension.
- `[LITERATURE]` Freedman, arXiv:2407.16055, relates detectable recurrence
  to low-dimensional, low-volume orbit closure.
- `[LITERATURE]` Kotowski--Oszmaniec,
  arXiv:2601.10409v2, prove
  \[
  t_{\rm rec}(\varepsilon)\le t_{\rm exit}(\varepsilon)
  (2\pi/\varepsilon+1)^{d-1},
  \]
  a generic packing-number theorem, random-Hamiltonian matching lower
  scaling, and an effective-support refinement.  This externally subsumes
  the finite uniform half-entropy exponent and kills any headline based
  only on covering numbers, support size, or the \(d/2\) fidelity exponent.
- `[EXTERNAL PRIORITY COLLISION]` Rozovsky, *Small deviation probabilities
  of weighted sums with fast decreasing weights*, Probability and
  Mathematical Statistics **35** (2015), 161--178, supplies the same
  regularly varying inverse-weight integral and leading coefficient for
  independent coordinate losses.  Aurzada, arXiv:0711.2576, supplies the
  exact exponentially weighted \(\nu=1\) case.
- `[OPEN NOVEL RESIDUE]` None of the audited sources proves the local
  log-weight counting law for a standard Anderson Hamiltonian.  Existing
  eigensystem localization and localization-centre statistics supply upper
  envelopes and centre density, not the two-sided fixed-observer amplitude
  asymptotic required by (4c).

## Hostile falsifiers

1. A regularly varying \(N_p\) for which the infinite minimax deadline is
   not asymptotic to the reverse-water entropy.
2. Tail normalization changing the leading constant in (3).
3. A primary source proving an equivalent weight-counting recurrence law.
   This falsifier has fired for the small-deviation part: Rozovsky is a
   direct priority collision.
4. An Anderson-localized local spectral measure for which the claimed
   spatial identification of \(\nu\) is asserted without a two-sided
   regularity theorem.
5. Dependence of the leading recurrence exponent on arithmetic relations
   in a theorem quantified over every phase packet.

## Dependency-closed paper proof candidate

Put
\[
 \tau_p(L)=\sum_{a_j>L}e^{-a_j}.
\]
Regular variation first gives
\[
 \tau_p(L)=o\!\left(e^{-L}N_p(L)\right).
 \tag{11}
\]
Indeed, decompose the Stieltjes integral
\(\int_{(L,\infty)}e^{-u}\,dN_p(u)\) into unit shells.  For every fixed
number of shells,
\[
 N_p(L+k+1)-N_p(L+k)=o(N_p(L))
\]
by (1).  The remaining shells are uniformly dominated, after division by
\(N_p(L)\), by an exponentially summable sequence times a polynomial,
using the standard regular-variation bound
\[
 \frac{N_p(L+k+1)}{N_p(L)}
 \le C_\epsilon
 \left(1+\frac{k+1}{L}\right)^{\nu+\epsilon}.
\]
First send \(L\) to infinity for the fixed block and then send its length
to infinity.  This proves (11).

The layer identity (6) follows from Tonelli:
\[
 \sum_j(L-a_j)_+
 =\sum_j\int_0^L{\bf1}_{\{a_j\le u\}}\,du
 =\int_0^LN_p(u)\,du.
\]
Integration of (1) then proves (7).

### Universal upper bound

Write \(L=\log(1/\eta)\) and choose
\[
 U=L+b\log L,\qquad b>\nu.
\]
Let \(A_U=\{j:a_j\le U\}\), \(M_U=|A_U|=N_p(U)\), and choose a pivot
\(k\in A_U\).  For \(j\in A_U\setminus\{k\}\), put
\[
 x_j=p_je^U\ge1,\qquad
 Q_j=\left\lceil\pi\sqrt{2x_j}\right\rceil.
\]
An anisotropic projective pigeonhole argument applied to the first
\(\prod_{j\ne k}Q_j+1\) powers gives, for every phase packet, an integer
\[
 1\le n\le\prod_{j\in A_U\setminus\{k\}}Q_j
 \tag{12}
\]
whose active relative phase errors satisfy
\(|\theta_j|\le2\pi/Q_j\).
After removal of the pivot phase,
\[
 \begin{aligned}
 1-\left|\sum_jp_je^{in\omega_j}\right|
 &\le
 \sum_{j\in A_U}p_j(1-\cos\theta_j)+2\tau_p(U)\\
 &\le e^{-U}N_p(U)+2\tau_p(U).
 \end{aligned}
 \tag{13}
\]
Here each active coordinate costs at most \(e^{-U}\), because
\[
 1-\cos\theta_j\le\frac{\theta_j^2}{2}
 \le\frac{2\pi^2}{Q_j^2}\le\frac1{x_j}.
\]
By (11) and \(b>\nu\), the right side of (13) is below \(\eta\) for all
sufficiently small \(\eta\).

Since \(\lceil y\rceil\le2y\) for \(y\ge1\), (12) also gives, for an
absolute constant \(c_0\),
\[
 \log T_p(\eta)
 \le {\cal H}_p(U)+c_0N_p(U).
 \tag{14}
\]
Because \(U/L\to1\), (7) implies
\[
 {\cal H}_p(U)\sim{\cal H}_p(L),
 \qquad N_p(U)=o({\cal H}_p(L)).
 \tag{15}
\]
Equations (14)--(15) prove the required upper asymptotic.

### Matching Haar lower bound

Take the finite head
\[
 A_{2L}=\{j:a_j\le2L\},\qquad
 M=N_p(2L),\qquad
 \tau=\tau_p(2L),\qquad m=1-\tau.
\]
By (11), \(\tau=o(\eta)\).  Normalize its weights by
\(w_j=p_j/m\).  If the full packet returns to amplitude at least
\(1-\eta\), then the normalized head has amplitude at least
\[
 1-\delta,\qquad \delta=\eta/m.
 \tag{16}
\]
For unit phases \(z_j\), the weighted variance identity gives
\[
 \sum_{j,k}w_jw_k|z_j-z_k|^2
 =2\left(1-\left|\sum_jw_jz_j\right|^2\right)
 \le4\delta.
 \tag{17}
\]
Consequently at least one pivot \(k\) satisfies
\[
 \sum_jw_j|z_j-z_k|^2\le4\delta.
 \tag{18}
\]

For a fixed pivot, projective Haar shear makes the relative phases
independent and Haar-uniform.  Exponential Markov together with the exact
circle Laplace bound
\[
 {\mathbb E}\,e^{-u|Z-1|^2}
 \le
 \exp\!\left[-\frac12\log\max\!\left(1,\frac{16u}{\pi}\right)\right]
 \tag{19}
\]
therefore yields, for every \(\lambda>0\),
\[
 {\mathbb P}((18))
 \le
 \exp\!\left[
 \frac{\pi}{4}\lambda\delta
 -\frac12\sum_{j\ne k}\log\max(1,\lambda w_j)
 \right].
 \tag{20}
\]
Choose \(\lambda=\delta^{-1}\).  Then
\(\lambda w_j=p_j/\eta\) exactly.  Moreover all coordinates with
\(p_j\ge\eta\) lie in \(A_{2L}\), and hence
\[
 \frac12\sum_{j\in A_{2L}}\log\max(1,p_j/\eta)
 ={\cal H}_p(L).
 \tag{21}
\]
Removing the pivot costs at most \(L/2\).  A union bound over the \(M\)
pivots now gives the one-step target estimate
\[
 {\mathbb P}\left(
 \left|\sum_jp_jz_j\right|\ge1-\eta\right)
 \le
 M\exp\!\left(\frac\pi4-{\cal H}_p(L)+\frac L2\right).
 \tag{22}
\]

Every positive integer coordinatewise power map preserves product Haar
measure.  Another union bound therefore shows that the phase population
returning through time \(N\) has measure at most
\[
 NM\exp\!\left(\frac\pi4-{\cal H}_p(L)+\frac L2\right).
 \tag{23}
\]
For the worst-packet deadline, choose the right side below one.  For the
fixed-\(q\) deadline, choose it below \(q\).  Thus
\[
 \begin{aligned}
 {\cal H}_p(L)-\frac L2-\log N_p(2L)-O_q(1)
 &\le \log T_{p,q}(\eta)\\
 &\le\log T_p(\eta)\\
 &\le{\cal H}_p(U)+c_0N_p(U).
 \end{aligned}
 \tag{24}
\]
Since \(L+\log N_p(2L)=o({\cal H}_p(L))\) for every \(\nu>0\),
(7), (15), and (24) prove (3), (4), and (4a).

### Anderson transfer

Fix \(\epsilon>0\).  Equations (4b)--(4c) imply, outside a finite set,
\[
 (\lambda_x-\epsilon)r_j\le a_j(x)
 \le(\lambda_x+\epsilon)r_j.
\]
Therefore
\[
 M_x\!\left(\frac{L}{\lambda_x+\epsilon}\right)-O(1)
 \le N_{p(x)}(L)
 \le
 M_x\!\left(\frac{L}{\lambda_x-\epsilon}\right)+O(1).
\]
Use (4b), divide by \(L^d\), and send first \(L\to\infty\) and then
\(\epsilon\downarrow0\).  This proves (4d); (4e)--(4f) follow from
(3).

## Nature gate

The paper must distinguish three statements:

1. the universal spectral law (3), which is purely mathematical;
2. the deterministic Anderson interface \(p_j(x)=\langle x,\Pi_jx\rangle\);
3. identification of \(\nu\) with physical spatial dimension, proved by
   (4b)--(4c), but not yet transferred from standard one-sided Anderson
   localization estimates for a named random ensemble.

This card cannot carry a Nature claim.  It is a proved-geometry candidate
and recurrence bridge.  Nature-level novelty requires proving (4b)--(4c),
or a sharper density version, for a recognized Anderson model; presenting
\(\nu\) only as an abstract observer spectral dimension does not clear the
priority bar.

## Formal status

The finite-head bounded-density transfer is proved in
`formal/GaloisForLFunctions/RHTower/ProjectiveWeightedBoundedDensityQuantile.lean`:

1. nonzero integer power maps preserve domination by a Haar multiple;
2. measure domination transfers to real target probabilities;
3. the early-hit probability is bounded by the domination factor times the
   canonical Haar water budget.

The infinite active-head extraction, summable Borel--Cantelli passage,
all-scale interpolation, and post-exit theorem remain Lean-open.  Equations
(4b2)--(4b5) are not manuscript-authorized until those dependencies are
formalized.
