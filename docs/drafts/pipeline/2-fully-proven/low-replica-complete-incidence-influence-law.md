# Low-replica complete-incidence influence law

- **ID:** `low-replica-complete-incidence-influence-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / replica-order decoupling / complete-union low-influence law
- **Parent:** `beta-threshold-complete-incidence-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [EXTERNAL PRIORITY OPEN] [LEAN DEFERRED]`
- **Date:** 2026-08-09

## Public sentence

Testing whether an autonomous quantum state is close to **any** short-circuit state does not require
one replica per circuit bit.  At fixed observational slack, replica order grows only logarithmically
with the desired confidence and number of observation times, regardless of circuit-image
cardinality; after one collision-controlled light filter, the resulting union is one phase
observable whose sensitivity vanishes as Hilbert-space dimension grows.

This removes growing replica order `r=Theta(D)` from the list of logically mandatory Brown-front
inputs.  It does not prove that a static local-Hamiltonian ensemble mixes this observable at the
Brown time scale.

## Setup

Let

\[
 V=\bigoplus_{j=1}^d V_j
\]

be an orthogonal decomposition of a finite-dimensional complex Hilbert space.  Fix vectors
`u_j in V_j` with

\[
 \sum_j\|u_j\|^2\le1,
 \qquad p_*=\max_j\|u_j\|^2,                                   \tag{1}
\]

and define the phase orbit

\[
 \psi(\phi)=\sum_{j=1}^d e^{-i\phi_j}u_j,
 \qquad \phi\in\mathbb T^d.                                   \tag{2}
\]

For an arbitrary finite nonempty set `Z` of unit vectors, put

\[
 X_z(\phi)=|\langle z,\psi(\phi)\rangle|^2,
 \qquad Y_Z(\phi)=\max_{z\in Z}X_z(\phi).                      \tag{3}
\]

Fix `0<b<a<1`, `delta=a-b`, `q=(a+b)/2`, replica order `r>=1`, and
`k=ceil(rq)`.  Let `B_(r,k)` be the binomial-tail polynomial from the parent card and define

\[
 F_{Z;r,a,b}(\phi)=\mathcal B_{r,k}(Y_Z(\phi)).                 \tag{4}
\]

## Theorem A -- replica order is independent of target entropy

For every probability law `nu` on the phase torus and every finite target set `Z`,

\[
 \begin{aligned}
 &(1-e^{-r\delta^2/2})\,
   \nu\{Y_Z\ge a\}
 \le \mathbb E_\nu F_{Z;r,a,b}\\
 &\hspace{35mm}\le
   \nu\{Y_Z\ge b\}+e^{-r\delta^2/2}.                         \tag{5}
 \end{aligned}
\]

The estimate contains no dependence on `|Z|`.  More generally, any desired reporter error
`0<zeta<1` is achieved by

\[
 r(\zeta)=\left\lceil{2\log(1/\zeta)\over\delta^2}\right\rceil, \tag{6}
\]

because `exp(-r(zeta) delta^2/2)<=zeta`.  In particular, for `n>=2`,

\[
 r_n=\left\lceil{4\log n\over\delta^2}\right\rceil           \tag{7}
\]

gives `exp(-r_n delta^2/2)<=n^(-2)`.  Therefore logarithmic replica order provides the
fixed-slack implications

\[
 \mathbb E F_{Z_n;r_n,a,b}=o(1)
   \Longrightarrow \nu_n\{Y_{Z_n}\ge a\}=o(1),                \tag{8}
\]

and

\[
 \nu_n\{Y_{Z_n}\ge b\}=o(1)
   \Longrightarrow \mathbb E F_{Z_n;r_n,a,b}=o(1)             \tag{9}
\]

for **every** sequence of finite target images `Z_n`, even if their cardinalities are
doubly exponential.  The proof is Theorem A of the parent card with `(7)` substituted.  No target
union bound is taken.

For a union over `N_time` prescribed observation times with total reporter error at most `zeta`, it
is enough to take

\[
 \boxed{
 r_{\rm time}
 =\left\lceil{2\log(N_{\rm time}/\zeta)\over\delta^2}\right\rceil.} \tag{10}
\]

Thus a fixed-time theorem needs only `r=O(log n)` for inverse-polynomial confidence.  A continuous
Brown ramp up to saturation time `Theta(D)` has, after a fixed-accuracy speed mesh,
`N_time=O(D poly(n))`; it needs `r=O(log D)=O(n)`, not `O(log n)`.  Both schedules are exponentially
smaller than `r=Theta(D)`.  A doubly-exponential continuous plateau can again require
`r=Theta(D)` solely to survive its exponentially larger time grid; the plateau parent already
supplies that separate estimate.

## Theorem B -- the complete target union is one low-influence observable

The binomial tail obeys

\[
 0\le\mathcal B'_{r,k}(x)
 =r{r-1\choose k-1}x^{k-1}(1-x)^{r-k}\le r                    \tag{11}
\]

on `[0,1]`.  The complete-incidence observable `(4)` is Lipschitz on `T^d` and satisfies, almost
everywhere,

\[
 \boxed{
 \|\nabla_\phi F_{Z;r,a,b}(\phi)\|_2^2
 \le4r^2p_*.}                                                  \tag{12}
\]

Consequently normalized Haar measure `m_d` on `T^d` obeys

\[
 \boxed{
 \operatorname{Var}_{m_d}(F_{Z;r,a,b})
 \le4r^2p_*.}                                                  \tag{13}
\]

Both bounds are independent of the number, parametrization, metric entropy, and duplication of
the targets.  They remain true for the complete endpoint image of every finite circuit dictionary
at every depth.

### Proof

The factor multiplying `r` in `(11)` is a binomial probability and is at most one.  For one target,
write

\[
 A_z(\phi)=\langle z,\psi(\phi)\rangle,
 \qquad c_{j,z}=\langle z,u_j\rangle.
\]

Orthogonality and Cauchy--Schwarz give

\[
 \sum_j|c_{j,z}|^2
 \le p_*\sum_j\|\operatorname{Proj}_{V_j}z\|^2=p_*.           \tag{14}
\]

Since `X_z=|A_z|^2`,

\[
 |\partial_{\phi_j}X_z|
 \le2|A_z|\,|c_{j,z}|,
\]

and hence

\[
 \sum_j|\partial_{\phi_j}X_z|^2
 \le4X_z\sum_j|c_{j,z}|^2\le4p_*.                              \tag{15}
\]

A finite maximum of functions with common Lipschitz constant has that same constant.  At almost
every differentiability point, its gradient belongs to the convex hull of the active gradients,
so `(15)` also holds for `Y_Z`.  The chain rule and `(11)` prove `(12)`.  The product-circle
Poincare inequality has constant one and turns `(12)` into `(13)`.

## Theorem C -- common light filtering makes phase influence vanish

Now let `psi_full(phi)=sum_j exp(-i phi_j)u_j` be a unit orbit and put

\[
 p_j=\|u_j\|^2,
 \qquad C=\sum_jp_j^2.                                         \tag{16}
\]

For `0<rho<1`, set `tau=C/rho^2`, retain

\[
 L=\{j:p_j\le\tau\},
 \qquad
 \widetilde\psi(\phi)=\sum_{j\in L}e^{-i\phi_j}u_j.           \tag{17}
\]

Then

\[
 \boxed{
 \|\psi_{\rm full}(\phi)-\widetilde\psi(\phi)\|^2
 =\sum_{p_j>\tau}p_j\le{C\over\tau}=\rho^2,}                  \tag{18}
\]

while the retained maximum weight is at most `C/rho^2`.  Thus the statistic `(4)` formed from
`tilde psi` satisfies

\[
 \boxed{
 \operatorname{Var}_{m_d}(F^{\rm light}_{Z;r,a,b})
 \le {4r^2C\over\rho^2}.}                                     \tag{19}
\]

If `C<=c/D`, then

\[
 \operatorname{Var}_{m_d}(F^{\rm light}_{Z;r,a,b})
 \le {4cr^2\over\rho^2D}.                                     \tag{20}
\]

In particular, the fixed-time choice `(7)` makes this variance `O((log n)^2/2^n)`.  The
single-trajectory Brown-grid choice `(10)` makes it `O(n^2/2^n)`.  Both vanish exponentially for
the collision-good cubic-phase/static-local pairs already constructed in the parent programme.

The filtering is operationally harmless at fixed slack.  Uniformly in `Z`,

\[
 \left|
  \sqrt{Y_Z^{\rm full}(\phi)}-
  \sqrt{Y_Z^{\rm light}(\phi)}
 \right|\le\rho.                                                \tag{21}
\]

Hence, for any physical fidelity threshold `a_0>rho^2`, setting

\[
 a=(\sqrt{a_0}-\rho)^2
\]

and choosing any `0<b<a` gives

\[
 \Pr\{Y_Z^{\rm full}\ge a_0\}
 \le {\mathbb E F^{\rm light}_{Z;r,a,b}
        \over1-e^{-r(a-b)^2/2}}.                                \tag{22}
\]

Conversely

\[
 \mathbb E F^{\rm light}_{Z;r,a,b}
 \le
 \Pr\left\{Y_Z^{\rm full}\ge(\sqrt b-\rho)_+^2\right\}
 +e^{-r(a-b)^2/2}.                                               \tag{23}
\]

### Proof

For every discarded index, `p_j>tau` implies `p_j<=p_j^2/tau`; summing proves `(18)`.
Equations `(19)--(20)` follow from Theorem B.  For every unit target `z`, the two overlap
amplitudes differ by at most the norm in `(18)`.  Taking the maximum proves `(21)`, and the event
inclusions from `(21)` combined with `(5)` prove `(22)--(23)`.

Every statement remains valid after restricting the source measure by a target-independent return
set.  Return mass is then added once by Theorem B' of the parent card.

## Conjecturing and falsification ledger

### C0 -- Brown growth requires replica order proportional to circuit depth

**Falsified as a logical requirement.**  It is required by the monomial moment plus circuit-word
union architecture, not by the physical shortcut event.  Equations `(5)--(10)` use `r=O(log n)`
for one fixed time and `r=O(n)` for the entire Brown-time mesh, for an arbitrarily large complete
target image.

### C1 -- taking the complete target maximum necessarily imports circuit entropy into derivatives

**Falsified.**  Maxima preserve a common Lipschitz constant.  Equations `(12)--(13)` contain no
`|Z|`, circuit count, or occupied-span rank.

### C2 -- collision control is too weak to make the complete union low influence

**False after one common light filter.**  Equations `(18)--(20)` convert collision `O(1/D)` into
complete-union phase variance `O(r^2/D)` while spending only fixed observational slack.  The filter
is target-independent and is applied once.

### C3 -- low influence alone transfers completed-phase bounds to one laboratory time

**False without dynamical input.**  A singular phase graph can lie inside a small Haar-measure
set.  Poincare concentration does not compare the fixed-time Hamiltonian graph
`theta mapsto (theta,t omega(theta))` with product Haar measure.  Static-local spectral motion is
still required.

### Positive survivor

The former mandatory target asked for growing-replica pseudodeterminant, Bures nuclear-norm, or
all-character transversality through `r=Theta(D)`.  The minimal remaining Brown-front statement is
strictly weaker:

> At `r=O(log n)`, prove simultaneously on the `O(n)` geometric endpoint skeleton of
> `geometric-skeleton-brown-ramp-transfer-law.md` that the fixed-shell static-local phase graph
> mixes the single target-cardinality-free, light-filtered incidence observable `(4)` to the
> required total error after one target-independent return excision, for circuit depth
> `s=Theta(min(t,D)/log M_n)`.  Separately align the final skeleton time with the beginning of the
> already available continuous near-maximal plateau.

The child `fixed-time-phase-graph-sobolev-blindness-law.md` sharpens the load-bearing phrase
“incidence observable”: its Dirichlet energy cannot by itself imply graph mixing, and no generic
`poly(n)`-order Sobolev repair can do so.  The theorem must exploit the Hamiltonian-independent,
local-gate-generated structure of the endpoint image.  Subject to that correction, the earlier
`r=O(n)` complete linear ramp mesh remains retired: deterministic circuit composition fills every
interval between the geometric endpoints.

## Hostile audit

1. **Growth still open.**  No estimate compares the physical fixed-time graph average with the
   completed-phase average at Brown scale.
2. **Low Haar variance is not graph anti-concentration.**  Equation `(20)` cannot be substituted
   for the missing mixing theorem.
3. **Filter spends fixed slack.**  The law applies to robust approximate complexity, not exact
   complexity at zero error.
4. **Classical ingredients.**  Binomial thresholding, Poincare, and hard spectral truncation are
   standard separately.  External priority attaches, if anywhere, to their complete adaptive
   circuit-incidence composition and the replica-order/frontier correction.
5. **Not an efficient measurement or search theorem.**  The maximum is the exact mathematical
   shortcut event; the theorem does not provide an efficient algorithm or one target-independent
   POVM that finds the maximizing circuit.
6. **Auxiliary high moments may remain useful.**  Logarithmic order is enough at one time and
   order `O(n)` on the full Brown grid; a later proof of the completed-phase mean may still use
   higher-order moments.  Such moments are proof tools, not part of the minimal physical invariant.
7. **No final-paper claim yet.**  Lean formalization is deferred during the active corpus refactor.

## Exact next move -- retired and replaced by child theorem

`fixed-time-phase-graph-sobolev-blindness-law.md` proves that no generic mixing seminorm dual to
`(12)` can perform the proposed comparison.  A fixed-time graph supports smooth detectors whose
conditional phase-Haar mean, variance and Dirichlet energy vanish while their graph expectation is
one.  Every generic phase Sobolev hierarchy below order `(D-1)/2` has the same obstruction.

The replacement frontier is incidence-specific.  It must compare

\[
 \mathbb E_\theta F^{\rm light}_{Z_s;r,a,b}
   (t\omega(\theta))
\]

with its conditional phase-Haar mean by exploiting that `Z_s` is one Hamiltonian-independent,
gate-generated endpoint image.  Neither the `O(r^2/D)` Dirichlet budget nor the selector's classical
information is sufficient: the same child theorem shows that an `O(n)`-parameter fixed-time orbit
through `t<=2^n` has an arbitrary `epsilon`-net describable with only `O(n^2)` bits.  The live
invariant is the tracking capacity of **local-circuit** codebooks against the spectral graph, not
target count, source entropy, minimum action, or generic phase smoothness.

## Lean realization after corpus refactor

1. target-entropy-free confidence/time-grid replica schedules `(5)--(10)`;
2. orthogonal-component phase-gradient bound `(14)--(15)`;
3. finite-max Lipschitz and product-torus Poincare law `(12)--(13)`;
4. common light-filter collision conversion `(18)--(20)`;
5. threshold transport `(21)--(23)`.
