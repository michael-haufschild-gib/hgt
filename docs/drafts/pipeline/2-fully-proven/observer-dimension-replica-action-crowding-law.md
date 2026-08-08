# Observer dimension forces replica-action crowding

- **ID:** `observer-dimension-replica-action-crowding-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / Brown-scale route-killer / positive representation law
- **Parents:** `fixed-shell-transversality-onset-hardening-cone-law.md`,
  `../3-formalized/replica-crowding-central-limit-floor.md`
- **Status:** `[PAPER-PROVED] [FRONTIER CORRECTION] [ABSOLUTE-TRANSVERSALITY ROUTE RETIRED]
  [SIGNED PACKET CORE OPEN] [LEAN DEFERRED] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-08

## Public sentence

A local observer cannot resolve exponentially many quantum histories one by one: replica actions
must crowd in observer space, so the present first-order Brown-scale strategy cannot work by
separating every spectral action or by discarding crowded actions after taking absolute values.

## Exact change of frontier

The prior fixed-shell onset theorem replaced an unnamed Riemann--Lebesgue threshold by a finite
first-order transversality bound.  It remained mathematically correct, but its proposed asymptotic
frontier was wrong.  At Brown replica order `r=Theta(D)`, its explicit `1/|t|` remainder already
requires `|t|=exp(Theta(D))` to reach the exponentially small capture-moment scale.  No estimate on
its constants `Q_r` and `B` can turn that proof into an onset at `t=Theta(D)`.

There is a second, geometric obstruction.  The number of balanced replica actions is exponential
in `D`, while their first derivatives live in the `O(n)`-dimensional Hamiltonian observer space.
Packing forces some actions to have exponentially close gradients at every Hamiltonian.  Replacing
the worst action by an amplitude-weighted absolute tail is still insufficient: a vector-valued
central-bin argument forces substantial weighted crowding for the easy seed target itself.

The exact survivor is therefore not a sharper minimum-action or first-gradient estimate.  Within
the audited architecture, a Brown-scale proof must either retain the complex signs of crowded
action packets until after aggregation or introduce genuinely higher structure not reducible to a
positive first-order unresolved-action majorant.

## Theorem A -- deterministic observer-compression law

Let `v_1,...,v_D` lie in the Euclidean ball of radius `L` in `R^d`, and let

\[
 \mathcal P_{D,r}=\{p\in\mathbb N^D:\ \sum_jp_j=r\},\qquad
 N_{D,r}=|\mathcal P_{D,r}|={D+r-1\choose r}.                    \tag{1}
\]

For `p in P_(D,r)`, put `G_p=sum_j p_jv_j`.  If `D>=2` and `r>=1`, then

\[
 \boxed{
 \min_{p\ne q}\|G_p-G_q\|
 \le {2rL\over N_{D,r}^{1/d}-1}.}                               \tag{2}
\]

Thus there is a nonzero balanced integer vector `k=p-q`, with positive and negative masses at most
`r`, whose observed action vector `sum_j k_jv_j` obeys `(2)`.

### Proof

All `N_(D,r)` points `G_p` lie in the ball `B_(rL)` of `R^d`.  If their mutual distance were greater
than `delta`, the open balls of radius `delta/2` around them would be disjoint and contained in
`B_(rL+delta/2)`.  Comparing Euclidean volumes gives

\[
 N_{D,r}(\delta/2)^d\le(rL+\delta/2)^d,
\]

hence `N_(D,r)^(1/d)<=1+2rL/delta`.  Solving for `delta` and taking the infimum of pairwise
distances proves `(2)`.  Distinct multiplicity vectors have a nonzero difference, and equal total
mass makes that difference balanced.  No probability, spectral gap, or genericity premise occurs.

## Corollary A1 -- worst spectral-action transversality is necessarily tiny

For the fixed-shell nearest-neighbour Pauli family, let `m=12n-9`, `D=2^n`, and let
`d=m-1` be the tangent dimension of the coefficient sphere.  On a simple-spectrum point set

\[
 v_j(\theta)=\nabla_SE_j(\theta).                                \tag{3}
\]

Hellmann--Feynman and Cauchy--Schwarz give

\[
 \|v_j(\theta)\|
 =\sup_{\|u\|_2=1}|\langle e_j,H(u)e_j\rangle|
 \le\sup_{\|u\|_2=1}\sum_{a=1}^m|u_a|
 \le\sqrt m.                                                     \tag{4}
\]

Applying Theorem A in the tangent space proves

\[
 \boxed{
 \min_{k\in K_r}\|\nabla_S\phi_k(\theta)\|
 \le {2r\sqrt m\over {D+r-1\choose r}^{1/(m-1)}-1}.}            \tag{5}
\]

Let `Q_r(zeta,g)` be the worst-action tail from the parent card and put

\[
 g_{\rm pack}(n,r)
 ={r\sqrt m\over {D+r-1\choose r}^{1/(m-1)}-1}.                  \tag{6}
\]

For every `g>=g_pack`, every simple point belongs to the small-gradient event.  Therefore

\[
 Q_r(\zeta,g)\ge\sigma\{\operatorname{Disc}\ge\zeta\}.          \tag{7}
\]

For `r=floor(cD)` with fixed `c>0`, the elementary binomial lower bound
`binom(D+r-1,r)>=( (D+r-1)/r )^r` gives a constant `kappa_c>0` such that

\[
 g_{\rm pack}(n,r)
 \le \exp\{-\kappa_cD/(m-1)+O(n)\}
 =\exp\{-\Omega(2^n/n)\}.                                      \tag{8}
\]

Consequently, making `Q_r` smaller than a fixed constant forces
`g<g_pack` and hence `g^(-2)=exp(Omega(2^n/n))`.  Worst-character
first-order transversality is not a Brown-time mechanism.

## Theorem B -- amplitude-weighted observer crowding

Let `lambda=(lambda_1,...,lambda_D)` be a probability vector and let `X` take value `v_j in R^d`
with probability `lambda_j`, where `||v_j||<=L`.  Let `P` be the multiplicity vector of `r`
independent copies of `X`, let `S=sum_jP_jv_j`, and let `(P',S')` be an independent copy.  Define

\[
 C_r(\lambda)=\Pr\{P=P'\}
 =\sum_{p\in\mathcal P_{D,r}}\Pr\{P=p\}^2.                      \tag{9}
\]

Then for every `delta>0`,

\[
 \boxed{
 \Pr\{P\ne P',\ \|S-S'\|\le\delta\}
 \ge {9\over16}
       \left(1+{8L\sqrt r\over\delta}\right)^{-d}
       -C_r(\lambda).}                                           \tag{10}
\]

### Proof

Writing `mu=E X`, independence gives

\[
 \mathbb E\|S-r\mu\|^2
 =r\,\mathbb E\|X-\mu\|^2\le rL^2.                             \tag{11}
\]

Markov's inequality therefore places at least `3/4` of the law of `S` in the ball
`B_(2L sqrt r)(r mu)`.  A ball of radius `2L sqrt r` in `R^d` has a `delta/2`-net of cardinality at
most

\[
 M_\delta\le\left(1+{8L\sqrt r\over\delta}\right)^d.            \tag{12}
\]

Partition the central ball into Voronoi cells of that net.  Every cell has diameter at most
`delta`.  If their probability masses are `b_1,...,b_M`, then

\[
 \Pr\{S,S'\text{ lie in one cell}\}
 =\sum_ab_a^2\ge {1\over M}\left(\sum_ab_a\right)^2
 \ge {9\over16M_\delta}.                                       \tag{13}
\]

This event implies `||S-S'||<=delta`.  Removing the entire event `P=P'`, whose probability is
`C_r(lambda)`, proves `(10)`.

## Theorem C -- exact replica-coefficient random-walk representation

Fix one filtered target coefficient family `widetilde c_j` and put

\[
 S_0=\sum_j|\widetilde c_j|.
\]

If `S_0>0`, define `lambda_j=|widetilde c_j|/S_0` and take
`v_j=nabla_S E_j`.  The ordered replica coefficients satisfy the pointwise identity

\[
 \boxed{
 \sum_{\alpha,\beta\ {\rm off}}
 |\widetilde A_{\alpha,\beta}|
 \mathbf1_{\{\|\nabla_S\Phi_{\alpha,\beta}\|\le\delta\}}
 =S_0^{2r}
 \Pr\{P\ne P',\ \|S-S'\|\le\delta\}.}                         \tag{14}
\]

For `S_0=0`, both sides are zero by definition.

### Proof

Under the product law `lambda^(tensor r)`, an ordered tuple `alpha` has probability
`prod_l lambda_(alpha_l)`.  Its multiplicity vector is multinomial and its observed sum is
`sum_l v_(alpha_l)`.  Multiplying the independent forward and backward probabilities by
`S_0^(2r)` gives exactly `|widetilde A_(alpha,beta)|`.  Equality of multiplicity vectors is exactly
the diagonal condition, and the difference of observed sums is
`nabla_S Phi_(alpha,beta)`.  Summing proves `(14)`.

## Corollary C1 -- even weighted absolute transversality misses Brown scale

Use the common soft-light filter from the parent theorem and choose the target `z=chi`, the
efficient stabilizer seed itself.  In the circuit-union application, take `s` at least the
polynomial Clifford preparation length of `chi`, so this target belongs to `Z_s`.  Then
`c_j=p_j=||Pi_j chi||^2` is nonnegative.  On the collision-good set

\[
 C=\sum_jp_j^2\le {2\mathcal L\over D+1},                       \tag{15}
\]

the filtered mass and largest normalized weight obey

\[
 S_0\ge1-a/4\ge3/4,
 \qquad
 \max_j\lambda_j\le {64\mathcal L\over3a(D+1)}.                \tag{16}
\]

Indeed the filter removes mass only from indices with `p_j>4C/a`, whose total mass is at most
`a/4`; its support has `p_j<8C/a`; divide by `S_0>=3/4`.

Take

\[
 r=\left\lfloor{a^2(D+1)\over256\mathcal L}\right\rfloor.       \tag{17}
\]

Assume `r>=1`, as holds for all sufficiently large `n` at fixed `a,mathcal L`.

Since `C_r(lambda)<=max_p Pr(P=p)<=r!(max_j lambda_j)^r`, equations `(16)--(17)` and
`r!<=r^r` give

\[
 C_r(\lambda)\le12^{-r}.                                        \tag{18}
\]

Equations `(4)`, `(10)`, and `(14)`, with `delta=D^(-1)`, yield

\[
 \sum_{\alpha,\beta\ {\rm off}}
 |\widetilde A_{\alpha,\beta}|
 \mathbf1_{\{\|\nabla_S\Phi_{\alpha,\beta}\|\le D^{-1}\}}
 \ge \left({9\over16}\right)^r
 \left[
 {9\over16}(1+8D\sqrt{rm})^{-(m-1)}-12^{-r}
 \right].                                                       \tag{19}
\]

For `m=12n-9`, `D=2^n`, and fixed `mathcal L,a`, the positive first term in the bracket is
`exp(-O(n^2))`, whereas `12^(-r)=exp(-Theta(D))`.  Thus for all sufficiently large `n` the bracket
is bounded below by `exp(-O(n^2))`; relative to the capture scale `(a/4)^r`, `(19)` gives

\[
 {\text{absolute crowded mass}\over(a/4)^r}
 \ge\left({9\over4a}\right)^r\exp\{-O(n^2)\}.                 \tag{20}
\]

It is exponentially too large even before a circuit union is paid.  Replacing the minimum in
`Q_r` by an amplitude-weighted **absolute** small-gradient mass cannot repair the Brown-time proof.

## Corollary C2 -- first-order dephasing has the wrong clock independently of constants

For `0<q<=1`, the parent onset formula contains

\[
 T_{\rm tr}
 ={2BN_s\over q(a/4)^r}(g^{-1}+g^{-2}),\qquad B,N_s\ge1.         \tag{21}
\]

The onset condition requires `Q_r<1` for large `n`.  If `g>=g_pack`, `(7)` and the first term in
the definition of `Q_r` give
`Q_r>=sigma{Disc>=zeta}+sigma{Disc<=2zeta}>=1`.  Hence the onset condition forces
`g<g_pack<1`, and therefore

\[
 T_{\rm tr}\ge {2\over q}\left({4\over a}\right)^r.             \tag{22}
\]

At `r=Theta(D)`, `(22)` is `exp(Theta(D))`, the recurrence/plateau-lifetime scale, not the Brown
growth time `Theta(D)`.  This lower bound is built into the proof architecture; improving `Q_r`,
`B`, semialgebraic exponents, or spectral gaps cannot remove it.

## Theorem D -- exact signed-lift convolution law

The crowded object has an exact algebraic representation.  Fix `theta,z,chi` and filtered
coefficients `widetilde c_j`.  Let `e_j` be the standard basis of `Z^D`, put

\[
 \mu_1=\sum_{j=1}^D\widetilde c_j
 \delta_{(e_j,v_j,E_j)}
 \quad\text{on}\quad
 \mathbb Z^D\times\mathbb R^d\times\mathbb R,                  \tag{23}
\]

and let `mu^star` denote conjugate reflection of a complex atomic measure.  Define

\[
 \mu_r=\mu_1^{*r},\qquad
 \nu_r=\mu_r*\mu_r^\star.                                      \tag{24}
\]

Then

\[
 \boxed{\nu_r=\nu_1^{*r}.}                                     \tag{25}
\]

Writing

\[
 a_p={r!\over\prod_jp_j!}\prod_j\widetilde c_j^{p_j},
 \qquad |p|=r,                                                  \tag{26}
\]

the contribution of a forward--backward pair `(p,q)` has signed coefficient
`a_p overline(a_q)`, hidden lattice label `k=p-q`, and observed action

\[
 \left(\sum_jk_jv_j,\ \sum_jk_jE_j\right).                    \tag{27}
\]

The exact return sector is `k=0`, equivalently `p=q`.  Therefore source-first return excision is
the single final projection

\[
 \boxed{\nu_r^{\rm off}=P_{k\ne0}(\nu_1^{*r}),}                \tag{28}
\]

followed by dropping the hidden label `k` and grouping the observed actions at the chosen finite
resolution.  Fibre-sheet multiplicities and complex signs are retained automatically because
pushforward sums coincident atoms before any norm or absolute value is taken.

### Proof

The multinomial theorem identifies `mu_1^{*r}` with the atoms
`(p,sum_j p_jv_j,sum_j p_jE_j)` and coefficients `(26)`.  Commutativity of convolution and
conjugate reflection give

\[
 \nu_r
 =\mu_1^{*r}*(\mu_1^\star)^{*r}
 =(\mu_1*\mu_1^\star)^{*r}=\nu_1^{*r}.
\]

The lattice coordinate of a forward--backward pair is `p-q`; since both multiplicity vectors have
mass `r`, it vanishes exactly when `p=q`.  The action coordinates are linear in that difference,
and pushforward combines all sheets mapping to one observed action by signed addition.  This proves
`(25)--(28)`.

For every observer frequency `xi in R^d` and time `t`, Fourier evaluation gives the exact character
identity

\[
 \boxed{
 \widehat\nu_r(\xi,t)
 =\left|\sum_j\widetilde c_j
   e^{-i(tE_j+\langle\xi,v_j\rangle)}\right|^{2r}.}             \tag{29}
\]

Since every `k=0` atom has zero observed action, final return removal yields

\[
 \boxed{
 \widehat\nu_r^{\rm off}(\xi,t)
 =\widehat\nu_r(\xi,t)-
   \sum_{|p|=r}|a_p|^2.}                                       \tag{30}
\]

Thus packet cancellation is Fourier cancellation after fibre sheets have been aggregated.  For the
seed target all `widetilde c_j` are nonnegative and `nu_r` itself is a positive measure; calling the
lift “signed” does not supply decay.  Any contraction theorem must act on `(29)--(30)`, not merely
on total variation of `(28)`.

This distinction is exact.  Without filtering, the seed coefficients `c_j=p_j` form a probability
vector, so `nu_r` is a probability measure and

\[
 \|\nu_r^{\rm off}\|_{\rm TV}=1-C_r(p).                        \tag{31}
\]

For the uniform law `p_j=1/D` and `r=floor(cD)` with fixed `0<c<1`,
`C_r(p)<=max_q Pr(P=q)<=r!D^(-r)<=c^r`; hence off-return total variation tends to one rather than
contracting.  This is an exact counterexample to any universal total-variation contraction claim.
Moreover return projection does not commute with convolution.  Writing `P_0` for the `k=0`
projection and `P_\perp=1-P_0`,

\[
 P_\perp(\nu_1^{*2})
 -P_\perp\bigl((P_\perp\nu_1)^{*2}\bigr)
 =2P_\perp\bigl((P_0\nu_1)*(P_\perp\nu_1)\bigr),              \tag{32}
\]

which is nonzero whenever both return and off-return one-step sectors are nonzero and their
convolution has off-return support.  Stepwise killing therefore deletes histories that return at an
intermediate replica step and leave again before the final replica order.

Theorem D does not prove contraction.  It replaces the informal packet with the exact operator to
be studied: convolution by `nu_1`, one final return projection, then observer/incidence
pushforward.  Projecting away `k=0` after every convolution step would be a different process and
is not allowed.

## Methodological no-go and positive survivor

Any first-order gradient-cutoff argument which, at Brown time, discards at least the sector
`||nabla_S Phi||<=D^(-1)` by the positive majorant

\[
 \sum_{\alpha,\beta}|\widetilde A_{\alpha,\beta}|
 \mathbf1_{\{\text{action unresolved}\}}                       \tag{33}
\]

must pay `(19)` on the collision-good seed target.  Therefore that class of arguments cannot prove
an `O((a/4)^r)` shortcut error at `r=Theta(D)` and `t=Theta(D)`.  Corollary C2 independently
retires the parent's particular `1/|t|` integration-by-parts formula for every choice of its
constants.

The strongest positive representation survivor is exact:

> The signed lift `(28)` retains information that action magnitude, minimum gradient, Jacobian
> determinant, and positive first-order near-action mass discard before it can act.

This is not a claim that the required cancellation already holds, nor a no-go for every possible
higher-order oscillatory invariant.  It proves that any continuation of the current
first-order/coarea architecture must retain signed/complex packet amplitudes through return
excision and the adaptive circuit incidence operation.

## Conjecturing protocol

### C0 -- make the worst-action transversality constants uniform in growing replica order

**Verdict:** `[FALSIFIED AS A BROWN-SCALE ROUTE]` by `(5)--(8)` and `(21)--(22)`.

Even ideal constants cannot change the explicit exponential-in-`r` time denominator.  Observer
packing additionally forces the worst gradient to be `exp(-Omega(D/n))`.

**Representation lesson:** resolving every character separately is the wrong operation.

### C1 -- weight unresolved actions by their physical replica amplitudes

**Verdict:** `[FALSIFIED AS AN ABSOLUTE-VALUE ROUTE]` by `(19)--(20)`.

The seed target has a broad collision-good spectral law, and its replica velocity sums have a
universal central-bin crowding floor in the `O(n)`-dimensional observer space.

**Representation lesson:** physical weights help only if their complex signs are retained.

### C2 -- a random-matrix spectral ramp supplies the missing complexity ramp

**Verdict:** `[FALSIFIED]`.

Ippoliti's 2026 static geometrically local clock Hamiltonian proves a connected spectral-form-factor
ramp beginning at physical time `Theta(n)`.  Standard local-Hamiltonian simulation prepares every
state endpoint at that time with polynomial circuit size.  Thus a rigorous spectral ramp can begin
while state complexity is still polynomial; a second-order trace statistic is not the missing
growing-replica no-shortcut law.

**Positive survivor:** static spectral ramps are evidence that signed spacetime contractions can be
proved in engineered local models.  The needed extension is a scale-matched, return-excised,
selector-aware signed replica packet law, not another spectral-form-factor claim.

### C3 -- the signed lift contracts in total variation

**Verdict:** `[FALSIFIED]` by `(31)`.

For a uniform positive seed law at `r=Theta(D)`, off-return total variation tends to one.  The
measure representation preserves the needed signs but does not create their interference.

**Representation lesson:** evaluate observer-action characters before applying the quotient norm.

### C4 -- delete return after each replica convolution and use a killed transfer gap

**Verdict:** `[FALSIFIED AS A REPRESENTATION OF THE TARGET PROCESS]` by `(32)`.

Stepwise projection deletes paths that visit `k=0` and later leave.  It can be studied as a new
process, but its spectral gap proves nothing about final source-first return excision unless the
missing renewal terms are restored.

**Representation lesson:** take the full power first and project return exactly once.

### C5 -- final-projected Fourier packet cancellation is the missing primitive

**Verdict:** `[SURVIVES PRELIMINARY ATTACK; OPEN]`.

The exact conjecture is recorded separately in
`../1-in-progress/scale-matched-signed-action-packet-law.md`.  Unlike C0--C4, it starts from the
exact signed convolution lift `(28)`, evaluates `(29)--(30)`, takes the occupied-incidence quotient
only afterward, and predicts the entire growth-to-plateau front rather than only late
equidistribution.

## External separation audit

- Euclidean packing and the central-ball second-moment argument are classical.  Multivariate
  concentration-function theory, including Kolmogorov--Rogozin and Littlewood--Offord methods,
  studies sharper upper and lower small-ball bounds; those parent tools are not claimed new:
  <https://arxiv.org/abs/2201.09861>, <https://arxiv.org/abs/1402.4492>.
- Greenblatt develops modern oscillatory-integral estimates using weighted gradient flows.  Those
  estimates do not address a growing replica language, an adaptive circuit target, or the
  seed-forced crowding obstruction `(19)`: <https://arxiv.org/abs/2403.12751>.
- Ippoliti proves the first random-matrix spectral ramp for a static geometrically local
  finite-dimensional Hamiltonian, in one clock sector and after disorder/time smoothing.  It does
  not prove state or unitary circuit-complexity growth:
  <https://arxiv.org/abs/2606.30635>.
- Zhou--Zhou--Sonner require three quenched Hamiltonian intervals for arbitrary temporal
  `k`-designs; Sun--Zhang use two Hamiltonians plus a random Pauli.  Neither is a one-generator
  Brown law: <https://arxiv.org/abs/2604.04205>, <https://arxiv.org/abs/2604.10122>.

No audited source states the observer-dimension packing obstruction for growing spectral replica
actions, its amplitude-weighted seed-target strengthening, or the resulting retirement of positive
first-order gradient cutoffs in static-local circuit complexity.  This is separation evidence, not
a final priority certification.

## Hostile review

1. Theorems A--D are unconditional finite-dimensional statements; the asymptotic application uses
   only the parent fixed-shell definitions and collision-good filter.
2. This card proves a no-go for a proof architecture, not Brown--Susskind growth itself.
3. The lower crowding bound does not imply that the signed oscillatory sum is large.  It rules out
   the specified positive first-order majorant, not all higher-order phase analysis.  Signed
   cancellation is the current surviving candidate, not a proved necessity among every
   conceivable method.
4. The static spectral-ramp comparison is a logical separation, not evidence that clock
   Hamiltonians have Brown state complexity.
5. Novelty can lie only in the exact quantum-complexity composition and frontier theorem; packing,
   Chebyshev, covering, and multinomial identities are classical.
6. No Lean claim is made.  During corpus refactoring, reuse should begin from
   `TracelessReplicaDyadicActionShellLaw.lean`, `ReplicaActionCrowdingShortcutLaw.lean`, and the
   finite-dimensional packing/covering corpus after the paper statement is independently audited.

## Remaining frontier

Prove or falsify the scale-matched signed packet conjecture.  A successful estimate must preserve:

1. complex packet cancellation;
2. source-first return excision;
3. the occupied adaptive circuit endpoint image;
4. replica orders `1<=r<=Theta(D)` with physical time proportional to `r` before saturation;
5. a fixed ordinary time-independent local generator.

Any return to minimum gaps, worst gradients, positive near-action mass, raw Jacobians, fixed-order
spectral form factors, or fresh time-dependent noise is already ruled out by the corpus and this
card.
