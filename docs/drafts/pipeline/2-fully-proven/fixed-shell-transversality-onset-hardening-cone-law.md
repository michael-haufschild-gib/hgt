# Fixed-shell spectral transversality controls onset and locality forces a hardening cone

- **ID:** `fixed-shell-transversality-onset-hardening-cone-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / quantitative fixed-shell onset / robust complexity propagation
- **Parents:** `fixed-shell-angular-dephasing-static-local-plateau-law.md`,
  `stabilizer-seeded-static-local-double-exponential-plateau-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE]
  [REPLICA VARIATION ALGEBRA LEAN-PROVED] [ABSTRACT OPERATOR CONE LEAN-PROVED]
  [TRANSVERSALITY LEAN DEFERRED]
  [FINITE-SIZE ONSET ONLY] [BROWN-SCALE FIRST-ORDER ROUTE RETIRED]`
- **Date:** 2026-08-08

## Public sentence

For an ordinary fixed-strength static local Hamiltonian ensemble, plateau onset is controlled by
how transversely its spectral actions move across Hamiltonian space, while locality forbids an
instantaneous jump into the plateau: every robust hard endpoint casts a backward circuit-complexity
cone of exponential duration.

This closes the prior purely non-effective Riemann--Lebesgue step by an exact finite-size geometric
onset bound.  Subsequent observer-crowding analysis proves that formula cannot reach Brown time at
`r=Theta(D)`: its capture denominator alone forces `T_tr=exp(Theta(D))`.  The hardening cone remains
valid, but is not a theorem of monotone growth from laboratory time zero.

## Discovery

The previous plateau theorem exposed spectral collision

\[
 C_H(\chi)=\sum_j|\langle e_j,\chi\rangle|^4
\]

as the capacity invariant: `1/C_H` controls plateau depth and logarithmic lifetime.  Collision
cannot also control onset.  The spectra

\[
 E^{(\eta)}=(0,1,2+\eta),\qquad p_j=1/3,                         \tag{1}
\]

have the same collision `1/3` for every irrational `eta`, but the height-two character
`k=(1,-2,1)` has action `eta`.  Its dephasing can be delayed beyond any prescribed time by taking
`eta` small.  Thus equal capacity does not imply equal clocks.

Minimum nonzero action is also the wrong repair.  A nearly weightless spectral level can create an
arbitrarily small action while contributing arbitrarily little to every physical capture moment.
A useful finite-order fixed-shell object is not action magnitude at one Hamiltonian but **action
transversality across the Hamiltonian ensemble**.  Its first-order oscillatory cancellation is
driven by `|grad phi_k|`, not by a global minimum of `|phi_k|`; this distinction does not by itself
supply the Brown-scale clock.

The second ingredient is kinematic and already existed abstractly in the formal corpus.  If a late
endpoint is hard, composing any earlier preparation with a circuit simulating the intervening local
evolution would prepare that endpoint.  Therefore a hard endpoint forces an exact backward lower
cone.  Local Hamiltonian simulation then turns the cone into an exponentially long, nearly linear
hardening shoulder.  The new use here is its quantitative composition with the ordinary-local
stabilizer plateau; the group-theoretic cone itself is not claimed new.

## Setup

Use the fixed-shell path-local ensemble from the parent card.  Thus

\[
 D=2^n,\qquad m=12n-9,\qquad
 H(\theta)=\sum_{a=1}^m\theta_aP_a,
 \qquad \theta\in S^{m-1},                                      \tag{2}
\]

with normalized spherical measure `sigma` and
`D^(-1) Tr H(theta)^2=1`.  Let `Stab_n` carry uniform measure.  Fix a finite local gate dictionary,
and let `Z_s` be all state targets prepared by words of length at most `s`; write

\[
 N_s=|Z_s|\le M_n^{s+1}.                                        \tag{3}
\]

Fix

\[
 0<\epsilon_-<\epsilon_+<1,\qquad
 a=1-\epsilon_+^2,\qquad
 \gamma=\epsilon_+-\epsilon_-.                                 \tag{4}
\]

On the simple-spectrum set, order the eigenvalues and write their rank-one spectral projectors as
`E_j(theta)` and `Pi_j(theta)`.  For `z in Z_s`, `chi in Stab_n`, put

\[
 c_j^{z,\chi}(\theta)=\langle z,\Pi_j(\theta)\chi\rangle.        \tag{5}
\]

All spectral expressions below are defined on this full-measure set.  On the exact degeneracy
locus they may be extended arbitrarily; every differentiated expression is multiplied by the
discriminant cutoff before it is used.

At replica order `r`, ordered tuples `alpha,beta in {1,...,D}^r` define

\[
 \Phi_{\alpha,\beta}(\theta)
 =\sum_{\ell=1}^rE_{\alpha_\ell}(\theta)
  -\sum_{\ell=1}^rE_{\beta_\ell}(\theta).                      \tag{6}
\]

The pair is diagonal if `alpha` and `beta` have the same multiplicity vector.  Otherwise `(6)` is
a nonzero balanced integer spectral action of height at most `r`.

## Theorem A -- replica coefficients have unit total variation

For every simple `theta`, every `z`, every `chi`, and every `r>=1`,

\[
 \left|\langle z,e^{-itH(\theta)}\chi\rangle\right|^{2r}
 =\sum_{\alpha,\beta}
 A_{\alpha,\beta}^{z,\chi}(\theta)
 e^{-it\Phi_{\alpha,\beta}(\theta)},                             \tag{7}
\]

where

\[
 A_{\alpha,\beta}^{z,\chi}
 =\prod_{\ell=1}^r c_{\alpha_\ell}^{z,\chi}
  \prod_{\ell=1}^r\overline{c_{\beta_\ell}^{z,\chi}},          \tag{8}
\]

and, crucially,

\[
 \boxed{
 \sum_{\alpha,\beta}|A_{\alpha,\beta}^{z,\chi}(\theta)|
 =\left(\sum_j|c_j^{z,\chi}(\theta)|\right)^{2r}\le1.}         \tag{9}
\]

### Proof

Equation `(7)` is the ordered multinomial expansion.  Orthogonality of the spectral subspaces and
Cauchy--Schwarz give

\[
 \sum_j|\langle z,\Pi_j\chi\rangle|
 \le
 \left(\sum_j\|\Pi_jz\|^2\right)^{1/2}
 \left(\sum_j\|\Pi_j\chi\|^2\right)^{1/2}=1.                  \tag{10}
\]

Raising `(10)` to power `2r` proves `(9)`.  No factor depending on `D`, `r`, number of spectral
characters, or circuit targets appears in this coefficient-mass bound.  Derivative constants
below may still depend on `D` and `r`, but no `D^(2r)` or character-count loss is forced.  This
removes a raw character-count loss.  It does not remove the exponentially small capture threshold
`(a/4)^r`; the later observer-crowding theorem shows that the resulting first-order estimate cannot
survive at Brown time when `r=Theta(D)`.

The abstract algebraic equality in `(9)` already has a read-only Lean proof as
`complexReplicaPairTotalVariation_eq_pow` in
`HTGeometry/TracelessReplicaDyadicActionShellLaw.lean`.  Specializing its one-copy coefficients to
`c_j` gives the equality; the spectral-projection contraction `(10)` and its filtered
specialization remain paper proofs during the corpus refactor.

The same proof survives every spectral filter `0<=w_j<=1`: replacing `c_j` by
`widetilde c_j=w_jc_j` only decreases the left side of `(10)`.  This filtered form is load-bearing
below.  A raw full-overlap moment has the weaker collision scale `C_H^(r/2)`; the sharp
`C_H^r` scale requires the common light-sector truncation used in the parent incidence theorem.

## Theorem B -- quantitative transversality dephasing

Let `Disc(theta)` be the nonnegative discriminant of the characteristic polynomial of
`H(theta)`.  Its zero set is the spectral degeneracy locus and has spherical measure zero.  For
`zeta>0`, choose a fixed smooth cutoff `rho_zeta` which is zero on
`{Disc<=zeta}` and one on `{Disc>=2zeta}`.

Let `K_r` be the finite set of nonzero balanced multiplicity characters of height at most `r`.
For `k in K_r`, write

\[
 \phi_k(\theta)=\sum_jk_jE_j(\theta).                            \tag{11}
\]

Define the replica transversality tail

\[
 \begin{aligned}
 Q_r(\zeta,g)
 :=\;&\sigma\{\operatorname{Disc}\le2\zeta\}\\
 &+\sigma\left\{\operatorname{Disc}\ge\zeta:\
       \min_{k\in K_r}\|\nabla_S\phi_k\|\le2g\right\}.
                                                                    \tag{12}
 \end{aligned}
\]

The fixed-shell nonflatness theorem proves that every `phi_k` has critical set of spherical
measure zero.  Since `K_r` is finite,

\[
 \boxed{
 \lim_{\zeta\downarrow0}\ \lim_{g\downarrow0}Q_r(\zeta,g)=0.}   \tag{13}
\]

Fix `L>=1`, put

\[
 c_0={2L\over D+1},                                               \tag{14}
\]

and choose a smooth collision cutoff `q_L` equal to one on `C_H(chi)<=c_0` and zero on
`C_H(chi)>=2c_0`.  For every fixed `n,r,s,L,zeta`, there is a finite explicitly defined derivative
constant `B=B(n,r,s,L,zeta)` as follows.

Choose one smooth nonincreasing `f:[0,infinity)->[0,1]` with `f(x)=1` for `x<=1` and `f(x)=0`
for `x>=2`.  For

\[
 p_j=\|\Pi_j\chi\|^2,\qquad C=\sum_jp_j^2,\qquad
 \tau={4C\over a},                                                \tag{15}
\]

define the common soft-light orbit

\[
 \Psi_L(t;\theta,\chi)
 =\sum_j f(p_j/\tau)e^{-itE_j}\Pi_j\chi.                          \tag{16}
\]

Then, uniformly in `z in Z_s`, `chi in Stab_n`, and `t!=0`,

\[
 \boxed{
 \left|
 \int q_L\,|\langle z,\Psi_L(t;\theta,\chi)\rangle|^{2r}d\sigma
 -I_{z,\chi,r}^{\mathrm{diag}}
 \right|
 \le
 Q_r(\zeta,g)
 +{B\over|t|}\left({1\over g}+{1\over g^2}\right).}             \tag{17}
\]

Here `I_diag` is the integral of the diagonal-multiplicity terms of the filtered version of `(7)`,
with the same collision and discriminant cutoffs.  Put `d=m-1` and

\[
 \begin{aligned}
 A_1&=\sup_{\theta,z,\chi}\sum_{\alpha,\beta\ {\rm off}}
   \|\nabla_S(q_L\rho_\zeta\widetilde A_{\alpha,\beta})\|,\\
 \mathcal H_r&=\sup_{\theta,k\in K_r}\|\nabla_S^2\phi_k(\theta)\|,\\
 B&=1+A_1+(d+4)\mathcal H_r .                                      \tag{18}
 \end{aligned}
\]

All suprema are on `{Disc>=zeta}` and `widetilde A` uses the filtered coefficients from `(16)`.
They also range over the finite sets `Z_s` and `Stab_n`.  Thus `B` is finite.  It does not hide a
character count: the first derivative sum is bounded by `2r` times the aggregate first derivative
of the filtered one-particle coefficients, while
`H_r<=2r sup_(theta,j)||nabla_S^2 E_j(theta)||` and the Hessian term is weighted by
`sum|widetilde A|<=1`.  Formula `(18)` is an admissible bound with no unnamed asymptotic constant.

### Proof

For a smooth phase `phi` on the sphere, on the region `|grad phi|>=g` set

\[
 X={\nabla_S\phi\over\|\nabla_S\phi\|^2}.                        \tag{17a}
\]

Since `X(e^{-it phi})=-it e^{-it phi}`, integration of
`div(a X e^{-it phi})` on the boundaryless sphere gives

\[
 \left|\int a e^{-it\phi}d\sigma\right|
 \le {1\over|t|}\int|\operatorname{div}(aX)|d\sigma.             \tag{17b}
\]

If `d=m-1` and `||Hess phi||<=K`, then

\[
 |X|\le g^{-1},\qquad
 |\operatorname{div}X|\le(d+2)K g^{-2}.                          \tag{17c}
\]

Choose this cutoff with derivative at most `2`: it is zero for `|grad phi|<=g` and one for
`|grad phi|>=2g`.  Its spatial derivative is at most `2K/g`, hence contributes at most
`2K/g^2` after multiplication by `|X|`.  Together with `(17c)`, this gives the coefficient
`(d+4)K/g^2` used in `(18)`.  The discarded part of the sphere is bounded by its measure.
The discriminant cutoff handles eigenvalue crossings and contributes to `B`.

Apply the integration-by-parts estimates to every non-diagonal term of the filtered expansion.  At
each `theta`, `(9)` bounds the total
absolute coefficient mass of all discarded terms by one.  Hence all bad-gradient pieces together
cost `Q_r(zeta,g)`, not `|K_r|Q_r`.  Summing the good-region integration-by-parts bounds gives the
second term of `(17)`.  The diagonal multiplicity terms have identically zero phase and remain in
`I_diag`.  This proves `(17)`.

### Algebraic corollary -- every finite replica order has a power-law transversality tail

For every fixed `n,r` there are `A_0,alpha_0,zeta_0>0` such that

\[
 \sigma\{\operatorname{Disc}\le2\zeta\}
 \le A_0\zeta^{\alpha_0}
 \qquad(0<\zeta\le\zeta_0).                                     \tag{18a}
\]

For every fixed `0<zeta<=zeta_0`, there are
`A_(r,zeta),alpha_(r,zeta),g_0>0` such that

\[
 \sigma\left\{\operatorname{Disc}\ge\zeta:\
       \min_{k\in K_r}\|\nabla_S\phi_k\|\le2g\right\}
 \le A_{r,\zeta}g^{\alpha_{r,\zeta}}
 \qquad(0<g\le g_0).                                             \tag{18b}
\]

Consequently

\[
 \boxed{
 Q_r(\zeta,g)
 \le A_0\zeta^{\alpha_0}
    +A_{r,\zeta}g^{\alpha_{r,\zeta}}.}                           \tag{18c}
\]

#### Proof

The coefficient sphere is a compact Nash manifold.  `Disc` is a nonzero polynomial on it because
the local family contains a simple-spectrum member.  Its zero set is therefore a proper compact
semialgebraic subset.  The semialgebraic Lojasiewicz inequality gives constants `c,N>0` with

\[
 \operatorname{Disc}(\theta)
 \ge c\,\operatorname{dist}(\theta,Z_{\rm disc})^N.
\]

A finite semialgebraic stratification of the proper set `Z_disc` has dimensions at most `m-2`;
the spherical volume of its `u`-tube is at most a finite constant times a positive power of `u`.
Combining the two facts proves `(18a)`.

On `{Disc>=zeta}`, every ordered eigenvalue is a Nash function of `theta`: it is an analytic
semialgebraic root of the characteristic polynomial.  Hence
`h_k=||grad_S phi_k||^2` is Nash.  Fixed-shell nonflatness says its zero set has empty interior for
every `k in K_r`; therefore that zero set is again a proper semialgebraic subset of codimension at
least one.  Apply the same Lojasiewicz-plus-tube argument to every `h_k`.  The set `K_r` is finite,
so summing the finitely many bounds and taking the smallest exponent proves `(18b)` and `(18c)`.

This corollary admits finite-size algebraic certificates: quantifier elimination together with a
Whitney--Lojasiewicz certificate can in principle supply the displayed constants.  No feasible
algorithm, or useful dependence on `n` or growing `r`, is claimed.

## Theorem C -- an explicit fixed-shell plateau-onset bound

Set

\[
 r=\left\lfloor{a^2(D+1)\over256L}\right\rfloor                 \tag{19}
\]

and assume `r>=1` and

\[
 s+1\le {r\log2\over2\log M_n}.                                  \tag{20}
\]

Let

\[
 G_L=\{(\theta,\chi):C_{H(\theta)}(\chi)\le c_0\}.               \tag{21}
\]

For any `q>0`, choose `zeta,g>0` so that

\[
 Q_r(\zeta,g)\le {q (a/4)^r\over2N_s}.                           \tag{22}
\]

Such a choice exists by `(13)`.  More concretely, `(18c)` permits first choosing `zeta` so its
first term is at most half the right side of `(22)`, and then choosing `g` so its second term is at
most the other half.  Define

\[
 \boxed{
 T_{\mathrm{tr}}
 ={2B(n,r,s,L,\zeta)N_s\over q (a/4)^r}
   \left({1\over g}+{1\over g^2}\right).}                       \tag{23}
\]

Then **every** fixed-shell laboratory time `t>=T_tr` satisfies

\[
 \boxed{
 \Pr_{\theta,\chi}
 \left(G_L\cap
 \{C_{\epsilon_+}(e^{-itH(\theta)}\chi)\le s\}\right)
 \le2^{-r/2}+q.}                                                  \tag{24}
\]

Consequently

\[
 \Pr\{C_{\epsilon_+}(e^{-itH}\chi)>s\}
 \ge1-{1\over L}-2^{-r/2}-q.                                    \tag{25}
\]

### Proof

For the soft filter `(16)`, the removed spectral norm obeys

\[
 \|e^{-itH}\chi-\Psi_L(t)\|^2
 \le\sum_{p_j>\tau}p_j
 \le C/\tau=a/4.                                                   \tag{26}
\]

If a depth-`s` target captures the full evolved state at error `epsilon_+`, its overlap magnitude
is at least `sqrt(a)`, so its soft-light overlap magnitude is at least `sqrt(a)/2`.  Therefore

\[
 (a/4)^r\mathbf1_{\mathrm{shortcut}}
 \le\sum_{z\in Z_s}|\langle z,\Psi_L(t)\rangle|^{2r}.            \tag{27}
\]

The soft cutoff is one on `G_L` and supported where collision is at most `2c_0=4L/(D+1)`.  The
filter is supported only where `p_j<2tau=8C/a`.  This filter depends on the Hamiltonian--seed pair
but not on the circuit target, so it is common to the complete target union.  Put
`q_j=||Pi_j z||^2`.  Then

\[
 |\widetilde c_j|^2
 \le p_jq_j\mathbf 1_{p_j<8C/a},\qquad
 \sum_j|\widetilde c_j|^2\le {8C\over a}\sum_jq_j={8C\over a}.    \tag{27a}
\]

If `xi_j` are independent uniform phases, exact Steinhaus orthogonality identifies the diagonal
multiplicity sum with `E|sum_j xi_j widetilde c_j|^(2r)`.  Expanding by multiplicity vectors gives

\[
 \sum_{\ell_1+\cdots+\ell_D=r}
 \left({r!\over\prod_j\ell_j!}\right)^2
 \prod_j|\widetilde c_j|^{2\ell_j}
 \le r!\left(\sum_j|\widetilde c_j|^2\right)^r
 \le r!\left({8C\over a}\right)^r.                              \tag{27b}
\]

The first inequality uses `prod_j ell_j!>=1` term by term against the multinomial expansion.
Dividing by the capture margin in `(27)`, summing the circuit targets, and using the collision
cutoff bounds the completed contribution by

\[
 N_s r!\left({128L\over a^2(D+1)}\right)^r
 \le N_s2^{-r}\le2^{-r/2},                                      \tag{28}
\]

using `(19)--(20)`.  Theorem B, summed over `Z_s` and divided by `(a/4)^r`, contributes at most `q`
by `(22)--(23)`.  This proves `(24)`.  The stabilizer two-design collision identity and Markov give
`Pr(G_L^c)<=1/L`, proving `(25)`.

Unlike the parent Riemann--Lebesgue proof, `(23)` is a uniform all-future onset bound made from
finite geometric data of the fixed interaction shell.  No random radius, minimum spectral gap,
minimum replica action, fresh noise, or random observation time occurs.

This is a finite-size effectiveness statement, not a Brown-scale estimate.  For fixed
`0<q<=1`, since `B,N_s>=1`, `0<a<1`, and the required small-gradient threshold has `g<1` at large
replica order, the formula itself gives

\[
 T_{\mathrm{tr}}\ge {2\over q}(4/a)^r.                         \tag{23a}
\]

Thus at `r=Theta(D)` this first-order onset architecture is necessarily `exp(Theta(D))`, regardless
of any improvement to `Q_r` or `B`.

## Corollary D -- explicit continuous-block onset

For a desired length `W`, use the parent grid

\[
 N_W=\left\lceil{W\sqrt{12n-9}\over\epsilon_+-\epsilon_-}\right\rceil+1.
                                                                    \tag{28a}
\]

Apply Theorem C with `q/N_W` in place of `q` and let `T_block` be the resulting value `(23)`.
Then every `A>=T_block` obeys

\[
 \boxed{
 \Pr\left\{\forall t\in[A,A+W],\
 C_{\epsilon_-}(e^{-itH(\theta)}\chi)>s\right\}
 \ge1-{1\over L}-N_W2^{-r/2}-q.}                                 \tag{29}
\]

The proof is the same finite grid union and deterministic speed interpolation as in the parent
card.  The collision-bad pair set is paid once.  Taking `N_W<=2^(r/4)` again gives continuous
duration `2^(Omega(D/L))` at depth `Omega(D/(L log n))`, now with onset bounded by the exact
transversality condition number `(23)` rather than an unnamed Riemann--Lebesgue threshold.

## Theorem E -- robust circuit hardening cone

`[ABSTRACT OPERATOR FORM LEAN-PROVED; STATE-ORBIT FORM PAPER-PROVED]`

This theorem is deterministic and applies to every unitary trajectory, not only the ensemble
above.  Let `psi_t=U_t psi_0` with `U_{t+u}=U_uU_t`.  Let

\[
 S_H(u,\delta)
 =\min\{|w|:\|W_w-U_u\|_{\mathrm{op}}\le\delta\}                \tag{30}
\]

be approximate unitary simulation complexity in the same gate model.  If

\[
 C_{\epsilon_+}(\psi_T)>s,
\]

then for every `0<=u<=T`,

\[
 \boxed{
 C_{\epsilon_-}(\psi_{T-u})
 >s-S_H(u,\gamma).}                                               \tag{31}
\]

Also, if `C_0(psi_0)<=b`, every such hard time satisfies

\[
 \boxed{S_H(T,\epsilon_+)>s-b.}                                  \tag{32}
\]

### Proof

If a word of length `c` prepares `psi_(T-u)` to error `epsilon_-` and a word of length `k`
approximates `U_u` in operator norm to error `gamma`, their composition prepares `psi_T` to error
at most `epsilon_-+gamma=epsilon_+` with `c+k` gates.  Hence

\[
 C_{\epsilon_+}(\psi_T)
 \le C_{\epsilon_-}(\psi_{T-u})+S_H(u,\gamma),                    \tag{33}
\]

which proves `(31)`.  Composing an exact preparation of `psi_0` with an `epsilon_+` simulator for
`U_T` proves

\[
 C_{\epsilon_+}(\psi_T)\le b+S_H(T,\epsilon_+),                  \tag{34}
\]

and therefore `(32)`.

For the nearest-neighbour chain `(2)`, rigorous lattice-Hamiltonian simulation gives gate cost
`(n|u|)^(1+o(1))` at fixed accuracy; compiling its local gates into a fixed universal alphabet
preserves this nearly linear dependence up to subpolynomial factors.  Thus every robust endpoint
at the plateau depth

\[
 s=\Omega\!\left({2^n\over L\log n}\right)                      \tag{35}
\]

has a compulsory backward hardening shoulder on a physical interval of length

\[
 \boxed{2^{n(1-o(1))}}                                           \tag{36}
\]

for every subexponential `L`.  More exactly, `(31)` is the lower envelope; `(36)` is obtained by
choosing the largest `u` for which the known simulation upper bound is at most a fixed fraction of
`s`.

This is not monotonicity.  Complexity may fluctuate above the envelope.  It proves something a
mere late hard block did not: bounded-strength locality forbids plateau-scale state complexity from
appearing on the zero-complexity escape timescale.  Every first robust entrance into plateau-scale
complexity is preceded by an exponentially long simulation-cost cone.

## Unified capacity--clock--speed law

The two parent theorems and Theorems B--E identify three faces of one replicated spectral orbit:

\[
 \boxed{
 \begin{array}{c|c}
 \text{spectral datum} & \text{complexity-history role}\\ \hline
 C_H(\chi) & \text{plateau capacity and logarithmic lifetime}\\
 Q_r(\zeta,g),\ B(n,r,s,L,\zeta) & \text{finite-order fixed-shell onset clock}\\
 S_H(u,\delta) & \text{maximum approach/escape speed}
 \end{array}}                                                     \tag{37}
\]

For collision `c`, the certified plateau depth is `Omega(1/(c log M_n))` and logarithmic lifetime
is `Omega(1/c)`.  At every fixed finite size and replica order, the transversality profile decides
when completed capacity becomes visible at a common laboratory time.  It does not supply the
Brown-scale clock at growing `r`.  Simulation complexity forces the approach to that capacity to
occupy at least the time needed to synthesize `Omega(1/(c log M_n))` gates.  Recurrence later returns
the same orbit to its efficient seed, while the existing two-query witness keeps locality
distinguishable from Haar randomness at every stage.

Collision, onset and growth are therefore not three unrelated estimates.  They are respectively
the diagonal mass, transverse motion, and physical propagation speed of one spectral phase tensor.

## Conjecturing protocol

### C0 -- collision alone controls the full complexity history

**Verdict:** `[FALSIFIED]` by `(1)`.

Equal collision permits arbitrarily different dephasing times.  Collision controls capacity, not
the clock that resolves it.

### C1 -- minimum nonzero replica action supplies the missing clock

**Verdict:** `[FALSIFIED AS THE RIGHT INVARIANT]`.

An action involving a vanishing-weight level can be arbitrarily small while its total moment weight
vanishes.  A minimum also cannot exploit oscillatory cancellation across Hamiltonian space.

**Finite-order survivor:** retain action weights and ensemble transversality.  The
unit-total-variation identity `(9)` removes raw character counting, but the observer-crowding card
proves that positive first-gradient control is still insufficient at Brown replica order.

### C2 -- radial disorder gives a quantitative onset

**Verdict:** `[TRUE BUT PHYSICALLY REJECTED]`.

A random Hamiltonian scale makes each action acquire an explicit one-dimensional Fourier kernel,
but normalizing time by interaction strength cancels that randomness.  It does not solve fixed-rate
onset.

**Finite-order survivor:** integrate by parts in angular Hamiltonian space, where every member has
the same interaction rate.  This yields finite-size effectiveness only.

### C3 -- action-gradient transversality quantitatively replaces Riemann--Lebesgue

**Verdict:** `[PAPER-PROVED AT EACH FIXED FINITE REPLICA ORDER; BROWN-SCALE ROUTE RETIRED]`.

The nowhere-flat action theorem makes every critical set null.  Finite replica order makes their
union finite.  Equations `(9)` and `(17)` yield the all-future bound `(24)` without an action-count
loss; the soft collision cutoff preserves the one-time payment of the bad pair set.  Equation
`(23a)` and the observer-crowding law prove that this first-order mechanism has the wrong
large-replica clock.

### C4 -- a hard plateau may still appear by an extremal jump

**Verdict:** `[FALSE FOR LOCAL SIMULABLE DYNAMICS]`.

Reverse circuit composition proves `(31)`.  Nearly linear local-Hamiltonian simulation turns it
into the exponential hardening interval `(36)`.

### C5 -- the result proves Brown--Susskind linear growth from time zero

**Verdict:** `[FALSE]`.

The transversality threshold `(23)` is structurally at least exponential in `r`, and `(31)` is a
lower cone before a robust hard endpoint, not pointwise monotonicity from `t=0`.  The first gap
cannot be closed by better constants in this proof; the replacement frontier is signed growing-
replica cancellation together with removal or classification of pre-cone delay.

## Hostile review

1. **First-order onset has the wrong asymptotic scale.** `T_tr` is explicit in finite geometric
   data, but `(23a)` forces `T_tr=exp(Theta(r))` for fixed error probability before `Q_r`, `B`, or
   spectral-gap estimates enter.  Observer compression also forces exponentially small worst
   gradients.  This theorem cannot show Brown-time onset.
2. **Hardening cone is not monotonic growth.** Equation `(31)` forbids a fast approach to a hard
   endpoint but allows oscillations and a long pre-cone delay.
3. **Continuous-disorder information remains.** The ensemble contains real-valued couplings.  The
   result does not imply a superpolynomial lower bound for a uniformly specified polynomial-bit
   Hamiltonian and therefore does not silently resolve a circuit-complexity-class separation.
4. **State complexity only.** Full unitary complexity and the black-hole/CFT dictionary require
   separate theorems.
5. **Disordered path family.** Translation invariance and deterministic physical models remain
   outside scope.
6. **Finite gate dictionary.** Continuous gates, measurements, discarded ancillas, and fault
   tolerance need their own entropy and simulation accounting.
7. **Classical ingredients.** Nonstationary phase and Hamiltonian simulation are known.  Candidate
   new knowledge is their exact composition with nowhere-flat local spectral actions, the
   unit-variation growing-replica identity, collision-first restriction, full circuit union, and
   the pathwise plateau theorem.
8. **Formal gate remains partly closed.** The abstract paired-replica variation equality and
   operator-norm cone are already Lean-proved in
   `HTGeometry/TracelessReplicaDyadicActionShellLaw.lean` and
   `HTGeometry/AutonomousWordComplexityConeLaw.lean`.  Projection contraction `(10)`, the common
   soft-light filter, action-gradient cutoff estimate, fixed-shell onset theorem, and state-orbit
   specialization have not been formalized.  No final paper claim using those steps is authorized
   yet.

## External separation audit

- The 2026 Physics Reports review on quantum complexity identifies superpolynomial lower bounds
  for typical time-independent local Hamiltonians as a major open frontier and relates uniform
  explicit versions to difficult complexity-class separations:
  <https://arxiv.org/abs/2503.10753>.
- Kotowski--Oszmaniec--Horodecki prove extremal complexity jumps for GUE and Haar-random-eigenbasis
  Hamiltonians.  Unitary invariance and nonlocal eigenvectors are load-bearing; they do not prove a
  local hardening cone or fixed-shell action-transversality onset:
  <https://arxiv.org/abs/2303.17538>.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence for random circuits
  and stochastic local Hamiltonian evolution, not one ordinary static local generator:
  <https://arxiv.org/abs/2205.09734>.
- Childs--Su prove nearly optimal `(nt)^(1+o(1))` product-formula simulation of nearest-neighbour
  lattice Hamiltonians.  That theorem supplies the upper simulator used in `(36)` and is not
  claimed new: <https://arxiv.org/abs/1901.00564>.

Targeted searches located no theorem combining fixed interaction strength, nowhere-flat replica
spectral actions of an ordinary local family, a finite-size quantitative transversality onset bound,
a complete circuit union, a doubly-exponential same-trajectory plateau, and a deterministic
hardening cone.  This is separation evidence, not a final priority determination; the present card
now explicitly rejects a Brown-scale extrapolation of that finite-size onset bound.

## Remaining frontier

1. Do not optimize `Q_r` or `B` for Brown scale; that route is retired by `(23a)` and
   `observer-dimension-replica-action-crowding-law.md`.
2. Prove or falsify `../1-in-progress/scale-matched-signed-action-packet-law.md` using the exact
   final-return-projected signed convolution lift.  Higher-order alternatives are admissible only
   if they are not positive first-order unresolved-action majorants in disguise.
3. Upgrade the hardening cone to a pointwise lower ramp from the initial seed, or prove an exact
   obstruction showing why a pre-cone delay is unavoidable.
4. After corpus refactoring, reuse the existing formal autonomous cone and formalize only the
   finite-size claims `(9)`, `(24)`, and `(31)`; do not encode the retired Brown-scale inference.

## Lean status -- Theorem A is already in the corpus

Searched before building.  Both halves of Theorem A are formalized.

| Card item | Existing declaration |
|---|---|
| **`(7)`, the ordered multinomial expansion** of the replica fidelity | `complexFidelityReplicaMultiplicityExpansion` (`HTGeometry/FidelityReplicaCharacterCoefficientLaw.lean`) |
| the total variation of all signed paired replica coefficients | `complexReplicaPairTotalVariation` (`HTGeometry/TracelessReplicaDyadicActionShellLaw.lean`) |
| **`(9)`, the equality half**: the total variation of one multinomial replica layer is exactly the `r`-th power of the one-copy coefficient variation | `sum_norm_complexReplicaMultiplicityAmplitude_eq_pow` (same module) |
| the underlying product-of-sums identity | `Fintype.sum_pow` (mathlib) |

`sum_norm_complexReplicaMultiplicityAmplitude_eq_pow` is exactly `(9)`'s
`Σ_{α,β}|A_{α,β}| = (Σ_j|c_j|)^{2r}`; the remaining `≤ 1` is the Cauchy--Schwarz step
`Σ_j |⟨z, Π_j χ⟩| ≤ 1` for unit vectors and orthogonal spectral projections.

### The `≤ 1` clause is closed

`formal/GaloisForLFunctions/HTGeometry/UnitCoefficientVariation.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| **the Cauchy--Schwarz step**: the spectral overlaps of two unit vectors sum in modulus to at most one | `sum_norm_mul_le_one` |
| any power of a quantity in `[0,1]` stays there | `pow_le_one_of_variation` |
| **`(9)` complete**: the paired replica coefficients have total variation at most one, at every replica order | `replica_variation_le_one` |

**Theorem A is therefore complete**: `complexFidelityReplicaMultiplicityExpansion` gives `(7)`,
`sum_norm_complexReplicaMultiplicityAmplitude_eq_pow` gives the equality of `(9)`, and
`replica_variation_le_one` gives its `≤ 1`.  The bound is uniform in the Hamiltonian, its spectrum
and the replica order, exactly as the card asserts.

### Theorems B, C and E -- the formal layer

`formal/GaloisForLFunctions/HTGeometry/NonstationaryPhaseVectorField.lean`,
`SoftLightCaptureFloor.lean`, `StateOrbitHardeningCone.lean` (all new, umbrella-wired,
axiom-clean), together with the corpus modules named below.

| Card item | Declaration | Module |
|---|---|---|
| `(17a)`, `X(e^{-it phi}) = -it e^{-it phi}` | `inner_phaseField_eq_one` | `NonstationaryPhaseVectorField` |
| `(17c)` first half, `\|X\| <= g^{-1}` | `norm_phaseField_le` | `NonstationaryPhaseVectorField` |
| `(17c)` second half, `\|div X\| <= (d+2)Kg^{-2}` | `abs_trace_le_of_phaseFieldDeriv` | `NonstationaryPhaseVectorField` |
| `(26)`, the soft filter loses at most `a/4` | `sum_removed_softWeight_le` | `SoftLightCaptureFloor` |
| the removed vector carries exactly the removed weight | `sum_norm_sub_softFilter_sq` | `SoftLightCaptureFloor` |
| `(27)`, the capture floor `(a/4)^r` survives the filter | `capture_floor_le_inner_pow` | `SoftLightCaptureFloor` |
| capture at `epsilon_+` gives overlap `>= sqrt(1-epsilon_+^2)` | `norm_inner_ge_sqrt_one_sub_sq_of_traceDistance_le` | `RHTower/DirectAdaptiveStaticChoiShortcutActionLaw` |
| `(27a)`, filtered coefficient mass `<= 8C/a` | `norm_sq_coordOverlap`, `sum_le_threshold_of_product_bound` | `SoftLightCaptureFloor` |
| `(27b)`, `sum (multinomial)^2 prod \|c\|^{2l} <= r!(sum\|c\|^2)^r` | `fidelityReplicaPermutationFloor_le_factorial_mul_sum_sq_pow` | `RHTower/DirectAdaptiveStaticChoiShortcutActionLaw` |
| `(28)` first step, `r!x^r <= 2^{-r}` at `x <= 1/(2r)` | `factorial_mul_pow_le_half_pow` | `SoftLightCaptureFloor` |
| `(28)` second step, `(20)` gives `N_s <= 2^{r/2}` | `pow_le_two_rpow_of_log_le` | `SoftLightCaptureFloor` |
| `(28)` conclusion, `N_s 2^{-r} <= 2^{-r/2}` | `count_mul_half_pow_le` | `SoftLightCaptureFloor` |
| `(33)`, composition of preparation and simulation | `approxComplexity_evolved_le_add` | `StateOrbitHardeningCone` |
| `(31)`, state-orbit backward cone | `lt_add_uniformSimComplexity_of_lt_approxComplexity`, `sub_uniformSimComplexity_lt_approxComplexity` | `StateOrbitHardeningCone` |
| `(34)`--`(32)`, easy seed forces expensive simulation | `lt_add_uniformSimComplexity_of_easy_seed`, `sub_lt_uniformSimComplexity_of_easy_seed` | `StateOrbitHardeningCone` |
| `(31)` operator-norm form | `unitaryCircuitWordSeparated_autonomous_backward_cone` | `HTGeometry/AutonomousWordComplexityConeLaw` |
| `Pr(G_L^c) <= 1/L` | `card_filter_collision_gt_mul_le` | `HTGeometry/StabilizerCollisionMarkov` |

**Theorem E is therefore complete in both forms.**  The state-orbit form is no longer a paper
proof: `(31)` and `(32)` hold for every isometric flow on a metric state space with any gate
alphabet, with the finite-complexity witnesses as their only hypotheses.  The cone is stated in
signed form, `(s : Z) - S < C`, because truncated natural subtraction would weaken it at `s <= S`.

### What remains -- one missing infrastructure (the first is now built)

1. **The divergence theorem on a compact boundaryless Riemannian manifold.**  Estimate `(17b)`
   integrates `div(aXe^{-it phi})` over `S^{m-1}` and uses that the total divergence vanishes.
   Mathlib has the Gauss--Green theorem only on boxes, and a corpus search for a manifold form
   returns nothing.

   **First layer built.**  `HTGeometry/DivergenceCompactSupport.lean` (new, umbrella-wired,
   axiom-clean) proves the flat model: `integral_divergence_eq_zero_of_hasCompactSupport` --
   a continuously differentiable field on `R^m` vanishing outside a compact set has vanishing
   total divergence, together with `divergence_eq_zero_of_notMem_tsupport`.  The proof puts the
   support inside a box, kills all `2m` boundary fluxes, and uses mathlib's
   `integral_divergence_of_hasFDerivAt_off_countable`.

   **Second layer built.**  `HTGeometry/LebesguePolarIntegral.lean` (new, umbrella-wired,
   axiom-clean) proves polar coordinates for Lebesgue measure: `integral_eq_polar` turns every
   ambient integral into an integral over the sphere times the half line with the Jacobian carried
   by `Measure.volumeIoiPow`, `integral_volumeIoiPow_eq` writes that Jacobian as `r^{m-1}`, and
   `integral_polar_mul` separates a radial-times-angular integrand into the product of its radial
   and angular integrals.  This is exactly the step that converts a compactly supported radial
   cutoff into the angular integral.

   **Third layer built.**  `divergence_smul_of_homogeneous` (same module) proves that a
   degree-zero homogeneous field has divergence homogeneous of degree `-1`: scaling the point
   scales the derivative, hence the divergence, by the reciprocal.  That is the identity which
   turns the radial integral into the Jacobian factor.

   **Fourth and fifth layers built.**  `HTGeometry/DivergenceEuclidean.lean` transfers the flat
   theorem to Euclidean coordinates (`integral_euclideanDivergence_eq_zero`), through the
   measure-preserving linear identification -- the sphere, the radial variable and the polar
   decomposition all refer to the Euclidean norm, so this is the form the argument consumes.
   `HTGeometry/SphereDivergence.lean` then proves the differential identities:
   `hasFDerivAt_norm_of_ne_zero` (the gradient of the norm away from the origin),
   `hasFDerivAt_radialCutoff` and `euclideanDivergence_radialCutoffDeriv` (**the product rule**:
   `div(phi(|x|)X) = phi(|x|) div X` for a *tangential* field, the radial term dying by
   tangentiality), and
   `euclideanDivergence_smul_of_homogeneous` (degree `-1` homogeneity in Euclidean coordinates).

   **The blocker is closed.**  `integral_toSphere_euclideanDivergence_eq_zero`
   (`HTGeometry/SphereDivergence.lean`) is the divergence theorem on the unit sphere: for a
   tangential, degree-zero homogeneous, continuously differentiable field, the total divergence
   over the sphere vanishes.  The proof is exactly the paper argument -- multiply by a radial
   cutoff supported in `(1/2, 2)`, note the cut-off field is `C^1` at the origin as well because it
   vanishes near it, apply the flat theorem, separate the radial and angular factors by
   `integral_polar_mul`, and divide by the nonzero radial integral.

   **`(17b)` itself is now formal.**  `HTGeometry/NonstationaryPhaseSphere.lean` bundles the cutoff
   data (`RadialCutoff`), restates the sphere theorem against it (`integral_toSphere_eq_zero`), and
   proves the oscillatory divergence identities
   `div(a sin(t phi) X) = sin(t phi) div(aX) + t a cos(t phi)` and its cosine companion
   (`euclideanDivergence_sin_smul`, `euclideanDivergence_cos_smul`, with
   `amplitudeDivergence` for `div(aX)` and `sum_apply_single_mul` recovering a functional from its
   basis values).  `abs_oscillatory_le` is the final step: a vanishing total divergence turns each
   identity into `|t| |int a cos(t phi)| <= int |div(aX)|`, which is exactly `(17b)`.

   The chain is: `integral_divergence_eq_zero_of_hasCompactSupport` (flat Gauss--Green) ->
   `integral_euclideanDivergence_eq_zero` (Euclidean coordinates) ->
   `hasFDerivAt_radialCutoff` + `euclideanDivergence_radialCutoffDeriv` (product rule, radial term
   killed by tangentiality) + `euclideanDivergence_smul_of_homogeneous` (degree `-1` homogeneity)
   + `integral_polar_mul` (radial--angular separation) ->
   `integral_toSphere_euclideanDivergence_eq_zero`.  Every step is unconditional and axiom-clean;
   mathlib has none of them.  Everything else in Theorem B is now formal: `(17a)`, both halves of `(17c)`,
   and the coefficient-mass input `(9)` that makes the discarded part cost `Q_r` rather than
   `|K_r|Q_r`.  This is the single analytic construction the theorem still needs.
2. **The semialgebraic Lojasiewicz inequality with a tube-volume bound.**

   **First layer built.**  `HTGeometry/PolynomialSublevelMeasure.lean` (new, umbrella-wired,
   axiom-clean) proves the elementary one-dimensional form of exactly this estimate:
   `exists_norm_sub_le_of_prod_le` (a small product of `d` distances forces one small distance),
   `sublevel_subset_iUnion` (hence the sublevel set is covered by `d` intervals of half-length
   `delta`), and `volume_sublevel_le` (so its Lebesgue measure is at most `2 d delta`, with
   `delta = (eps/a)^{1/d}` for a degree-`d` product with leading coefficient `a`).  This is the
   root-factorisation route to a power-law sublevel bound: no stratification, no Lojasiewicz
   exponent, just the roots.

   **The blocker is closed.**  Three new modules carry the one-dimensional bound to the sphere,
   all umbrella-wired and axiom-clean.

   | Card item | Declaration | Module |
   |---|---|---|
   | the complex roots of a real polynomial as a tuple, and `\|q(t)\| = \|a\| prod \|t - z_i\|` | `exists_roots_tuple` | `HTGeometry/PolynomialLineSlice` |
   | **the one-variable sublevel law** `\|{\|q\| <= eps}\| <= 2 d (eps/\|a\|)^{1/d}` | `volume_polynomial_sublevel_le` | same |
   | the restriction of a polynomial to a line | `lineSlice`, `lineSlice_eval` | same |
   | **its top coefficient is the top form at the direction**, independent of the base point | `coeff_lineSlice` | same |
   | the degree and leading coefficient of a slice in a nondegenerate direction | `natDegree_lineSlice_eq`, `leadingCoeff_lineSlice` | `HTGeometry/PolynomialSublevelSlicing` |
   | a direction with nonvanishing top form and nonzero first coordinate exists | `exists_direction` | same |
   | **the sliced sublevel bound** (Fubini over the transverse coordinates) | `volume_prod_sublevel_le` | same |
   | the shear parametrisation pushes the product measure to `\|v_0\|` times Lebesgue | `volume_shear_preimage` | same |
   | homogeneous scaling `P(r x) = r^d P(x)` | `eval_smul_of_isHomogeneous` | `HTGeometry/PolynomialSublevelSphere` |
   | **the ambient sublevel bound** on a box | `volume_sublevel_le_of_direction` | same |
   | **`(18)`-type shell bound**: `mu_S{\|P\| <= eps} <= C eps^{1/d}` for a nonzero homogeneous `P` | `exists_toSphere_sublevel_le` | same |

   The route replaces the semialgebraic Lojasiewicz step by the top-form slicing: no Nash manifold,
   no stratification, no Carbery--Wright.  Letting the level tend to zero also gives the
   degeneracy-locus statement the card uses in `(12)`: **the zero set of a nonzero homogeneous
   polynomial has spherical measure zero** (`toSphere_zeroSet_eq_zero`).  What the corollary still
   needs from the geometry is the identification of the discriminant as a nonzero homogeneous
   polynomial of an explicit degree in the shell coordinates.

With those two in place, `(17)`, `(18c)`, `(22)`--`(25)` and Corollary D are assembly over the
already-formal pieces above.

### What remains

Theorem B (quantitative transversality dephasing) and its algebraic
corollary; Theorem C (the explicit plateau-onset bound); Corollary D; Theorem E (the robust
hardening cone).

## Lean progress -- the aggregation step of `(17)` (2026-08-19)

`formal/GaloisForLFunctions/HTGeometry/AggregatedOscillatoryMass.lean` (new, umbrella-wired,
axiom-clean) formalises the step the card singles out as the load-bearing use of Theorem A:

> "At each `theta`, `(9)` bounds the total absolute coefficient mass of all discarded terms by one.
> Hence all bad-gradient pieces together cost `Q_r(zeta,g)`, not `|K_r|Q_r`."

| Card item | Declaration |
|---|---|
| the oscillatory factor of a real phase, and that it has unit modulus | `oscFactor`, `norm_oscFactor`, `norm_mul_oscFactor` |
| **the discarded region costs one copy of its measure**, with no factor counting the terms | `sum_norm_setIntegral_le_measure` |
| the diagonal split: the deviation from the zero-phase terms is at most the sum of the remaining moduli | `norm_integral_sub_diagonal_le` |
| **`(17)` in aggregated form**: deviation `≤ μ(discarded) + ∑ (individual good-region bounds)` | `norm_integral_sub_diagonal_le_measureReal_add` |

The statement is deliberately free of the sphere, the spectrum and the particular phases: it takes
a finite family, a unit total coefficient mass on the discarded set, a discarded set of finite
measure, and whatever individual bounds hold on the complement.  Composing it with
`abs_oscillatory_le` (`HTGeometry/NonstationaryPhaseSphere`) for the good-region bounds and with
`replica_variation_le_one` (`HTGeometry/UnitCoefficientVariation`) for the mass hypothesis is
exactly `(17)`; the remaining work is supplying the two ingredient families for the fixed-shell
spectral data, not any further analysis.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

## Lean progress -- the discriminant is a polynomial, and `(18a)` (2026-08-19)

The corollary's remaining input was named on this card as

> "What the corollary still needs from the geometry is the identification of the discriminant as a
> nonzero homogeneous polynomial of an explicit degree in the shell coordinates."

`formal/GaloisForLFunctions/HTGeometry/SpectralDiscriminantPolynomial.lean` (new, umbrella-wired,
axiom-clean) supplies exactly that, for an arbitrary Hermitian family `P₁, …, P_N` and its
Hamiltonian `H(θ) = ∑ θ_a P_a`.

| Card item | Declaration |
|---|---|
| the Hamiltonian at a coefficient vector, and its Hermiticity | `spectralEnsembleMatrix`, `isHermitian_spectralEnsembleMatrix` |
| the same Hamiltonian over the polynomial ring in `θ` | `spectralGenericMatrix` |
| the Hankel matrix of its power traces, and the discriminant as its determinant | `spectralTraceHankel`, `spectralDiscriminantC` |
| **the power-trace Hankel matrix is `VᵀV`, so its determinant is the squared Vandermonde** | `det_powerSum_hankel` |
| **reality**: coefficientwise conjugation transposes the generic matrix, so the determinant has real coefficients | `mapMatrix_conj_spectralGenericMatrix`, `map_conj_spectralDiscriminantC`, `map_spectralDiscriminantPoly` |
| **`Disc` as a real multivariate polynomial in `θ`** | `spectralDiscriminantPoly` |
| **homogeneous of degree `D(D−1)`** | `spectralDiscriminantDegree`, `isHomogeneous_spectralDiscriminantPoly` |
| **it evaluates to `∏_{i<j}(E_i(θ) − E_j(θ))²`**, hence is nonnegative | `eval_spectralDiscriminantPoly`, `spectralDiscriminantPoly_nonneg` |
| **it is a nonzero polynomial** as soon as one member of the family has simple spectrum | `spectralDiscriminantPoly_ne_zero` |
| **`(18a)`**: `σ{Disc ≤ ε} ≤ C ε^{1/(D(D−1))}` | `exists_toSphere_spectralDiscriminant_sublevel_le` |

The construction deliberately avoids the discriminant of the characteristic polynomial and the
semialgebraic machinery: the entry `Tr H(θ)^{i+j}` is visibly a polynomial in `θ` of degree `i+j`,
so every permutation term of the determinant has the *same* degree `∑_i (σ(i) + i) = D(D−1)` and
homogeneity is immediate; and the Hankel matrix is `VᵀV` for the Vandermonde matrix of the
spectrum, so the determinant is `(det V)²`, which is the product of the squared eigenvalue
differences.  Reality is Hermiticity: conjugating coefficients transposes the generic matrix, and
transposition fixes every trace.

Composed with `exists_toSphere_sublevel_le` this closes `(18a)` unconditionally, with the exponent
`1/(D(D−1))` explicit.  The one hypothesis is the card's own: the family must contain a
simple-spectrum member, which is exactly the sentence "Disc is a nonzero polynomial on it because
the local family contains a simple-spectrum member".

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

### What `(18b)` still needs

`(18b)` bounds the sublevel sets of `h_k = ‖∇_S φ_k‖²`, which is *not* polynomial in `θ` -- the
eigenvalues are algebraic, not rational, functions of the coefficients.  The polynomial-slicing
route above therefore does not apply verbatim.  Two routes remain: eliminate the eigenvalues to
get a polynomial in `θ` whose zero set contains the critical locus, or drop the power law and prove
only the boxed limit `(13)`, which follows from continuity of `h_k` on `{Disc ≥ ζ}` together with
the fixed-shell nonflatness statement that its zero set is shell-null.

## Lean progress -- the assembly of Theorem C and Corollary D (2026-08-19)

Every *ingredient* of Theorem C was already in the corpus (the soft-filter loss `(26)`, the capture
floor `(27)`, the filtered coefficient mass `(27a)`, the permutation floor `(27b)`, the three steps
of `(28)`, and the collision Markov bound).  What was missing was the assembly: how the capture
floor plus a split of each integral becomes the two-term probability bound `(24)`, and how the
finite grid becomes `(29)`.  Two new modules, umbrella-wired and axiom-clean, supply exactly that.

`formal/GaloisForLFunctions/HTGeometry/OnsetProbabilityAssembly.lean`

| Card item | Declaration |
|---|---|
| **integrating the capture floor**: a margin dominated on the event by a finite sum of non-negative observables is dominated by the total of their integrals | `mul_measureReal_le_of_capture` |
| **`(24)`**: with each integral split into a diagonal part and a deviation, and each family summing to the margin times a small number, the event has measure at most the sum of those numbers | `measureReal_le_of_capture_split` |
| **`(25)`**: the complementary reading, with the exceptional event removed by a union bound | `one_sub_le_measureReal_compl` |

`formal/GaloisForLFunctions/HTGeometry/GridUnionOnset.lean`

| Card item | Declaration |
|---|---|
| a finite union of uniformly small events, with the grid size the only loss | `measureReal_iUnion_le_card_mul` |
| **`(29)`**: the continuous-block bound -- the good event contains the grid-good intersection with the non-exceptional event, so its probability is `≥ 1 − 1/L − N_W 2^{-r/2} − q` | `one_sub_le_measureReal_of_grid` |

The two statements are deliberately free of the shell, the spectrum and the circuit alphabet: they
take a finite family of non-negative integrable observables, a capture margin, a split of the
integrals, and (for the block form) a grid and an exceptional event.  Composing them with
`capture_floor_le_inner_pow` for the floor, with
`norm_integral_sub_diagonal_le_measureReal_add` for the split, with
`fidelityReplicaPermutationFloor_le_factorial_mul_sum_sq_pow`, `factorial_mul_pow_le_half_pow`,
`pow_le_two_rpow_of_log_le` and `count_mul_half_pow_le` for the diagonal total, and with
`card_filter_collision_gt_mul_le` for the exceptional mass, is Theorem C and Corollary D.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

## Lean progress -- the boxed `(13)`, without the power law

`(18b)` -- the *power-law* bound on the sublevel sets of `‖∇_S φ_k‖` -- is not what Theorem B and
Theorem C actually consume.  What they consume is the boxed `(13)`,
`lim_{ζ↓0} lim_{g↓0} Q_r(ζ,g) = 0`, and that follows from the nullity of the critical sets alone,
with no Łojasiewicz exponent and no semialgebraic geometry.

`formal/GaloisForLFunctions/HTGeometry/SublevelVanishing.lean` (new, umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| **sublevel sets of a function with null zero set are eventually small** | `exists_small_sublevel` |
| the same for a finite family, simultaneously | `exists_small_finite_sublevel` |
| **`(13)` in `ε`-form**: a discriminant threshold and a gradient threshold whose two discarded regions together weigh less than any prescribed tolerance | `exists_small_transversalityTail` |

The mechanism is continuity of measure from above: the sublevel sets `{|f| ≤ 1/(n+1)}` decrease,
their intersection is exactly the zero set, and the shell measure is finite, so their masses
converge to the mass of the zero set.  A finite family is handled by cutting each at tolerance
`ε/|K|` and taking the smallest threshold.

So `Q_r(ζ,g)` can be made arbitrarily small using only:

* `σ{Disc = 0} = 0` -- already proved, and in the sharper power-law form, by
  `exists_toSphere_spectralDiscriminant_sublevel_le` together with
  `SpectralDiscriminantPolynomial`;
* `σ{‖∇_S φ_k‖ = 0} = 0` for each of the finitely many `k ∈ K_r` -- the fixed-shell nonflatness
  theorem, which is the parent card's Theorem A.

`(18b)` remains a sharpening -- it gives the *rate* `A g^α` rather than mere vanishing, and the
onset constant `(23)` is stated with an explicit `g` -- but the boxed `(13)`, which is what the
card asserts and what Theorem C's choice `(22)` needs, no longer waits on any semialgebraic input.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.
