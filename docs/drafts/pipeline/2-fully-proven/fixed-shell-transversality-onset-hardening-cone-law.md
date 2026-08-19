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

## Lean progress -- the elimination step for `(18b)`

The card names two routes for `(18b)`: a semialgebraic Łojasiewicz inequality, or *eliminate the
eigenvalues to get a polynomial in `θ` whose zero set contains the critical locus*.  The second
route is the buildable one, and its first step is now formal.

`formal/GaloisForLFunctions/HTGeometry/LabeledActionSymmetricPolynomial.lean` (new,
umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| the spectral action at one labelling of the spectrum, `∑_j k_j E_{π(j)}` | `labeledAction` |
| relabelling the eigenvalues translates the labelling | `rename_labeledAction` |
| the symmetrised action polynomial `∏_π (Y − ∑_j k_j E_{π(j)})` | `labeledActionPoly` |
| relabelling permutes its factors, hence fixes it | `map_rename_labeledActionPoly` |
| **every coefficient is a symmetric polynomial in the eigenvalues** | `isSymmetric_coeff_labeledActionPoly` |
| **hence a polynomial in the elementary symmetric functions**, i.e. in the characteristic coefficients, i.e. in the shell coordinates | `exists_esymmAlgHom_coeff_labeledActionPoly` |
| **every labelled action value is a root** | `eval_map_labeledActionPoly`, `eval_labeledAction` |

This is exactly the elimination the card asks for: the spectral action `φ_k` is not a rational
function of `θ`, but it is a root of a polynomial whose coefficients *are* polynomials in `θ`, and
the passage from one to the other costs only the symmetrisation over labellings -- the same device
that turns the parent card's `(13)` into the polynomial `(14)`.

What `(18b)` still needs on top of this is the differentiated form: implicit differentiation of the
root relation turns `∇_S φ_k = 0` into the vanishing of a polynomial expression in `(θ, y)` at
`y = φ_k(θ)`, and symmetrising that expression over the roots again gives a polynomial in `θ` alone,
whose sublevel sets are then controlled by the corpus's `exists_toSphere_sublevel_le`.

## Lean progress -- the elimination chain for `(18b)`, second and third links

Three further modules -- umbrella-wired, axiom-clean -- carry the elimination from the symmetrised
action polynomial to the sublevel bound.  Together with the first link they reduce `(18b)` to a
single differential identity.

`formal/GaloisForLFunctions/HTGeometry/ActionValueProduct.lean` generalises the symmetrisation from
the linear factor `Y − action` to an arbitrary one-variable polynomial over the coordinate ring --
which is what the *differentiated* relation produces.

| Card item | Declaration |
|---|---|
| an equivariant family of polynomials has a symmetric product | `isSymmetric_prod_of_equivariant` |
| the value of a one-variable polynomial at one labelled action, and its relabelling law | `actionValue`, `rename_actionValue` |
| the product of the values at all labellings | `actionValueProduct` |
| **it is symmetric**, hence a polynomial in the elementary symmetric functions | `isSymmetric_actionValueProduct`, `exists_esymmAlgHom_actionValueProduct` |
| **its evaluation at a spectrum** | `eval₂_actionValueProduct` |
| **the vanishing criterion**: vanishing at one labelled action value kills the product | `eval₂_actionValueProduct_eq_zero` |

`formal/GaloisForLFunctions/HTGeometry/SymmetricEsymmRepresentation.lean` puts the fundamental
theorem of symmetric polynomials into the form the tail argument needs -- a substitution, so that
evaluation at a spectrum is evaluation at the elementary symmetric functions of that spectrum.

| Card item | Declaration |
|---|---|
| **the fundamental theorem as a substitution** | `exists_bind₁_esymm_of_isSymmetric` |
| the value of a substituted polynomial at a spectrum | `eval₂_of_bind₁_esymm` |
| **a symmetric polynomial evaluates to a fixed polynomial in the elementary symmetric functions of the spectrum** | `exists_eval₂_esymm_repr_of_isSymmetric` |
| the same for the symmetrised action-value product | `exists_eval₂_esymm_repr_actionValueProduct` |

`formal/GaloisForLFunctions/HTGeometry/SublevelTransfer.lean` is the final link.

| Card item | Declaration |
|---|---|
| **the transferred power-law bound**: a nonnegative observable dominating a nonzero homogeneous polynomial inherits its shell sublevel bound | `exists_toSphere_sublevel_le_of_dominated` |
| the same simultaneously for a finite family -- the shape of `(18c)` | `exists_toSphere_sublevel_le_of_dominated_finite` |

So the chain now reads: the labelled action is a root of a polynomial whose coefficients are
symmetric (`labeledActionPoly`); any polynomial expression in `(θ, y)` symmetrised over labellings
is again symmetric (`actionValueProduct`); a symmetric polynomial is a polynomial in the elementary
symmetric functions, hence in the characteristic coefficients, hence in the shell coordinates
(`exists_eval₂_esymm_repr_of_isSymmetric`); and a homogeneous nonzero such polynomial dominated by
`h_k` gives the power law (`exists_toSphere_sublevel_le_of_dominated`).

The one remaining link is the differential identity itself: implicit differentiation of
`R(θ, φ_k(θ)) = 0` together with Euler's relation `θ · ∇φ_k = φ_k`, which turns `∇_S φ_k = 0` into
the vanishing at `y = φ_k(θ)` of the explicit polynomial

```text
  Q(θ, y) = ∑_i ( ∂_i R(θ,y) + y θ_i ∂_y R(θ,y) )²,
```

whose symmetrisation is then exactly the `Q` that `actionValueProduct` consumes.

## Lean progress -- the differential half of the elimination

`formal/GaloisForLFunctions/HTGeometry/PolynomialRelationImplicitDerivative.lean` (new,
umbrella-wired, axiom-clean) supplies the last analytic ingredient of the `(18b)` route: the
derivative of a quantity that is not rational in its parameters but satisfies a polynomial relation
with differentiable coefficients.

| Card item | Declaration |
|---|---|
| the derivative of a polynomial expression whose coefficients and unknown both move | `hasDerivAt_polyCurve` |
| **the implicit relation**: along a curve on which the polynomial relation holds, `∂_θ R + ∂_y R · φ' = 0` | `polyCurve_relation` |
| **the solved form**, wherever `∂_y R ≠ 0` | `deriv_eq_of_polyCurve` |
| **Euler's relation along the radial curve**: a degree-one positively homogeneous function has radial derivative equal to its own value | `hasDerivAt_homogeneous_scaling` |

Composing the two: on the shell, `∇_S φ_k = 0` means `∂_v φ_k = φ_k · ⟨θ, v⟩` for every direction
`v` (the radial part being fixed by Euler), so `polyCurve_relation` turns criticality into

```text
  ∂_v R(θ, φ_k(θ)) + ∂_y R(θ, φ_k(θ)) · φ_k(θ) · ⟨θ, v⟩ = 0,
```

an identity between polynomial expressions in `(θ, φ_k(θ))`.  Feeding the square-sum of those
expressions to `actionValueProduct` as the one-variable polynomial `Q`, and reading the result
through `exists_eval₂_esymm_repr_of_isSymmetric`, produces the polynomial in `θ` alone whose
sublevel sets `exists_toSphere_sublevel_le_of_dominated` converts into `(18b)`.

What is left is the bookkeeping of that composition for the concrete shell family: identifying the
coefficients of `R` as the characteristic coefficients of `H(θ)`, checking `∂_y R ≠ 0` off the
discriminant locus, and checking that the assembled polynomial is homogeneous, nonzero, and
dominated by `h_k` on the compact shell.

## Lean progress -- symmetric spectral functions are shell polynomials

The elimination chain needed one algebraic link it did not yet have: passing from a symmetric
function *of the spectrum* to a polynomial *in the shell coordinates*.  Three new modules --
umbrella-wired, axiom-clean -- close it.

`formal/GaloisForLFunctions/HTGeometry/EsymmAdjoinPsum.lean`:

| Card item | Declaration |
|---|---|
| **Newton inversion**: over a `ℚ`-algebra every elementary symmetric polynomial lies in the subalgebra generated by the power sums | `esymm_mem_adjoin_psum` |

`formal/GaloisForLFunctions/HTGeometry/SymmetricTraceRepresentation.lean`:

| Card item | Declaration |
|---|---|
| the adjoined subalgebra is exactly the range of the substitution | `aeval_mem_adjoin_range`, `adjoin_range_le_range_aeval` |
| **a symmetric polynomial is a polynomial in the power sums** | `isSymmetric_mem_adjoin_psum`, `exists_aeval_psum_repr_of_isSymmetric` |
| **a symmetric function of a Hermitian spectrum is a polynomial in the traces of its powers**, with one polynomial for every matrix | `exists_trace_repr_of_isSymmetric` |

`formal/GaloisForLFunctions/HTGeometry/ShellSymmetricPolynomial.lean`:

| Card item | Declaration |
|---|---|
| **the shell polynomial of a symmetric spectral function**: for a Hermitian interaction family, a symmetric function of the spectrum of `H(θ)` equals a fixed polynomial evaluated at `θ` | `exists_shellPoly_of_isSymmetric` |

The route deliberately goes through the *power sums* rather than the characteristic coefficients:
power sums of the spectrum are traces of matrix powers (`trace_pow_eq_sum_eigenvalues_pow`), and
those are polynomial in the coordinates because the Hamiltonian is linear in them
(`mapMatrix_spectralGenericMatrix`, `trace_mapMatrix`).  Newton's identities, solved for the
elementary symmetric polynomials over a `ℚ`-algebra, bridge the two.

With this, the `(18b)` chain is complete except for the concrete instantiation: the symmetrised
gradient expression built by `actionValueProduct` out of the implicit-derivative identity is a
symmetric polynomial in the spectrum, so `exists_shellPoly_of_isSymmetric` turns it into a
polynomial in `θ`, and `exists_toSphere_sublevel_le_of_dominated` turns that into the power law.
What remains is checking, for that particular polynomial, homogeneity, non-vanishing, and the
domination `|G| ≤ C · h_k` on the compact shell.

## Lean progress -- the transversality tail from a shell polynomial

Two new modules -- umbrella-wired, axiom-clean -- remove the last two side conditions of the
`(18b)` route, so that the tail follows from properties of the constructed polynomial alone.

`formal/GaloisForLFunctions/HTGeometry/HomogeneousEvalCriterion.lean`:

| Card item | Declaration |
|---|---|
| **homogeneity is readable off the evaluation**: a polynomial whose value scales like a power is homogeneous of that degree | `isHomogeneous_of_eval_smul` |
| **a continuous cofactor is a constant** on a compact space, so a continuous multiple of a nonnegative observable is dominated by a constant multiple of it | `exists_bound_of_continuous_cofactor` |

The first removes the need to track degrees through the symmetrisation: the assembled polynomial
inherits homogeneity from the degree-one homogeneity of the spectrum, and the criterion converts
that functional statement into the `IsHomogeneous` hypothesis the sublevel bound wants.  The proof
compares the scaling of the homogeneous components as a polynomial identity in the scaling
parameter, which kills every component but one.  The corpus's own `eval_smul_of_isHomogeneous`
supplies the forward direction, and is reused rather than reproved.

`formal/GaloisForLFunctions/HTGeometry/ShellSublevelCapstone.lean`:

| Card item | Declaration |
|---|---|
| **the transversality tail**: a nonnegative observable which is a continuous multiple of a nonzero polynomial with power scaling has the power-law shell sublevel bound | `exists_toSphere_sublevel_le_of_shellPoly` |

This is `(18b)` with the construction abstracted into three checkable properties of the assembled
polynomial `G`: it is nonzero, its evaluation scales as `G(tθ) = t^d G(θ)`, and it factors as
`G(θ) = g(θ) · h_k(θ)` with `g` continuous on the shell.  Nothing analytic remains -- the
Łojasiewicz inequality the card offered as the alternative route is not used anywhere.

## Lean progress -- the criticality criterion in the coordinates

`formal/GaloisForLFunctions/HTGeometry/ShellCriticalityCriterion.lean` (new, umbrella-wired,
axiom-clean) instantiates the implicit-derivative relation on the coordinate lines of the shell,
which is the form the elimination consumes.

| Card item | Declaration |
|---|---|
| the coordinate line through a point and its derivative | `hasDerivAt_coordinate_line` |
| **the criticality criterion**: if a quantity satisfies a polynomial relation with polynomial coefficients and its derivative along the `i`-th coordinate line is the tangential-criticality value `φ(θ)·θ_i`, then `∑_n ∂_i c_n(θ) φ(θ)^n + (∑_n n c_n(θ) φ(θ)^{n−1}) φ(θ) θ_i = 0` | `shell_criticality_relation` |

The chain rule for a multivariate polynomial along a curve was already in the corpus
(`hasDerivAt_mvPolynomial_eval_curve_real`, `HTGeometry/PolynomialZeroSetDimension`), so this
module only combines it with `polyCurve_relation` and the coordinate-line derivative; nothing was
reproved.

This is the polynomial expression `Q(θ, y)` referred to in the elimination plan, now formal: the
left-hand side is a polynomial in the coordinates and in the action value, and it vanishes exactly
at the critical points.  Feeding its square-sum over the coordinate directions to
`actionValueProduct`, reading the result through `exists_shellPoly_of_isSymmetric`, and applying
`exists_toSphere_sublevel_le_of_shellPoly` is `(18b)`.

## Lean progress -- the real shell polynomial

The shell polynomial produced by the trace representation lives over `ℂ`, because the traces of
matrix powers do; the sublevel machinery needs a *real* polynomial.  A complex polynomial with real
values at every real point has real coefficients, and that is now formal.

`formal/GaloisForLFunctions/HTGeometry/RealValuedComplexPolynomial.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| the coefficientwise imaginary part, and the real/imaginary split of a complex polynomial | `imagCoeffPart`, `coeff_imagCoeffPart`, `split_realCoeffPart` |
| the value of the split at a real point | `eval_split` |
| **real values force conjugation-invariant coefficients** | `map_conj_of_real_valued` |
| **hence a real polynomial representing the same function** | `exists_realPoly_of_real_valued` |
| **the real shell polynomial of a symmetric spectral function** | `exists_realShellPoly_of_isSymmetric` |

The split is coefficientwise, so no induction over monomials is needed: evaluating it at a real
point separates the real and imaginary parts, reality kills the imaginary polynomial pointwise, and
`MvPolynomial.funext` over `ℝ` makes it the zero polynomial.  The corpus's `realCoeffPart` and
`map_realCoeffPart` are reused; only the imaginary half was missing.

With `exists_realShellPoly_of_isSymmetric`, every symmetric real function of the shell spectrum is
now a real polynomial in the shell coordinates, which is the exact input of
`exists_toSphere_sublevel_le_of_shellPoly`.

## Lean progress -- the polynomial relation of the shell spectral action

`formal/GaloisForLFunctions/HTGeometry/ShellActionRelation.lean` (new, umbrella-wired,
axiom-clean) instantiates the elimination at the actual shell family, producing the hypothesis the
criticality criterion consumes.

| Card item | Declaration |
|---|---|
| the spectral action at one labelling of the shell spectrum | `shellSpectralAction` |
| the coefficients of the symmetrised labelled action polynomial, as real shell polynomials | `exists_realShellCoeff_labeledActionPoly` |
| **the polynomial relation**: for every labelling and every coordinate vector, `∑_n c_n(θ) φ_k(θ)^n = 0` with each `c_n` a real polynomial in the coordinates | `exists_shellRelation_labeledAction` |
| **the criticality criterion for the spectral action**: one polynomial family, common to every labelling and every coordinate vector, whose vanishing expresses the vanishing of the tangential gradient | `exists_shell_criticality_polynomial` |

The relation comes from `eval_map_labeledActionPoly` -- the action value at a labelling is a root of
the symmetrised polynomial -- read through `exists_realShellPoly_of_isSymmetric` for the
coefficients, with `Polynomial.eval_eq_sum_range'` supplying a single uniform degree bound.

So the card's `(18b)` route is now instantiated end to end except for the final step: form the
square-sum over coordinate directions of the criticality expression, symmetrise it over labellings
with `actionValueProduct`, read it as a real shell polynomial, and check that this polynomial is
nonzero, scales with a fixed degree, and factors through `h_k` -- at which point
`exists_toSphere_sublevel_le_of_shellPoly` gives the power law.

## Lean progress -- the criticality square sum

`formal/GaloisForLFunctions/HTGeometry/CriticalitySquareSum.lean` (new, umbrella-wired,
axiom-clean) packages the criticality expressions of all coordinate directions into a single
polynomial in the auxiliary variable over the coordinate ring -- the object the symmetrisation over
labellings consumes.

| Card item | Declaration |
|---|---|
| the criticality expression in one direction, as a polynomial in the auxiliary variable | `criticalityPoly` |
| the sum of their squares over all directions | `criticalitySquareSum` |
| their evaluations at a coordinate vector and an action value | `eval_map_criticalityPoly`, `eval_map_criticalitySquareSum` |
| **the square sum vanishes at a critical point** | `eval_map_criticalitySquareSum_eq_zero_of_forall` |

Composed with `exists_shell_criticality_polynomial`, this says: at any coordinate vector where the
tangential gradient of the spectral action vanishes, the square sum evaluates to zero at the action
value.  That is exactly the vanishing hypothesis of `eval₂_actionValueProduct_eq_zero`, so
symmetrising the square sum over labellings produces a symmetric spectral function vanishing at
every critical point -- and `exists_realShellPoly_of_isSymmetric` turns it into the real shell
polynomial that `exists_toSphere_sublevel_le_of_shellPoly` consumes.

## Lean progress -- symmetric spectral functions over the coordinate ring

The symmetrised criticality expression is symmetric in the eigenvalue variables but its
coefficients live in the coordinate ring, not in the reals, so the earlier shell-polynomial theorem
does not apply directly.  Newton inversion holds over any `ℚ`-algebra, and the coordinate ring is
one, so the same route works.

`formal/GaloisForLFunctions/HTGeometry/ShellSymmetricOverCoordinates.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| **the shell polynomial of a symmetric spectral function with coordinate-ring coefficients** | `exists_shellPoly_of_isSymmetric_over` |

The proof substitutes the power sums by the real trace polynomials of the family -- themselves
produced by `exists_realShellPoly_of_isSymmetric` applied to `MvPolynomial.psum` -- and matches the
two sides through `MvPolynomial.eval₂_comp_left`, so no algebra-instance juggling is needed.

This is the missing type-level link: `actionValueProduct` of the criticality square sum lives
exactly in `MvPolynomial (Fin D) (MvPolynomial (Fin N) ℝ)`, is symmetric by
`isSymmetric_actionValueProduct`, and therefore is now a single real polynomial in the shell
coordinates.

## Lean progress -- the critical-locus shell polynomial

`formal/GaloisForLFunctions/HTGeometry/CriticalLocusShellPolynomial.lean` (new, umbrella-wired,
axiom-clean) assembles the whole elimination into the object the transversality tail needs.

| Card item | Declaration |
|---|---|
| **a real shell polynomial vanishing on the critical locus**, together with the polynomial relation satisfied by every labelled spectral action | `exists_criticalLocusShellPoly` |

The construction is exactly the card's "eliminate the eigenvalues" route, now complete:

1. the labelled spectral actions are the roots of a polynomial whose coefficients are real shell
   polynomials (`exists_shellRelation_labeledAction`);
2. differentiating that relation along each coordinate line, with Euler's relation fixing the radial
   part, turns tangential criticality into the vanishing of an explicit polynomial expression in the
   coordinates and the action value (`shell_criticality_relation`);
3. squaring and summing over the directions packages those expressions into one polynomial in the
   auxiliary variable (`criticalitySquareSum`);
4. multiplying its values over all labellings gives a symmetric spectral function with
   coordinate-ring coefficients (`actionValueProduct`, `isSymmetric_actionValueProduct`);
5. Newton inversion over the coordinate ring, with the power sums replaced by the real trace
   polynomials of the family, makes it a single real polynomial `G` in the shell coordinates
   (`exists_shellPoly_of_isSymmetric_over`);
6. and at a critical point the factor belonging to that labelling vanishes, so `G` does
   (`eval_map_criticalitySquareSum_eq_zero_of_forall`).

`(18b)` is now: `G ≠ 0`, `G` scales with a fixed degree, and `G` factors as a continuous function
times `h_k` -- at which point `exists_toSphere_sublevel_le_of_shellPoly` gives the power law.  The
first two are properties of the explicit polynomial above; the third is where the eigenbranch
differentiability of the spectral action enters, the same input the parent card's Theorem A needs.

## Lean progress -- symmetric functions of the spectrum scale

The homogeneity of the critical-locus polynomial rests on the spectrum scaling with the
Hamiltonian.  The canonical eigenvalue *list* of `t·H` need not be `t` times the list of `H` --
the ordering can change -- but a symmetric function does not see the ordering, and it is a
polynomial in the power sums, which scale exactly.

`formal/GaloisForLFunctions/HTGeometry/SymmetricEigenvalueScaling.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| the power sums of the spectrum scale, from `tr((tH)^n) = t^n tr(H^n)` | `sum_pow_eigenvalues_smul` |
| **every symmetric function of a Hermitian spectrum scales with the matrix** | `eval_symmetric_eigenvalues_smul` |

This is the ordering-free replacement for the naive "eigenvalues scale" statement, and it is what
feeds `isHomogeneous_of_eval_smul` when the critical-locus polynomial's degree is read off its
scaling.

One clarification the formalisation forced: the criticality expression built by
`shell_criticality_relation` is *not* homogeneous as written, because it uses the unit-sphere form
`∂_i φ = φ · θ_i` of the tangential condition.  The scale-correct form carries `|θ|^{-2}`, so the
homogeneous version multiplies the gradient sum by `∑_a θ_a²` -- which is `1` on the shell and
therefore changes nothing there, while making the total degrees of the two terms agree.

## Lean progress -- the homogeneous critical-locus polynomial

`formal/GaloisForLFunctions/HTGeometry/HomogenisedCriticality.lean` (new, umbrella-wired,
axiom-clean) carries out the degree correction recorded above and rebuilds the critical-locus
polynomial from the corrected expression.

| Card item | Declaration |
|---|---|
| the norm-square polynomial of the coordinates, and its value | `normSqPoly`, `eval_normSqPoly` |
| the homogeneous forms of the criticality expression and of its square sum | `criticalityPolyHom`, `criticalitySquareSumHom` |
| their evaluations | `eval_map_criticalityPolyHom`, `eval_map_criticalitySquareSumHom` |
| **the homogeneous square sum still vanishes at a critical point of the shell** | `eval_map_criticalitySquareSumHom_eq_zero_of_forall` |
| **the critical-locus shell polynomial, homogeneous form**, with the polynomial relation, the product formula for its values, and the vanishing on the critical locus | `exists_criticalLocusShellPolyHom` |

The correction is exactly one factor of `∑_a θ_a²` on the gradient term: identically one on the
shell, so the vanishing statement is untouched, while the two terms of the criticality expression
now carry the same total degree once the auxiliary variable is given degree one.  The product
formula is recorded because it is what the scaling argument consumes: the value of `G` at `θ` is
the product over labellings of the square-sum values, and each factor scales through
`eval_symmetric_eigenvalues_smul`.

## Lean progress -- degree bookkeeping of the symmetrised action polynomial

`formal/GaloisForLFunctions/HTGeometry/ProdXSubCCoeffHomogeneous.lean` (new, umbrella-wired,
axiom-clean) supplies the degree bookkeeping the scaling argument needs.

| Card item | Declaration |
|---|---|
| the product of linear factors is monic of the expected degree | `natDegree_prod_X_sub_C` |
| **the coefficients of a product of linear factors with degree-one roots are homogeneous of the complementary degree** | `isHomogeneous_coeff_prod_X_sub_C` |

Applied to `labeledActionPoly`, whose roots are the labelled spectral actions -- each homogeneous of
degree one in the eigenvalue variables -- this says the coefficient of `Y^n` is homogeneous of
degree `D! − n`.  Combined with `eval_symmetric_eigenvalues_smul`, that is the scaling of the shell
coefficients `c_n`, and hence, through the product formula of
`exists_criticalLocusShellPolyHom`, the fixed-degree scaling of the critical-locus polynomial.

The proof is the induction over the factor set, with the two boundary cases -- the constant
coefficient, and coefficients beyond the degree -- handled by `mul_coeff_zero` and
`coeff_eq_zero_of_natDegree_lt` respectively.

## Lean progress -- the shell coefficients scale

`formal/GaloisForLFunctions/HTGeometry/ShellCoeffScaling.lean` (new, umbrella-wired, axiom-clean)
combines the degree bookkeeping with the spectral scaling to give the scaling law of the shell
coefficients of the action polynomial.

| Card item | Declaration |
|---|---|
| the labelled action is homogeneous of degree one in the eigenvalue variables | `isHomogeneous_labeledAction` |
| hence the coefficient of `Y^n` is homogeneous of the complementary degree | `isHomogeneous_coeff_labeledActionPoly` |
| the Hamiltonian family is linear in the coordinates | `spectralEnsembleMatrix_smul` |
| so the canonical eigenvalue list of the scaled family is that of the scaled Hamiltonian | `eigenvalues_spectralEnsembleMatrix_smul` |
| **the shell coefficients scale**: `c_n(tθ) = t^{|S_D| − n} c_n(θ)` | `eval_shellCoeff_smul` |

The eigenvalue step goes through mathlib's `IsHermitian.eigenvalues_eq_eigenvalues_iff`, which
compares characteristic polynomials rather than matrices, so the matrix identity is transported by
`congrArg Matrix.charpoly`.  The symmetric-scaling lemma then removes the ordering ambiguity and
`eval_smul_of_isHomogeneous` supplies the power.

This is the last scaling ingredient: with it, every coefficient appearing in `criticalityPolyHom`
carries a known homogeneity degree, so the product formula of `exists_criticalLocusShellPolyHom`
exhibits the critical-locus polynomial as scaling by a fixed power -- the hypothesis of
`isHomogeneous_of_eval_smul`.

## Lean progress -- the total grading of the spectral construction

The scaling of the critical-locus polynomial is not a statement about the coordinates alone: the
symmetrised construction lives in the polynomials in the *spectral* variables whose coefficients are
polynomials in the *coordinates*, and both scale simultaneously.  The relevant notion is the total
grading.

`formal/GaloisForLFunctions/HTGeometry/Bihomogeneous.lean` (new, umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| the total grading: a spectral monomial of degree `a` carries a coefficient of coordinate degree `d − a`, and vanishes beyond `d` | `IsBihomogeneous` |
| **a bihomogeneous object scales by its total degree** under simultaneous scaling of the coordinates and of the spectrum | `eval₂_smul_of_isBihomogeneous` |

The proof is monomialwise: the coefficient contributes `t^{d−a}` by `eval_smul_of_isHomogeneous`
and the spectral monomial contributes `t^a`, and the vanishing clause is exactly what makes the
exponents add to `d` on the support.

This is the grading in which the whole `(18b)` construction is homogeneous: the shell coefficients
`c_n` have coordinate degree `|S_D| − n` (`eval_shellCoeff_smul`), the auxiliary variable stands for
a spectral quantity of degree one, and `criticalityPolyHom` was corrected precisely so that its two
terms have the same total degree.  What remains is to record that grading for the symmetrised
product and read the scaling of `G` off `eval₂_smul_of_isBihomogeneous`.

## Lean progress -- the joint grading replaces the ad hoc one

The total grading of the previous entry is nothing but ordinary homogeneity on the *joint* variable
set: polynomials in the spectral variables with coordinate-ring coefficients are polynomials in the
disjoint union of the two variable sets.  Working there makes every closure property -- sums,
products, constants, variables -- immediate from mathlib's `IsHomogeneous` API, instead of having
to be re-proved for a bespoke bigraded predicate.

`formal/GaloisForLFunctions/HTGeometry/JointGradingBridge.lean` (new, umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| the homogeneous scaling identity over an arbitrary variable set | `eval_smul_of_isHomogeneous_general` |
| **the iterated evaluation is the joint evaluation** | `eval_sumAlgEquiv` |
| **a jointly homogeneous object scales by its degree** under simultaneous scaling of the coordinates and of the spectrum | `eval₂_smul_of_joint_isHomogeneous` |

The bridge is the algebra equivalence `MvPolynomial (S₁ ⊕ S₂) R ≃ₐ MvPolynomial S₁ (MvPolynomial S₂ R)`
together with a three-case induction identifying the two evaluations.  The corpus's
`eval_smul_of_isHomogeneous` is stated for `Fin m`; the general-index version is proved here rather
than transporting along a cardinality equivalence.

This supersedes the bespoke `IsBihomogeneous` predicate: the construction should be built on the
joint ring, where the criticality polynomial's homogeneity is assembled from `IsHomogeneous.add`,
`IsHomogeneous.mul`, and the degrees already established for the shell coefficients.

## Lean progress -- the graded pieces on the joint ring

`formal/GaloisForLFunctions/HTGeometry/JointSpectralAction.lean` (new, umbrella-wired,
axiom-clean) records the graded pieces the criticality construction is assembled from.

| Card item | Declaration |
|---|---|
| **the shell coefficients of the action polynomial are homogeneous** of the complementary degree | `isHomogeneous_shellCoeff` |
| coordinate polynomials embed homogeneously into the joint ring | `isHomogeneous_rename_inr` |
| the spectral action of one labelling is a linear form on the joint ring | `jointAction`, `isHomogeneous_jointAction` |
| its value at a spectrum and a coordinate vector | `eval_jointAction` |

The first is a one-line consequence of two earlier results and is worth isolating: the shell
coefficients were produced by an existential, so their homogeneity was not available structurally;
`eval_shellCoeff_smul` gives their scaling at every real factor, and `isHomogeneous_of_eval_smul`
converts that into genuine homogeneity of the polynomial.  This is the point at which the value
level and the polynomial level meet.

With these, the criticality expression can be written directly on the joint ring -- the auxiliary
variable replaced by `jointAction`, the coefficients renamed in -- and its homogeneity assembled
from `IsHomogeneous.add` and `IsHomogeneous.mul` alone.

## Lean progress -- the criticality expression is homogeneous on the joint ring

`formal/GaloisForLFunctions/HTGeometry/JointCriticalityHomogeneous.lean` (new, umbrella-wired,
axiom-clean) writes the corrected criticality expression on the joint ring and computes its degree.

| Card item | Declaration |
|---|---|
| a degree-zero homogeneous polynomial is constant, so its partial derivatives vanish | `eq_C_of_isHomogeneous_zero`, `pderiv_eq_zero_of_isHomogeneous_zero` |
| the norm-square polynomial has degree two | `isHomogeneous_normSqPoly` |
| the criticality expression on the joint ring | `jointCriticality` |
| **it is homogeneous of degree `M + 1`** | `isHomogeneous_jointCriticality` |

The two terms carry degrees `(M − n − 1) + 2 + n` and `(M − n) + (n − 1) + 2`, both `M + 1`, and the
computation has exactly two boundary cases, each of which makes its term vanish rather than break
the grading:

* at `n = M` the coefficient `c_M` is homogeneous of degree zero, hence constant, so its partial
  derivative is zero -- this is why `eq_C_of_isHomogeneous_zero` is needed;
* at `n = 0` the scalar factor `n` is zero.

Both are genuine features of the construction, not artefacts: the top coefficient of a monic
polynomial is a constant, and the derivative of the constant term contributes nothing.

With the degree in hand, `eval₂_smul_of_joint_isHomogeneous` gives the scaling of the symmetrised
product, which is the `hGscale` hypothesis of `exists_toSphere_sublevel_le_of_shellPoly`.

## Lean progress -- the symmetrised criticality product is homogeneous

`formal/GaloisForLFunctions/HTGeometry/JointCriticalProduct.lean` (new, umbrella-wired,
axiom-clean) completes the graded construction.

| Card item | Declaration |
|---|---|
| the sum over the coordinate directions of the squared criticality expressions, on the joint ring | `jointCriticalitySquareSum`, `isHomogeneous_jointCriticalitySquareSum` |
| the product over all labellings of the spectrum | `jointCriticalProduct` |
| **the symmetrised criticality product is homogeneous**, of degree `\|S_D\| · 2(M+1)` | `isHomogeneous_jointCriticalProduct` |
| **its evaluation scales by that power** under simultaneous scaling of the coordinates and the spectrum | `eval_jointCriticalProduct_smul` |

Because the construction now lives on the joint variable set, the homogeneity of the product is
`IsHomogeneous.prod` applied to `IsHomogeneous.pow` applied to
`isHomogeneous_jointCriticality` -- no bespoke bigraded reasoning at all, which is the payoff of
the change of setting recorded two entries above.

The scaling statement is literally the `hGscale` hypothesis of
`exists_toSphere_sublevel_le_of_shellPoly`, once the joint product is identified with the shell
polynomial `G` of `exists_criticalLocusShellPolyHom`.  That identification -- the two constructions
agree because both are the symmetrisation of the same criticality expression -- is what remains,
together with `G ≠ 0` and the factorisation through `h_k`.

## Lean progress -- the criticality product is invariant under relabelling

`formal/GaloisForLFunctions/HTGeometry/JointCriticalSymmetry.lean` (new, umbrella-wired,
axiom-clean) supplies the symmetry that lets the joint construction descend to the shell
coordinates.

| Card item | Declaration |
|---|---|
| relabelling fixes the coordinate variables | `rename_sumMap_rename_inr` |
| and translates the labelling of the spectral action | `rename_sumMap_jointAction` |
| so the criticality expression translates | `rename_sumMap_jointCriticality` |
| and its square sum too | `rename_sumMap_jointCriticalitySquareSum` |
| **the product over all labellings is invariant** | `rename_sumMap_jointCriticalProduct` |

The relabelling acts as `Sum.map τ id`: it permutes the spectral variables and fixes the
coordinates, so the shell coefficients -- which are renamed in along `Sum.inr` -- are untouched,
while the spectral actions are permuted among themselves.  The product over `S_D` is then invariant
by the same group-translation reindexing used for `labeledActionPoly`.

Together with `isHomogeneous_jointCriticalProduct` and `eval_jointCriticalProduct_smul` this gives
the joint object all three properties needed downstream: it is symmetric in the spectrum, so it
descends to a real shell polynomial; it is homogeneous, so its evaluation scales by a fixed power;
and it vanishes on the critical locus.  What is left is to run the descent and to establish that the
resulting polynomial is nonzero and factors through `h_k`.

## Lean progress -- the descent to the shell coordinates

`formal/GaloisForLFunctions/HTGeometry/JointDescent.lean` (new, umbrella-wired, axiom-clean) runs
the descent: from the joint ring back to a single real polynomial in the shell coordinates.

| Card item | Declaration |
|---|---|
| the equivalence intertwines relabelling of the spectral variables with relabelling of the outer ones | `rename_sumAlgEquiv` |
| hence the descended criticality product is symmetric | `isSymmetric_sumAlgEquiv_jointCriticalProduct` |
| **the shell polynomial of the criticality product**: its value at a coordinate vector is the joint product evaluated there and at the spectrum that vector determines | `exists_shellPoly_jointCriticalProduct` |

So the construction is now available in both pictures at once: as a homogeneous polynomial on the
joint variable set, where its degree and its scaling are visible, and as a real polynomial in the
shell coordinates, where the sublevel bound applies -- with the two linked by an explicit identity
of values.

What remains for `(18b)` is the transport of the scaling across that identity -- for which the
symmetric-scaling lemma must be stated with a general coefficient homomorphism rather than over the
reals -- together with `G ≠ 0` and the factorisation through `h_k`.

## Lean progress -- the shell polynomial scales

`formal/GaloisForLFunctions/HTGeometry/ShellPolyScaling.lean` (new, umbrella-wired, axiom-clean)
transports the joint scaling law across the descent.

| Card item | Declaration |
|---|---|
| **the spectral scaling with a general coefficient homomorphism**: for a symmetric polynomial over any `ℚ`-algebra, the value at the spectrum of a scaled Hermitian matrix is the value at the scaled spectrum | `eval₂_symmetric_eigenvalues_smul` |
| **the shell polynomial of the criticality product scales by a fixed power** | `eval_shellPoly_jointCriticalProduct_smul` |

The general-coefficient form is needed because the descent evaluates the symmetric polynomial with
coefficients in the coordinate ring, not in the reals; the proof is the same power-sum argument,
with `eval₂` in place of `eval`.  The transport then reads:

```text
  G(tθ) = ⟨joint product⟩(spec(tθ), tθ)          (descent identity)
        = ⟨joint product⟩(t · spec(θ), tθ)        (symmetric spectral scaling)
        = t^d · ⟨joint product⟩(spec(θ), θ)       (joint homogeneity)
        = t^d · G(θ)                              (descent identity).
```

That is the second of the three properties `(18b)` needs, and it is the one that required the whole
graded apparatus: `G` is produced by an existential, so its scaling could only be established
through the explicit joint construction it descends from.  What is left is `G ≠ 0` and the
factorisation `G = g · h_k`.

### Lean progress — witness reduction for the shell criticality polynomial

`HTGeometry/ShellPolyNonvanishing.lean` (umbrella-wired, `lake build` green, axioms =
`propext`/`Classical.choice`/`Quot.sound`) closes the nonvanishing half of the `(18b)` chain:

* `eval_jointCriticalitySquareSum_eq` — the evaluation of the sum-of-squares aggregate is the sum of
  the squares of the evaluations of the individual joint-criticality components.
* `eval_jointCriticalitySquareSum_ne_zero_of_exists` — one component nonzero at a point forces the
  aggregate nonzero there (sum of nonnegative reals vanishes iff each term does).
* `eval_shellPoly_ne_zero_of_forall` — if for *every* labelling permutation some component survives
  at the witness point, the whole labelling product is nonzero there.
* `shellPoly_ne_zero_of_eval_ne_zero` — a single evaluation witness upgrades to `G ≠ 0` as a
  polynomial, which is the hypothesis the sublevel-measure capstone consumes.

This removes the last "generic transversality" appeal from the `(18b)` route: nonvanishing of the
criticality polynomial is now a checkable pointwise statement rather than an assumed genericity.

### Lean progress — `(18b)` closed: the transversality power law

Four new modules (umbrella-wired, `lake build` green, axioms = `propext`/`Classical.choice`/
`Quot.sound`) complete the elimination route and prove `(18b)` in the form the card states.

`HTGeometry/CriticalityTangentialFactorisation.lean`

| Card item | Declaration |
|---|---|
| the leading factor of the defining relation and the criticality value | `criticalityLeading`, `criticalityValue` |
| `h_k = ‖∇_S φ_k‖²` as the deviation of the directional derivatives from the radial one | `tangentialGradNormSq`, `tangentialGradNormSq_nonneg`, `tangentialGradNormSq_eq_zero_iff` |
| on the shell, `‖∇_S φ‖² = ‖∇φ‖² − φ²` | `tangentialGradNormSq_eq_sub_sq_of_euler` |
| **the criticality expression is the leading factor times the tangential deviation** | `criticalityValue_eq_leading_mul_tangential` |
| **hence the direction square sum is `(∂_yQ)² · ‖∇_S φ‖²`** | `criticalitySquareSum_eq_leading_sq_mul` |

This is the factorisation `G = g · h_k` the card asked for, and it is an *identity*, not a
genericity statement: implicit differentiation of the defining relation gives
`∑_n ∂_i c_n φ^n = −(∑_n n c_n φ^{n−1}) ∂_iφ`, so the criticality expression equals
`(∑_n n c_n φ^{n−1}) · (φθ_i − ∂_iφ)`, and summing the squares over `i` factors exactly.

`HTGeometry/JointCriticalityEvaluation.lean`

| Card item | Declaration |
|---|---|
| the leading factor as a polynomial on the joint ring | `jointLeading`, `eval_jointLeading` |
| the evaluation of the homogenised criticality expression | `eval_jointCriticality` |
| **on the unit shell the homogenising factor is one** | `eval_jointCriticality_of_unit` |

`HTGeometry/SpectralEnsembleEigenvalueBound.lean`

| Card item | Declaration |
|---|---|
| the eigenvalue energy is the real trace of the square | `sum_sq_eigenvalues_eq_trace_sq_re` |
| hence every eigenvalue is bounded by its square root | `abs_eigenvalues_le_sqrt_trace_sq_re` |
| **the uniform spectral bound on the shell** | `ensembleTraceBound`, `abs_eigenvalues_spectralEnsembleMatrix_le` |
| a polynomial is bounded on a box | `exists_bound_eval_of_abs_le` |
| **a joint polynomial is bounded on the shell** | `exists_bound_eval_joint` |

This replaces the continuity the sublevel capstone originally asked of the cofactor.  Eigenvalues
of a Hermitian matrix are *not* continuous in its entries, so no continuous-cofactor statement is
available; but `∑_i λ_i(θ)² = Re Tr H(θ)²` is a quadratic form in `θ`, bounded on the shell by the
total absolute trace mass `∑_{a,b} |Tr(P_aP_b)|` of the family, and boundedness is all the
domination step needs.

`HTGeometry/ShellCriticalityDomination.lean`

| Card item | Declaration |
|---|---|
| the criticality product with the distinguished tangential block removed | `jointCriticalCofactor` |
| **the factorisation on the unit shell**: the product is `‖∇_S φ_k‖²` times the cofactor | `eval_jointCriticalProduct_eq_tangential_mul` |
| the two shell facts used: `|θ_a| ≤ 1` and `∑_a θ_a² = 1` | `sphere_abs_coord_le_one`, `sphere_sum_sq_coord` |
| **`(18b)`**: `σ{ω : ‖∇_S φ_k(ω)‖² ≤ g} ≤ A · g^{1/(D!·2(M+1))}` | `exists_toSphere_sublevel_le_shellCriticality` |

So the power law now holds with the explicit exponent `1/(D!·2(M+1))`, where `M` is the degree of
the symmetrised labelled action polynomial.  Its hypotheses are the card's own setup: the family is
Hermitian, the action satisfies the relation `∑_n c_n(θ)φ^n = 0` with homogeneous shell
coefficients (both supplied by `exists_shellRelation_labeledAction` and `isHomogeneous_shellCoeff`),
the branch is differentiable along the coordinate lines of the shell, and one coordinate vector
exists at which no labelling of the spectrum is critical.  No Łojasiewicz inequality, no
semialgebraic stratification, and no genericity appeal is used anywhere.

With `(18a)` (`exists_toSphere_spectralDiscriminant_sublevel_le`), `(13)`
(`exists_small_transversalityTail`), Theorem C's assembly (`OnsetProbabilityAssembly`,
`GridUnionOnset`) and now `(18b)`, the transversality half of the card is Lean-complete.
