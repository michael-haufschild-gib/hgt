# Static ensembles obey a parameter--time--coverage barrier

- **ID:** `static-ensemble-coverage-time-barrier-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** THEOREM (paper) / FRONTIER NO-GO WITH POSITIVE SURVIVOR
- **Parents:** `../3-formalized/static-orbit-net-no-go-and-circuit-bellman-law.md`,
  `cubic-phase-seeded-static-local-full-scale-plateau-law.md`,
  `spectral-phase-folding-locality-addressability-law.md`
- **Status:** `[PAPER-PROVED] [LEAN PARTIAL] [SUPPORTING LAW] [HEADLINE NOVELTY REJECTED]`
- **Date:** 2026-08-10
- **Statement:** An `m`-parameter bounded static Hamiltonian ensemble cannot cover a target of
  fixed-resolution metric entropy `N` before time of order `N^(1/m)`; covering projective
  `D`-dimensional quantum state space therefore needs `exp(Omega(D/m))` time.

## Public sentence

Static quantum dynamics can generate states of near-maximal circuit complexity long before its
low-dimensional Hamiltonian ensemble can cover the full space of quantum states.  The theorem
quantifies that coverage separation, but it is a supporting law rather than a paper headline.

This theorem does **not** prove the Brown--Susskind ramp.  It proves that global Haar coverage cannot
be the missing ramp mechanism and identifies one-sided avoidance of easy circuits as the only live
metric-entropy mechanism.

## Theorem A -- abstract parameter--time--coverage law

Let `K` be contained in the closed Euclidean ball of radius `R>0` in `R^m`, let `(Y,d)` be a metric
space, and let `F:K -> Y` be `L`-Lipschitz.  Suppose `F(K)` is `epsilon`-dense in a target
`S subset Y`, where `epsilon>0`.  Then

\[
 \boxed{
 N_{2\epsilon}(S)
 \le \left(1+{2RL\over\epsilon}\right)^m .}                    \tag{1}
\]

Here `N_r(S)` is the least cardinality of an external closed `r`-ball cover.  Consequently, if
`N_{2 epsilon}(S)>=N>1`, then

\[
 \boxed{
 L\ge {\epsilon\over2R}\left(N^{1/m}-1\right).}                \tag{2}
\]

For `m=0`, the image is a singleton and the same conclusion is read without taking an `m`-th root:
no target with covering number greater than one can be densely covered.

### Proof

Assume first `L>0`.  A maximal `epsilon/L`-separated subset of `K` is an `epsilon/L`-net.  The
standard Euclidean volume comparison bounds its size by

\[
 \left(1+{2R\over \epsilon/L}\right)^m
 =\left(1+{2RL\over\epsilon}\right)^m.                           \tag{3}
\]

Its image is an `epsilon`-net of `F(K)`.  Every point of `S` is within `epsilon` of `F(K)`, so the
same image centres form a `2 epsilon`-cover of `S`.  This proves `(1)`.  If `L=0`, the image has
diameter zero; density gives a one-ball `2 epsilon`-cover, again proving `(1)`.  Taking the positive
`m`-th root of `(1)` and rearranging proves `(2)`.

No measurability, probability distribution, spectral gap, nondegeneracy, or dynamics is used.

## Theorem B -- exact projective-state exponent

Let `P(C^D)` carry pure-state trace distance

\[
 d_{\rm tr}([\psi],[\phi])=\sqrt{1-|\langle\psi,\phi\rangle|^2}
\]

and Haar probability.  For every centre and `0<=r<=1`,

\[
 \boxed{
 \mu_{\rm Haar}\bigl(B_r([\phi])\bigr)=r^{2D-2}.}               \tag{4}
\]

Hence

\[
 \boxed{
 N_r(P(C^D))\ge r^{-(2D-2)}}                                   \tag{5}
\]

for `0<r<=1`.

### Proof

By unitary invariance take `phi=e_1`.  For a Haar unit vector `psi`,
`X=|psi_1|^2` has the `Beta(1,D-1)` law.  Therefore

\[
 \Pr\{d_{\rm tr}([\psi],[e_1])\le r\}
 =\Pr\{X\ge1-r^2\}=r^{2D-2},
\]

which is `(4)`.  A cover by `q` radius-`r` balls has Haar mass at most
`q r^(2D-2)`; since it covers a probability-one space, `q>=r^(-(2D-2))`.

## Theorem C -- static-Hamiltonian coverage time

Let

\[
 H(\theta)=\sum_{a=1}^m\theta_a A_a,
 \qquad \theta\in K\subseteq\overline B_R(0),
 \qquad
 B_A:=\left(\sum_{a=1}^m\|A_a\|_{\rm op}^2\right)^{1/2},       \tag{6}
\]

where every `A_a` is self-adjoint, and fix any unit seed `chi`.  Put

\[
 F_t(\theta)=[e^{-itH(\theta)}\chi].                            \tag{7}
\]

If `F_t(K)` is `epsilon`-dense in `P(C^D)` for `0<epsilon<1/2`, then

\[
 \boxed{
 |t|B_A\ge {\epsilon\over2R}
 \left((2\epsilon)^{-(2D-2)/m}-1\right).}                      \tag{8}
\]

### Proof

Duhamel's formula and unitarity give

\[
 \|e^{-itH(\theta)}-e^{-itH(\eta)}\|_{\rm op}
 \le |t|\,\|H(\theta)-H(\eta)\|_{\rm op}.                     \tag{9}
\]

Cauchy--Schwarz in coefficient space gives

\[
 \|H(\theta)-H(\eta)\|_{\rm op}
 \le B_A\|\theta-\eta\|_2.                                   \tag{10}
\]

Pure-state trace distance is at most the Hilbert norm between any chosen unit representatives, so
`F_t` is `|t| B_A`-Lipschitz.  Theorem B at radius `2 epsilon` gives

\[
 N_{2\epsilon}(P(C^D))\ge(2\epsilon)^{-(2D-2)}.                \tag{11}
\]

Apply Theorem A and rearrange.

## Corollary -- ordinary local shells miss Haar coverage until recurrence scale

For the nearest-neighbour full Pauli shell used in the static-local plateau theorem,

\[
 m=12n-9,\qquad R=1,\qquad B_A\le\sqrt m,\qquad D=2^n.         \tag{12}
\]

At every fixed `epsilon in (0,1/2)`, projective-state `epsilon`-density therefore requires

\[
 \boxed{
 |t|\ge \exp\!\left(\Omega\!\left({2^n\over n}\right)\right).} \tag{13}
\]

Brown state saturation is expected at `2^n/poly(n)`.  Thus global projective Haar coverage is
separated from Brown saturation by an exponential in `2^n/n`, not by a missing polynomial estimate.

The same proof applies to every bounded `m`-parameter autonomous Hamiltonian family and every target
whose fixed-resolution covering entropy is known.  It is not specific to qubits, locality, or Haar
measure.

## Distributional interpretation

Let `nu_t` be any pushforward of a probability on `K`.  Any condition implying that every
`epsilon`-ball has positive `nu_t` mass forces `supp(nu_t)` to be `epsilon`-dense and is subject to
`(8)`.  In particular the theorem obstructs uniform lower-mass equidistribution and
`W_infinity`-coverage before `(13)`.

It does **not** obstruct weak convergence tested by finitely many observables, low-order designs, or
Wasserstein metrics that permit a small amount of mass to travel far.  Total-variation convergence
is even more strongly impossible whenever an `m`-dimensional Lipschitz image has Haar measure zero,
but that separate singularity fact is not used here.

## Conjecture attack and positive survivor

### Conjecture 1 -- prove the Brown ramp by showing static endpoints become Haar-like

**Killed.**  Any Haar-like condition strong enough to occupy every fixed-resolution state-space
ball cannot begin near Brown saturation for an `O(n)`-parameter shell.  The lower time is
`exp(Omega(2^n/n))`.

### Conjecture 2 -- replace Haar coverage by high source metric entropy

**Killed as a sufficient mechanism.**  Equation `(1)` is an upper bound on source-image entropy.
Large upper capacity does not prove that distinct parameter cells have distinct endpoints and says
nothing about circuit avoidance.

### Positive survivor -- asymmetric complexity before randomness

The cubic-phase theorem already proves near-maximal complexity on a static-local plateau while a
fixed two-copy local test distinguishes the same ensemble from Haar.  The present theorem shows why
this asymmetry is structurally necessary on Brown time scales:

\[
 \boxed{
 \text{Brown complexity can arise from avoiding one tiny easy set;
 it cannot arise from covering the ambient state space.}}       \tag{14}
\]

The live ramp mechanism must therefore be **one-sided and directional**.  It must control the
pairing of the static endpoint law with the first-entry equilibrium potential of the short-circuit
tube, retain occupied endpoint image and sheet multiplicity, and beat only the complete circuit
union.  Global designs, global discrepancy norms, minimum spectral gaps, and global source entropy
are stronger in irrelevant directions and are now excluded as proof targets.

## Hostile audit

1. **The abstract inequality is classical metric entropy.** Correct.  Novelty cannot be assigned to
   Theorem A alone.
2. **Density is much stronger than complexity.** Correct and essential.  The result is a route-killing
   theorem, not a complexity lower bound.
3. **Approximate designs need not be dense.** Correct.  No design no-go is claimed.
4. **The result does not prove growth.** Correct.  The first-onset/ramp estimate remains the sole
   missing Brown clause.
5. **Unbounded or exponentially many parameters evade it.** Correct.  Formula `(8)` displays the
   exact escape hatch through `R`, `B_A`, and `m`.
6. **Integrable families may never cover.** Correct.  The theorem supplies a necessary time, never a
   sufficient one.
7. **Popular phrasing could overclaim.** The only justified interpretation is: near-maximal circuit
   complexity does not require, and on the Brown time scale cannot be explained by, global Haar
   coverage of an ordinary static local ensemble.

## External novelty audit

The possible headline interpretation is rejected.  Cui, Schuster, Mao, Huang, and Brandao,
[*Random unitaries from Hamiltonian dynamics*](https://arxiv.org/abs/2510.08434), prove a stronger
all-time statement for constant-local Hamiltonians: every such time-independent Hamiltonian
ensemble is efficiently distinguishable from Haar and fails to form even a unitary 2-design.  The
present theorem neither subsumes nor improves that result for constant-local systems.

The surviving contribution is narrower but exact: `(1)--(8)` give a quantitative
parameter--time--resolution tradeoff for **any** bounded low-parameter static family and any target
with known metric entropy, including nonlocal families outside the constant-local distinguisher.
This is useful formal infrastructure and a rigorous route exclusion, not significant external
novelty for the master paper.  It must not be presented as the paper's discovery.

## Formalization target

Formalize without a weaker substitute:

1. the exact finite-net/dense-target entropy inequality for the existing coefficient sphere;
2. the corresponding fixed-time static-orbit entropy lower bound using
   `exists_staticOrbit_net`;
3. a target entropy instantiation already present in Lean;
4. then add projective Haar-ball volume and pure-state trace-distance infrastructure needed for the
   exact exponent `(8)`.

No numerical computation is required.

## Log

- 2026-08-10 -- conjectured global static-Haar mixing as a ramp mechanism; falsified by the
  parameter--time covering calculation; extracted asymmetric complexity-before-randomness survivor.
- 2026-08-10 -- complete paper proof written; hostile scope corrections added; Lean proof opened.
- 2026-08-10 -- `staticOrbit_targetEntropy_le` and
  `staticOrbit_booleanReflection_coverage_time` proved in
  `HTGeometry/StaticEnsembleCoverageTimeBarrierLaw.lean`; projective Haar exponent remains open.
- 2026-08-10 -- external audit found arXiv:2510.08434's stronger permanent constant-local 2-design
  no-go; headline novelty rejected and theorem retained only as a quantitative supporting law.
