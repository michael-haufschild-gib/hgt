# Observer-rank autonomous no-shortcut law

- **ID:** observer-rank-autonomous-no-shortcut-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / sharp aggregate shortcut law for static local dynamics
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR PAPER-PROVED]`
- **Parent:** `static-local-complexity-law.md`, obligation O4
- **Master conjecture:** `observer-spectral-shortcut-action-law.md`
- **Supersedes:** `autonomous-shortcut-free-energy-law.md` as active conjecture
- **Date:** 2026-08-05

## Exact model

Fix `q>=2`.  For `n>=q`, let `P_(n,q)` be the nonidentity `n`-qubit Pauli
words of weight at most `q`, let

\[
 m_n=|P_{n,q}|=\sum_{k=1}^q3^k{n\choose k},
 \qquad
 H_n(J)={1\over\sqrt{m_n}}\sum_{P\in P_{n,q}}J_PP,
 \tag{1}
\]

and sample `J` from the standard Gaussian on `R^(m_n)`.  The input is
`Phi_n=|0>^(tensor n)`.  Fix a finite exactly specified universal two-qubit
gate alphabet `G`, pure-state trace distance, no postselection, and clean
ancillas returned to zero.  Write `C_epsilon(psi)` for the least word length
preparing `psi` from `Phi_n` to trace error at most `epsilon`.

Let

\[
 v_{n,q}=2\sum_{k=1}^q{n\choose k}.                 \tag{2}
\]

This is not a fitted exponent.  The Stage-2 observer theorem proves that it
is exactly the real rank of the projective Hamiltonian action at `Phi_n`,
equivalently the rank of the pure-state multiparameter QFI matrix.

Use the explicit local interaction scale

\[
 \Lambda_n(J)={1\over\sqrt{m_n}}\sum_{P\in P_{n,q}}|J_P|. \tag{3}
\]

## Conjecture

There is `epsilon_0(q,G)>0` such that, for every fixed
`0<epsilon<epsilon_0(q,G)` and every `eta>0`, there are constants

\[
 a,c,C_\eta,b>0,
\]

depending only on `q`, `G`, `epsilon`, and `eta`, such that for all
sufficiently large `n` and every

\[
 n^{C_\eta}\le t\le 2^{cn},                         \tag{4}
\]

the complete Hamiltonian-dependent shortcut event obeys

\[
 \boxed{
 \Pr_J\!\left\{
 C_\epsilon(e^{-itH_n(J)}\Phi_n)
 \le {a t\Lambda_n(J)\over n^b}
 \right\}
 \le t^{-(1-\eta)v_{n,q}}.
 }                                                    \tag{5}
\]

Conversely, for possibly different constants and throughout the same window,
the observer-stationary tube gives

\[
 \Pr_J\!\left\{
 C_\epsilon(e^{-itH_n(J)}\Phi_n)
 \le {a t\Lambda_n(J)\over n^b}
 \right\}
 \ge t^{-(1+\eta)v_{n,q}}.                           \tag{6}
\]

The lower inequality is already paper-proved.  In the normalization (1),
`J=J_F+J_perp` with `F=ker T_(Phi_n)`, and

\[
 \|J_\perp\|\le {\epsilon\over t}
 \quad\Longrightarrow\quad
 \Delta(e^{-itH_n(J)}\Phi_n,\Phi_n)\le\epsilon.
 \tag{6a}
\]

The `v_(n,q)`-dimensional Gaussian ball in (6a) has mass at least

\[
 \left({c\epsilon\over t\sqrt{v_{n,q}}}\right)^{v_{n,q}}. \tag{6b}
\]

Taking `t>=n^(C_eta)` with `C_eta` large enough absorbs the
`v_(n,q)^(-v_(n,q)/2)` factor and yields (6).  Thus only the upper bound (5)
is conjectural.

Thus the proposed sharp logarithmic law is

\[
 \boxed{
 {-\log\Pr(\text{relative shortcut at time }t)\over\log t}
 =v_{n,q}+o(v_{n,q}).
 }                                                    \tag{7}
\]

The genuinely new assertion is (5).  It is selector-aware: the approximating
circuit may depend arbitrarily on `J`, and no union over fixed circuit targets,
compiler, carrier classification, Haar approximation, or undefined
“shortcut format” is assumed.

## Why this is the stronger replacement

The failed free-energy conjecture attempted to classify shortcut geometry
before controlling the actual selector.  Equation (5) instead makes one
risky prediction: after all circuit words and all recurrence components are
aggregated, the largest shortcut mass is already visible infinitesimally at
the initial ray.  A local metrological rank would therefore control a global
computational escape exponent through exponentially long autonomous time.

For fixed `q`,

\[
 v_{n,q}={2\over3^q}m_n+O(n^{q-1}).                 \tag{8}
\]

Hence (5) is strong enough for a time net through exponential time and would
close the quantitative first-hard-time obstruction in O4 at the correct
effective exponent.  Combined with the already formalized autonomous cone,
completed-time plateau, recurrence, and permanent two-query locality witness,
it would supply the missing growth input to the master law.

## First hostile attack

### One-local fast forwarding

The claim excludes `q=1`.  This is not an ad hoc repair: the complete
one-local Pauli family is uniformly synthesizable with linear-size circuits,
so its shortcut exponent is zero although its QFI rank is `2n`.  Any later
universal classification must recover this branch rather than suppress it.

### Known continuous and periodic carriers

For `q>=2`, the largest currently proved carrier is the stationary kernel of
dimension `m_n-v_(n,q)`.  The commuting Pauli carriers, one-local carrier, and
known mixed periodic carriers all have strictly smaller leading dimension and
therefore do not contradict (5).  This comparison is only a survival test;
it is not evidence for the upper bound.

The commuting comparison is now exhaustive for Pauli-word sectors, not only
for the diagonal example.  If `A` is any set of distinct pairwise commuting
nonidentity Pauli words of weight at most `q`, then

\[
 |A|\leq\sum_{k=1}^q(2^k-1){n\choose k}.
 \tag{8a}
\]

Indeed, on each fixed support of size `k`, the words form a binary symplectic
isotropic set and hence contain at most `2^k-1` nonidentity elements.  It
follows that every translated recurrence lattice generated by commuting
Pauli involutions has transverse exponent

\[
 m_n-|A|\geq
 \sum_{k=1}^q(3^k-2^k+1){n\choose k}\geq v_{n,q}.
 \tag{8b}
\]

Thus no commuting Pauli refocusing frame beats the observer-stationary tube.
The dependency-closed proof is in
`../3-formalized/commuting-pauli-observer-rank-dominance.md`.  The live
recurrence threat is narrower: a mixed carrier combining a genuinely
noncommuting stationary continuum with transverse periodic directions.

### Fixed-block fast forwarding

This class is now excluded sharply.  The paper- and Lean-proved fixed
observer-channel law says that if a coefficient subspace acts inside a fixed
real observer channel `K`, then

\[
 \dim U\le m-v_\Phi+\dim K.                          \tag{9}
\]

A fixed complex `d`-dimensional invariant block containing the input has
`dim_R K=2(d-1)`.  Hence any `d=o(n^q)` efficiently diagonalizable block can
change only the `o(v_(n,q))` term and cannot falsify (5) at leading order.

### Quadratic and Gaussian families

They are not fixed linear blocks, so (9) does not dispose of them.  Dimension
comparison nevertheless removes the known continuous family as a leading
competitor.  A general quadratic Hamiltonian on `n` fermionic modes has real
coefficient dimension `binom(2n,2)=2n^2-n`.  For `q=2`, the stationary kernel
already has dimension

\[
 m_{n,2}-v_{n,2}=n+7{n\choose2}
 ={7\over2}n^2+O(n),                                \tag{10}
\]

and for every fixed `q>=3` it has order `n^q`.  Thus even an embedding of the
entire quadratic family into the weight-at-most-`q` Pauli dictionary would
not supply a larger continuous carrier.  Jordan--Wigner fixed-weight
quadratic subfamilies are smaller still.  What remains unexcluded is a
growing family of encodings/translates whose component entropy contributes at
leading `Theta(v)` order; no known quadratic fast-forwarding construction has
that property.

### Easy-state manifolds

Allowing all product or bounded-depth targets can reduce finite-`n`
codimension by `O(n s)` and can alter lower-order powers.  It does not change
the leading `Theta(n^q)` exponent in (7) for fixed `q>=2` and sub-direct
budgets.  This is why (5) includes the arbitrary `eta v_(n,q)` slack rather
than asserting an exact finite-`n` power.

### Fixed-size saturation

The time window ends below a fixed exponential fraction of Hilbert capacity.
No `t->infinity` statement is made at fixed `n`; compact-state saturation
therefore does not kill (5).

### Dimension-dependent Gaussian constants

A `v_(n,q)`-dimensional Euclidean small ball has a prefactor of order
`v_(n,q)^(-v_(n,q)/2)`.  Therefore the stationary-tube lower bound cannot be
written as `t^(-(1+eta)v)` uniformly from one fixed polynomial threshold for
every arbitrarily small `eta`.  The dependence `C_eta` in (4) is
load-bearing: taking `log t` sufficiently larger than `eta^(-1) log v`
absorbs the small-ball prefactor.  Any version with one `C` preceding the
quantifier `for every eta` is false.

### Circuit selector

The selector is not assumed to be computable or geometrically organized.
This removes the circularity that killed the predecessor.  It also makes the
open core harder: targetwise phase anti-concentration, QFI, Hall rank, and
linear-span generation cannot by themselves prove (5).

### Literature collision

Fast-forwarding classifications cover commuting, quadratic, block-diagonal,
permutation-invariant, and low-energy frustration-free systems.  Random-circuit
and stochastic-Hamiltonian results prove complexity growth when fresh
randomness is injected.  Current static-local results provide plateau,
recurrence, or Haar distinguishability separately.  No audited source proves
(5), a matching observer/QFI-rank shortcut exponent, or an aggregate robust
state-complexity lower bound through exponential time.  This remains
`[NOVELTY UNVERIFIED]`, not a priority claim.

## Verdict and first open core

**Verdict:** `SURVIVES FIRST HOSTILE ATTACK`.

`[OPEN CORE]` Prove a selector-aware upper bound for the radial pullback

\[
 \{J:C_\epsilon(e^{-itH_n(J)}\Phi_n)
       \le a t\Lambda_n(J)/n^b\}
\]

with loss `t^(eta v_(n,q))`, uniformly in (4).  Equivalently, prove that any
shortcut family whose Gaussian tube mass beats the stationary kernel at
leading logarithmic order forces an explicit counterexample to (5).

No Lean work is authorized on (5) until this paper proof closes.  The proved
observer-stationary lower obstruction remains a separate Stage-2
formalization candidate.

## Final hostile falsification -- gapped easy eigenlines

The upper law `(5)` is false on its stated exponential-time window. The
dependency-closed counterexample is
`../3-formalized/gapped-eigenstate-uniform-shortcut-floor.md`.

For the literal full fixed-`q` Pauli Gaussian ensemble, centre a
full-dimensional coefficient box of width `epsilon^2/(16m_(n,q))` at the
diagonal Hamiltonian

\[
 m_{n,q}^{-1/2}\sum_{\varnothing\ne S,\ |S|\le q} Z_S.
\]

The input product ray is its unique top eigenline with gap at least
`2/sqrt(m_(n,q))`. Every Hamiltonian in the box has an eigenline within
trace distance `epsilon/4` of the input, so its complete time orbit stays
within `epsilon/2` of the input. The Gaussian box mass is at least

\[
 \left(c\epsilon^2/m_{n,q}\right)^{m_{n,q}},
\]

independently of time. At `t=2^(c_0 n)` this is
`exp(-O_q(n^q log n))`, whereas `(5)` demands
`exp(-Omega_q(n^(q+1)))`. This contradiction holds for every positive
exponential-window constant.

The exact why is that the Duhamel stationary tube prices transverse
perturbations by `1/t`, while spectral-gap stability prices a neighborhood
of an easy eigenline once and for all. Observer rank is therefore a local
short-time action, not the aggregate exponential-time shortcut action.

The positive survivor is the time-uniform gapped-eigenstate shortcut floor.
The wider observer--spectral minimum is not falsified: its completed-orbit
mass includes this floor and therefore forces an early spectral crossover.

## Master-law interpretation

This conjecture is now the pre-capacity branch of
`observer-spectral-shortcut-action-law.md`.  Its exponent is predicted to
hold while

\[
 v_{n,q}\log t<I_{n,\epsilon}(R),
\]

where `I^comp` is the exact completed spectral-orbit shortcut information for
the same ensemble.  After this crossover, the proposed universal action
saturates at `I^comp`; plateau and recurrence are therefore not separate
pasted-on laws.  Identifying `I^comp` with Fubini--Study rate--distortion is a
separate unproved ensemble-transfer theorem.  This interpretation is
conjectural and authorizes no additional paper claim.
