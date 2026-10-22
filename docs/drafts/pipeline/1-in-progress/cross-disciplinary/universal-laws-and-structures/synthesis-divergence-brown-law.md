# First-entrance synthesis-divergence Brown law

- **ID:** `synthesis-divergence-brown-law`
- **Stage:** 1 -- in progress
- **Type:** frozen conjecture / ordinary static-local Brown law
- **Parents:** `../2-fully-proven/first-entrance-gate-renewal-prefix-law.md`,
  `../2-fully-proven/circuit-complexity-selection-synthesis-divergence-law.md`,
  `../../../3-formalized/geometric-skeleton-brown-ramp-transfer-law.md`
- **Status:** `[CONJECTURE] [OPEN CORE] [HOSTILE ATTACK ACTIVE]`
- **Date:** 2026-08-10

## Public sentence

The complexity of autonomous quantum time is the rarity of reaching its states
for the first time by random local actions: growth is increasing first-arrival
surprisal, the plateau is sustained rarity, and recurrence is exact collapse.

This is a mathematical conjecture about ordinary static local-Hamiltonian
ensembles. No black-hole statement is asserted.

## Retired primitive

The earlier version used raw geometrically killed endpoint Green mass. That
primitive is retired.

For a singleton target, the proved entrance--return law gives

\[
 G_a(x,y)=\frac{F_a(x,y)}{1-R_a(y)}.
\]

For a target tube, the scalar return multiplier becomes a return resolvent.
Raw endpoint occupation therefore mixes first preparation with arbitrarily
many post-success returns. It is not a pure synthesis observable.

Label: `[RAW GREEN FALSIFIED AS EXACT PREPARATION; RATE-EQUIVALENT]`.

The normalized raw Green mass \(\overline G_a\) and first-entrance mass obey

\[
 (1-a)\mathcal F_a\le\overline G_a\le\mathcal F_a.
\]

Their surprisals differ by at most \(-\log(1-a)\). Therefore the earlier raw
Green conjecture was not wrong at Brown exponential scale. First entrance
corrects its operational meaning and recurrence accounting; it does not make
the quenched estimate asymptotically easier.

## Frozen conjecture

Use the ordinary bounded-strength nearest-neighbour fixed-shell Hamiltonian
ensemble, easy cubic seed, finite inverse-closed local gate alphabet, and robust
errors of the parent programme. Let \(M_n\) be gate-alphabet size. Fix
\(a\in(0,1)\) independently of \(n\).

For target

\[
 \psi_{H,t}:=e^{-itH}\chi_n,
\]

let \(\tau_{n,\varepsilon}(H,t)\) be the first time the uniform
right-extension gate-word process from \(\chi_n\) enters
\(B_\varepsilon(\psi_{H,t})\). This synthesis enumeration reverses ordinary
chronological word labels but preserves length, uniform word prior, and robust
circuit complexity. Equivalently, it is the inverse-gate backward walk from
the target into the seed tube. Define first-entrance mass and normalized
first-entrance free energy

\[
 \mathcal F_{n,a,\varepsilon}(H,t)
 :=\mathbb E_{\rm gate}\!\left[
   a^{\tau_{n,\varepsilon}(H,t)}
   \mathbf 1_{\{\tau_{n,\varepsilon}(H,t)<\infty\}}
 \right],                                                            \tag{1}
\]

\[
 \boxed{
 \Phi_{n,a,\varepsilon}(H,t)
 :=\frac{-\log\mathcal F_{n,a,\varepsilon}(H,t)}
          {\log(M_n/a)}.}                                             \tag{2}
\]

Let

\[
 \rho_{n,a}:=\frac{\log(1/a)}{\log(M_n/a)}.
\]

The proved first-entrance sandwich gives, unconditionally,

\[
 \boxed{
 \rho_{n,a}C_\varepsilon(\psi_{H,t})
 \le \Phi_{n,a,\varepsilon}(H,t)
 \le C_\varepsilon(\psi_{H,t}).}                                     \tag{3}
\]

The conjecture is that there are constants \(a,c>0\), geometric ratio
\(q>1\), polynomial boundary terms \(K_n\), and one target-independent
return/fast-forwardable-carrier filtration such that, with quenched probability
\(1-o(1)\) for one Hamiltonian draw, all retained geometric skeleton times
from the postlocal boundary layer through
\(T_{\rm sat}=\Theta(2^n/\operatorname{poly}(n))\) obey

\[
 \boxed{
 \Phi_{n,a,\varepsilon_+}(H,T_j)
 >c v_nT_j-K_n.}                                                       \tag{4}
\]

The last endpoint begins a continuous block on which

\[
 \boxed{
 \Phi_{n,a,\varepsilon_-}(H,t)
 =\Omega(2^n/\log M_n).}                                              \tag{5}
\]

At every later recurrence satisfying

\[
 d(e^{-it_RH}\chi_n,\chi_n)\le\varepsilon_R,
\]

the seed already lies in the target tube, so the proved recurrence law gives

\[
 \boxed{
 \mathcal F_{n,a,\varepsilon_R}(H,t_R)=1,
 \qquad
 \Phi_{n,a,\varepsilon_R}(H,t_R)=0.}                                  \tag{6}
\]

Here \(v_n\) is the local simulation speed used by the formalized
geometric-skeleton transfer. Equations (3)--(4) would prove the continuous
Brown lower ramp; the existing simulator gives the matching upper ramp.
Existing plateau, recurrence, and local/Haar separator theorems would then
complete growth--plateau--recurrence while locality remains distinguishable
from Haar.

Equation (4) is frozen as a physical mathematical hunch. No part of it is
counted as proved.

## What changed scientifically

At fixed positive fugacity, raw endpoint Green surprisal was conjectured to
make a stronger prediction than circuit complexity because long successful
words might create overwhelming mass. The first-entrance theorem disproves
that concern for the corrected observable.

Every first-hit word is prefix-free, and

\[
 (a/M_n)^C\le\mathcal F\le a^C.
\]

Therefore (3) makes \(\Phi\) and robust circuit complexity equivalent up to
explicit constants at each fixed \(n,a,M_n\). First-entrance free energy is
not a new complexity class and does not add an independent physical
hypothesis. Its value is structural:

1. it is external to shortest-word minimization;
2. it separates every post-hit loop exactly, while changing fixed-fugacity
   rates by only an additive constant;
3. it preserves all pre-hit witness multiplicity as a prefix-free partition;
4. it turns the complete circuit union into one first-arrival moment;
5. it collapses exactly, rather than polynomially, at recurrence.

Thus it is a possible proof coordinate for Brown growth, not a substitute for
the missing Brown theorem.

## Evidence

1. `[PAPER-PROVED]` The entrance--return resolvent separates first preparation
   from recurrence exactly.
2. `[PAPER-PROVED]` First-hit word mass is prefix-free and bilipschitz-equivalent
   to robust word complexity at fixed fugacity.
3. `[PAPER-PROVED]` First-hit surprisal is the exact KL information projection
   of the geometric gate prior onto successful first-entry words.
4. `[CORPUS]` The full static-local plateau supplies complexity
   \(\Omega(2^n/\log n)\), later recurrence, and permanent non-Haar locality,
   but with uncontrolled onset.
5. `[FORMALIZED CORPUS]` The geometric-skeleton theorem reduces the continuous
   ramp to \(O(n)\) simultaneous endpoint events.
6. `[LITERATURE]` Random-circuit linear growth is proved. The corresponding
   static time-independent local-Hamiltonian law at this scale was not found in
   the audited literature.

## Hostile attack

### Attack 1 -- this only renames complexity

**Verdict:** mathematically correct at the level of pointwise scaling. Equation
(3) proves constant-factor equivalence. No novelty may be claimed merely from
renaming \(C\) as \(\Phi\).

**Survivor:** first entrance supplies a new exact decomposition and a
prefix-free probabilistic representation. Significance requires that this
representation enable the missing quenched static-local estimate.

### Attack 2 -- first-hit expectation recreates the circuit union

For any random target \(V\), the proved complete-union inequality is

\[
 \Pr\{C(V)\le s\}
 \le(M_n/a)^s\mathbb E[\mathcal F_{n,a,\varepsilon}(V)].              \tag{7}
\]

The factor \((M_n/a)^s\) is still exponential in target depth. A weak average
collision estimate does not close Brown scale.

**Required response:** obtain an incidence or anti-concentration exponent that
beats the full gate-word entropy at the desired depth. Prefix-freeness removes
post-hit redundancy but not genuine pre-hit route entropy.

### Attack 3 -- recurrence leakage

Quasiperiodicity creates arbitrarily accurate easy returns. A uniform all-time
lower bound is false.

**Required response:** one target-independent recurrence/carrier cut, paid
once. Retained times obey (4); actual recurrence is reported by the exact
collapse (6), not silently discarded.

### Attack 4 -- integrable local countermodels

Commuting or free local Hamiltonians can remain easy. A law for every local
Hamiltonian is false.

**Required response:** the frozen statement concerns the specific ordinary
noncommuting full-shell ensemble already used by the plateau theorem. It does
not quantify over all local Hamiltonians.

### Attack 5 -- zero-temperature circularity

Taking \(a\downarrow0\) recovers complexity exactly and would contribute no
new proof method.

**Required response:** (4) fixes \(a>0\) independently of \(n\). No tropical
limit is allowed in the conjectured estimate.

### Attack 6 -- source entropy

The Hamiltonian ensemble and every short orbit segment have low arbitrary
metric entropy.

**Verdict:** not a falsifier. The proved two-currency law forces hard
low-information codewords to have large synthesis divergence. Source entropy
alone neither proves nor disproves (4).

The quantitative closure is now formalized.  If an `m`-parameter bounded
static endpoint image is `epsilon`-dense in a target of external
`2 epsilon`-covering number `N`, then

\[
 N\le\left(1+{2|t|\sqrt m\over\epsilon}\right)^m.
\]

For `m=O(n)` and `|t|<=2^n poly(n)`, this supplies only `O(n^2)` bits of
source-image capacity, exponentially below the `Theta(2^n)` exponent of the
complete Brown circuit union.  A source-Jacobian or coarea argument that uses
only this capacity cannot prove (9); occupied-image separation from the easy
set must contribute the missing exponent.

Global Haar coverage is also retired as a mechanism, not merely left
unproved.  Fixed-resolution projective coverage by such a shell requires
`exp(Omega(2^n/n))` time, and Cui--Schuster--Mao--Huang--Brandao
(`arXiv:2510.08434`) prove the stronger external fact that constant-local
time-independent Hamiltonian ensembles fail even a unitary 2-design at every
time.  Neither result falsifies (4): high circuit complexity can coexist with
low source entropy and permanent non-Haar locality.  They prove that the
missing estimate must remain the signed, one-sided pairing in (10), not any
global mixing norm.

## Exact open core

For each of the \(O(n)\) geometric skeleton endpoints, prove after one common
return/carrier cut

\[
 \Pr_H\left\{
  \Phi_{n,a,\varepsilon_+}(H,T_j)
  \le c v_nT_j-K_n
 \right\}
 \le e^{-\kappa r_n},                                                  \tag{8}
\]

with one replica/confidence schedule \(r_n=O(\log n)\), or prove an equally
strong direct quenched estimate, uniformly through \(T_{\rm sat}\).

Equivalently, using (7), prove a first-entry incidence estimate whose exponent
survives the complete circuit union at depth
\(s_j\asymp v_nT_j\):

\[
 \boxed{
 \mathbb E_H\!\left[
   \mathbf 1_{\mathcal R_n}
   \mathcal F_{n,a,\varepsilon_+}(H,T_j)
 \right]
 \le e^{-\kappa r_n}\left(\frac a{M_n}\right)^{s_j}.}                 \tag{9}
\]

The estimate must retain first-entry sheet multiplicity and the occupied
endpoint image after return removal. Minimum spectral-gap anti-concentration,
source codebook entropy, generic phase Sobolev norms, and absolute global
moment norms are already retired.

## Sharpened invariant after the capacity attack

On any finite reversible inverse-gate discretization, put

\[
 A_{n,\varepsilon}:=B_\varepsilon(\chi_n),
\]

let \(h_{n,a,\varepsilon}\) be its discounted equilibrium potential, and let
\(\nu_{n,t}\) be the static endpoint law after the common return cut. The
proved inverse-word identity gives

\[
 \mathbb E_H\mathcal F_{n,a,\varepsilon}(H,t)
 =\mathbb E_{V\sim\nu_{n,t}}h_{n,a,\varepsilon}(V).
\]

Writing \(\pi_n\) for the stationary gate law, this is exactly

\[
 \boxed{
 \frac{\operatorname{cap}_{n,a}(A_{n,\varepsilon})}{1-a}
 +\delta_{n,a,\varepsilon}(t),}
 \tag{10}
\]

where \(\delta\) is the signed pairing of
\(\nu_{n,t}-\pi_n\) with this one equilibrium potential.

A global resolvent or \(H^{-1}\) norm is explicitly not the target: the proved
global-discrepancy obstruction shows that it lower-bounds \(\chi^2\)-distance
and is incompatible with low-support or singular endpoint laws. The open core
is the directional upper estimate

\[
 \boxed{
 \frac{\operatorname{cap}_{n,a}(A_{n,\varepsilon_+})}{1-a}
 +\delta_{n,a,\varepsilon_+}(T_j)
 \le e^{-\kappa r_n}
       \left(\frac a{M_n}\right)^{s_j}.}
 \tag{11}
\]

This formulation permits permanent non-Haar locality: discrepancies in every
observer direction orthogonal to \(h_{n,a,\varepsilon}\) are unrestricted.
The unsolved step is to derive (11) from ordinary static-shell geometry while
retaining incidence sheets. It is not global mixing, design convergence, or
minimum spectral-gap anti-concentration.

## Lean status

No Lean statement is written while (4) remains conjectural and corpus refactor
is active. The first-entrance theorem is paper-proved only and queued for later
formalization. A dependency-closed proof of (8) or (9) would open the final
formalization gate.

## 2026-08-13 concurrent correction and quenched replica target

The free-word first-entrance potential above remains mathematically valid, but it is no longer the
intrinsic preparation reporter for bounded-degree local hardware.  After quotienting exact swaps of
support-disjoint gates, incomparable minimal causal prefixes can share a completion.  Their
cylinders are not prefix-free: for independent letters `a,b`,

\[
 \uparrow a\cap\uparrow b=\uparrow(ab).
\]

The paper-proved successor `../../../3-formalized/concurrent-causal-heap-accessibility-law.md` replaces
the word sum by the probability of the **union** of successful causal-prefix cylinders under the
finite trace law `pi_z(T)=z^|T|/Z(z)`.  It proves exact cylinder mass `z^|u|`, exact recurrence value
one, a relative-entropy preparation action, intrinsic bounded-dependence capacity, and a soft
`1/delta`-Lipschitz reporter independent of Hilbert dimension and circuit count.  Thus equations
`(9)--(11)` above remain sufficient free-word formulations but are superseded as the active
bounded-degree target.

The paper-proved child `../2-fully-proven/quenched-causal-replica-action-law.md` identifies the new
growing-replica object.  With one common static Hamiltonian in every replica,

\[
 Z_r(t)=\mathbb E_H F_{A,z}(\Phi_H(t))^r,
\]

and exactly

\[
 -\log Z_r(t)
 =\inf_{q\ll\rho_H}
   \left\{D(q\Vert\rho_H)+r\,\mathbb E_qJ_{A,z}(\Phi_H(t))\right\}.
\]

Consequently, the replica estimate `Z_r<=z^(rs)e^(-kappa r)` is equivalent to one action gap for
every tilted Hamiltonian law:

\[
 {1\over r}D(q\Vert\rho_H)+\mathbb E_qJ_{A,z}(\Phi_H(t))
 \ge s\log(1/z)+\kappa.
\]

This retains source fibres, occupied endpoint image, causal sheet multiplicity, and the complete
circuit union.  It also proves a hostile correction: growing replicas amortize a rare carrier's
source cost as `D/r`, so they expose rather than suppress rare easy Hamiltonians.  Common recurrence
mass is the exact nondecaying replica sector and is removed once; all remaining low-action carriers
must still be classified quantitatively.  This action gap is the exact open core of the
growing-replica route.  It is sufficient, not necessary, for a direct Brown lower-tail proof: a
rare easy carrier can be harmless to the desired event probability yet dominate `Z_r`.  Lean
remains read only during refactor.

## 2026-08-21 canonical endpoint-design correction

For finite projective endpoint dictionaries, raw label unions, worst action degree, and squared
incidence-action budgets are no longer sharp frontier. Formalized determinant-design law retains
actual occupied replica endpoint image and every post-return source sheet. Its exact same-draw
sufficient statistic is

\[
 \dim\operatorname{span}\{\phi_c^{\otimes r}\}
 \left[{r!\over d^r}+\sum_c w_c^*A_{r,\delta}(E_H,\phi_{H,c})
 +e^{-(T\delta)^2/2}\right],
\]

with `w*` supplied unconditionally by endpoint determinant optimum. A strict bound below explicit
later-hit cell mass proves first return to complete dictionary is later than `T`; same fixed
nearest-neighbour Hamiltonian also obeys certified laboratory ramp. Infinite or adaptive target
classes reduce to finite nets without selector measurability.

This does not prove Brown onset. Active ordinary-ensemble core is now a quenched growing-replica
lower-tail estimate for canonical weighted near-action term, uniform over Brown times and an
entropy-efficient continuous-circuit net. Unlike global Haar/design convergence, this statistic
allows permanent locality and uses only spectral direction selected by occupied circuit image.
Formal card: `../../../3-formalized/optimal-design-weighted-static-choi-first-return-law.md`.
