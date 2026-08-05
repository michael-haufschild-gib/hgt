# The universal replica-collision law of quantum return

- **ID:** `universal-replica-collision-law-of-quantum-return`
- **Stage:** 1-in-progress
- **Type:** MASTER-LAW CANDIDATE / COMPLETE RECURRENCE CLASSIFICATION /
  LOCAL-INTERACTION EXTREMALITY
- **Replaces as master candidate:**
  `temporal-codimension-interaction-law.md`
- **Scientific status:** `[KINEMATIC LAW LEAN-PROVED]`
  `[LOCAL GENERATOR PAPER-PROVED] [PRIORITY PROVISIONALLY CLEARED]`
  `[ONE-KNOB POLYNOMIAL LAYER LEAN-PROVED]`
  `[LOCAL GENERATOR LEAN PROOF OPEN]`
- **Public manuscript rule:** the manuscript never mentions formal
  verification and never counts it toward novelty or significance.

## Discovery

> **Quantum return is an energy-collision law.**

For every stationary probability energy spectrum, every long-time moment of
return is exactly the probability that two independent replicas have the
same total energy. The complete hierarchy of these replica collisions
determines every continuous long-time return statistic.

The new physical theorem is extremal:

> **At fixed spectral weights, generic nearest-neighbour interaction makes
> quantum return as rare as unitarity permits, at every replica order
> simultaneously.**

The higher physical interpretation is:

> **Local interaction opens exponentially many dimensions of quantum time.**

At zero interaction, \(n\) uncoupled \(q\)-level constituents have at most
\(n(q-1)\) independent projective energy rhythms. For a generic fixed
nearest-neighbour interaction profile, turning one scalar coupling knob to
any value outside a countable exceptional set raises that number to
\(q^n-1\), including values arbitrarily close to zero. The same jump removes
every nontrivial equal-energy replica collision, minimizes every long-time
return moment and makes global recurrence doubly exponentially sparse in
maximum entropy.

This is a singular asymptotic transition, not an instantaneous laboratory
effect. At every fixed observation horizon \(T\), the interacting and
uncoupled histories converge as the coupling tends to zero. After arbitrarily
long observation at fixed nonexceptional coupling, their completed temporal
dimensions differ exponentially. The noncommuting weak-coupling and
long-time limits explain how an arbitrarily weak interaction can be
asymptotically decisive while remaining invisible for a long finite time.

An open one-dimensional chain of \(n\) \(q\)-level systems has only
polynomially many local coupling parameters but \(D=q^n\) energy levels.
For almost every such local Hamiltonian, no nontrivial equality between two
finite energy multisets survives. Consequently the chain attains the
absolute collision floor at every order and generates the same exact
long-time return law as \(D\) independent phases.

This is stronger than the temporal-codimension formulation. Temporal
dimension, exact recurrence, return density, observer dependence,
continuous-spectrum escape and interaction-induced rarity are derived from
one completed visible energy law and its replica collisions. They are not
parallel clauses.

“Universal” has an exact domain: `(RC)` holds for every probability spectral
measure of stationary unitary return. The interaction theorem then
classifies the generic bounded-range finite-chain realization. It does not
mean every physical phenomenon or every nonstationary/open/gravitational
model is governed by `(RC)`.

## Universal law

Let \(\mu\) be any probability measure on \(\mathbb R\). Define
\[
 A_\mu(t)=\int_{\mathbb R}e^{-itE}\,d\mu(E),
 \qquad
 F_\mu(t)=|A_\mu(t)|^2 .
                                                        \tag{1}
\]
Let \(\widetilde\mu(B)=\mu(-B)\), let
\(\nu_\mu=\mu*\widetilde\mu\), and for \(m\geq1\) define
\[
 \kappa_m(\mu)
 =
 \nu_\mu^{*m}(\{0\})
 =
 (\mu^{*m}*\widetilde{\mu^{*m}})(\{0\}).
                                                        \tag{2}
\]
Equivalently, if
\[
 S_m=E_1+\cdots+E_m,\qquad
 S'_m=E'_1+\cdots+E'_m
\]
for two independent \(m\)-replicas sampled from \(\mu\), then
\[
 \kappa_m(\mu)=\mathbb P(S_m=S'_m).                    \tag{3}
\]

For every \(m\geq1\),
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}
 \int_{-T}^{T}F_\mu(t)^m\,dt
 =
 \kappa_m(\mu).
 }
                                                        \tag{RC}
\]
For every continuous \(h:[0,1]\to\mathbb R\), the long-time mean of
\(h(F_\mu(t))\) exists and is uniquely determined by
\(\{\kappa_m(\mu)\}_{m\geq0}\). Thus `(RC)` is a complete law, not a
one-moment plateau formula.

The replica language is exact rather than metaphorical. On an \(m\)-copy
forward/backward energy space, `(3)` is the spectral mass at zero of the
relative generator
\[
 L_m=H_1+\cdots+H_m-H'_1-\cdots-H'_m.                 \tag{4}
\]
The operator realization `(4)` is a manuscript claim only after its exact
spectral-measure bridge is formalized. The measure statement `(RC)` is
already unconditional.

## Finite-spectrum collision floor

Let
\[
 \mu=\sum_{j=1}^{D}p_j\delta_{E_j},
 \qquad p_j>0,\quad \sum_jp_j=1.
\]
For \(k=(k_1,\ldots,k_D)\in\mathbb N^D\), write
\[
 |k|=\sum_jk_j,
 \qquad
 {m\choose k}=\frac{m!}{k_1!\cdots k_D!}.
\]
Every spectrum has the unavoidable permutation collisions
\[
 \boxed{
 \kappa_m(\mu)\geq
 \sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{\!2}\prod_{j=1}^{D}p_j^{2k_j}.
 }
                                                        \tag{5}
\]
Equality holds for every \(m\) simultaneously exactly when equality of two
finite energy multisets forces equality of their multiplicity vectors:
\[
 \sum_jk_jE_j=\sum_j\ell_jE_j,\quad |k|=|\ell|
 \quad\Longrightarrow\quad k=\ell.                    \tag{6}
\]
Condition `(6)` is maximal projective rational rank. Any nontrivial
resonance adds a strictly positive term to at least one replica moment.

Therefore maximal projective rank is not merely a number of clocks. It is
the exact all-order minimizer of quantum return fluctuations at fixed
spectral weights.

## Local-interaction extremality theorem

Let \(\mathcal L_{P_n,q}\) be the full real space of arbitrary one-site and
nearest-neighbour two-site Hermitian terms on an open \(q\)-level path.
Put \(D=q^n\).

The paper proof in
`../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`
gives, for Lebesgue-almost every \(H\in\mathcal L_{P_n,q}\),
\[
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_j-E_1:2\leq j\leq D\}=D-1.                      \tag{7}
\]
Combining `(5)`--`(7)` gives, for every state and every replica order,
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}F_\mu(t)^m\,dt
 =
 \sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{\!2}\prod_{j=1}^{D}p_j^{2k_j}.
 }
                                                        \tag{8}
\]
This is the exact independent-phase law. It holds for one fixed static
local Hamiltonian, with time providing the ensemble. No random-matrix
ensemble, stochastic dynamics, chaos premise, central-limit premise or
finite-order no-resonance assumption is used.

It also proves every finite \(r\)-no-resonance condition simultaneously.
In replica language, the only zero-energy sectors of every finite
forward/backward replica are the unavoidable permutation matchings.

### One interaction knob is enough

Split the local coupling space canonically into onsite and pure interaction
parts,
\[
 \mathcal L_{P_n,q}
 =
 \mathcal A_{n,q}\oplus\mathcal V_{n,q}.
\]
The paper proof in
`../2-fully-proven/local-interaction-replica-collision-extremality.md`
establishes a sharper activation theorem. For almost every fixed onsite
background \(A\) and almost every fixed nearest-neighbour interaction
profile \(V\), there is a countable exceptional set \(C_{A,V}\), containing
zero, such that
\[
 \boxed{
 \rho(A+gV)=q^n-1
 \quad\text{for every }g\notin C_{A,V}.
 }
                                                        \tag{8a}
\]
At \(g=0\), \(\rho(A)\leq n(q-1)\), whereas arbitrarily weak nonzero
choices outside a countable set activate the full \(q^n-1\) rank. Thus the
exponential hierarchy does not require independent tuning of polynomially
many couplings after the background and interaction shape have been
selected: one scalar control is generically enough.

This is an exact infinite-time transition. It does not say the new
frequencies become resolvable within a coupling-independent finite time.

### Singular weak-interaction/long-time law

Let \(X_H^{\mathcal O}(T)\) be the finite-horizon orbit of a finite reporter
family \(\mathcal O\), and let
\[
 \mathcal B_{\mathcal O}^2
 =
 \sum_a\lambda_a\|B_a\|_{\mathrm{HS}}^2.
\]
The perturbation theorem in
`../2-fully-proven/finite-horizon-observer-temporal-profile-stability.md`
gives, for every \(A,V,g,T\),
\[
 \boxed{
 d_{\mathrm H}\!\left(
 X_{A+gV}^{\mathcal O}(T),X_A^{\mathcal O}(T)
 \right)
 \leq
 2T|g|\,\|V\|_{\mathrm{op}}\mathcal B_{\mathcal O}.
 }
                                                        \tag{8b}
\]
Hence fixed finite-resolution histories are continuous at \(g=0\). For a
spectrally complete reporter family, however, Theorem C2 gives for almost
every \((A,V)\) and every \(g\notin C_{A,V}\),
\[
 \boxed{
 \dim_{\mathrm M}X_A^{\mathcal O}(\infty)
 \leq n(q-1),
 \qquad
 \dim_{\mathrm M}X_{A+gV}^{\mathcal O}(\infty)
 =q^n-1.
 }
                                                        \tag{8c}
\]
Equations `(8b)`--`(8c)` are the exact noncommuting-limit statement:
bounded-time observation sees a smooth weak-coupling limit, while completed
quantum time undergoes an exponential dimension jump at arbitrarily weak
generic interaction.

## Exact spectral-form-factor law

For the normalized spectral form factor
\[
 X_D(t)=\frac1D\left|\sum_{j=1}^{D}e^{-itE_j}\right|^2,
                                                        \tag{9}
\]
almost every local chain obeys, for every \(m\geq1\),
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}X_D(t)^m\,dt
 =
 \frac1{D^m}
 \sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{\!2}.
 }
                                                        \tag{10}
\]
The right side is the \(m\)-th moment of
\[
 \left|
 \frac1{\sqrt D}\sum_{j=1}^{D}U_j
 \right|^2,
 \qquad U_j\stackrel{\mathrm{iid}}{\sim}\operatorname{Haar}(\mathbb T).
                                                        \tag{11}
\]

For each fixed \(m\), the terms with \(m\) distinct indices contribute
\[
 \frac{\binom Dm(m!)^2}{D^m}\longrightarrow m!,
                                                        \tag{12}
\]
while every repeated-index pattern has fewer than \(m\) freely selected
indices and contributes \(o(1)\). Hence the moments in `(10)` converge to
\(m!\), the moments of a unit-mean exponential random variable.
Moment determinacy then yields the iterated thermodynamic/late-time law
\[
 \boxed{
 \lim_{n\to\infty}\lim_{T\to\infty}
 \operatorname{Law}_{t\in[-T,T]}X_{q^n}(t)
 =
 \operatorname{Exp}(1).
 }
                                                        \tag{13}
\]
The order of limits in `(13)` is load-bearing and may not be reversed
without another theorem.

The exact finite-size moment formula and the independent-spectrum
exponential limit are already known abstractly from
Campos Venuti--Odavić--Hamma (2026). The new consequence, if the local
generator survives, is not that abstract probability theorem: it is that
almost every static nearest-neighbour local Hamiltonian unconditionally
satisfies its difficult rational-independence premise.

## How prior results become corollaries

```text
completed observer energy law mu
              |
              v
replica sum laws mu^{*m}
              |
              +-- zero collision masses  -> every long-time return statistic
              +-- support difference group -> exact-return type
              +-- rational rank          -> temporal dimension
              +-- upper-endpoint tail    -> recurrence-density exponent
              +-- reporter projection    -> observer dependence
              +-- peripheral restriction -> dissipative return ceiling
              +-- spectral completion    -> local-data identifiability boundary
              +-- local interaction      -> simultaneous collision minimum
```

Consequences:

1. **Poincaré/finite quantum recurrence.** Pure-point compactness provides
   return; `(RC)` supplies the complete frequency of every return level.
2. **Temporal dimension.** For a finite positive-weight spectrum with a
   nondegenerate visible return target, the dimension of the
   support-difference group is recovered from the high-fidelity tail of the
   return law. “Time has an observer-dependent dimension” survives as a
   finite-sector corollary, not the master postulate.
3. **Observer dependence.** A reporter changes the visible energy law and
   therefore its entire replica tower. Observer composition becomes
   composition of visible gap modules.
4. **Continuous spectra.** If \(\mu\) is atomless, every positive-order
   collision is zero and the full asymptotic fidelity law is
   \(\delta_0\), including singular-continuous spectra.
5. **Dissipation.** The peripheral spectral sector supplies the surviving
   probability law; transient mass fixes the ceiling before `(RC)` applies.
6. **Rate--distortion recurrence.** Reverse-water information estimates a
   finite-resolution upper tail of the same return law.
7. **Global completion.** Complete local moment/Krylov data can fail to
   determine the completed \(\mu\), hence can fail to determine the replica
   tower and the future recurrence law.
8. **Free versus interacting systems.** Free many-body energies inherit
   only \(O(n)\) base frequencies and unavoidable nontrivial replica
   collisions. Generic interaction creates \(q^n-1\) projective frequencies
   and deletes all nontrivial collisions.

## Community questions answered

1. **Are generic two-body eigenenergies rationally independent?**
   Projectively, yes already in a nearest-neighbour path, if the local
   generator theorem survives audit.
2. **Are hidden energy resonances forced by locality?**
   No. Polynomially many bounded-range coupling parameters generically
   generate exponentially many rationally independent projective energies.
3. **What fixes the complete late-time return distribution?**
   The all-order replica collision tower `(RC)`.
4. **When is the independent-phase or exponential late-time law exact?**
   Finite size: exactly under maximal projective rank. Thermodynamic limit:
   `(13)` after the long-time limit.
5. **What distinguishes free/integrable and generic interacting return?**
   Survival or destruction of nontrivial replica zero-sum sectors at all
   orders, not level repulsion alone.

## Novelty boundary

Not novel:

- Wiener's one-moment theorem;
- convolution and characteristic-function identities;
- Kronecker--Weyl equidistribution;
- the abstract fact that flexible operator families can be generically
  nonresonant;
- central-limit heuristics for independent phases.

Candidate new package:

1. maximal projective rank for almost every static bounded-degree
   nearest-neighbour qudit Hamiltonian despite only polynomially many local
   parameters;
2. one-knob activation: for almost every fixed onsite background and
   interaction profile, every coupling strength outside a countable
   exceptional set activates the full exponential rank;
3. simultaneous attainment of the absolute return-moment floor `(5)` at
   every replica order;
4. unconditional realization, by one deterministic local Hamiltonian, of
   the known independent-spectrum law `(8)`--`(13)`;
5. proof that bounded-range interaction supplies the rational independence
   previously assumed for nonintegrable SFF universality;
6. one replica-collision classification subsuming the prior recurrence
   corpus.

Items 2--5 are consequences of item 1 plus polynomial restriction,
harmonic-analysis and known random-walk results. Their novelty is the
local-Hamiltonian premise discharge and its one-parameter activation, not
the abstract moment formula or exponential distribution.

Closest direct sources currently known:

- Vallejo-Fabila--Torres-Herrera (2023) obtains exponential late-time
  distributions when a central-limit condition holds;
- Riddell--Bertini (2024) constructs rationally independent one-particle
  free fermions and proves that free many-body spectra still fail
  Poisson spectral-form-factor moments; it explicitly leaves the interplay
  with interacting perturbations as future research;
- Campos Venuti--Odavić--Hamma (2026) proves exact SFF moments for
  independent spectra and the thermodynamic Gaussian/exponential law under
  a weight condition, but treats many-body spectral independence as a hard
  premise and supports it numerically for nonintegrable models;
- Szymański (2024) asks whether generic two-body eigenenergies are
  rationally independent;
- continuum quantum-control literature proves generic nonresonance in
  infinite-dimensional potential families, not exponential rank from a
  polynomial-dimensional tensor-local family.

## Honest physics reach

The law is directly about stationary quantum dynamics, return probability,
spectral form factors, higher-point form factors, equilibration assumptions
and many-body resonance.

It gives a rigorous benchmark for finite-entropy black-hole or de Sitter
models: any proposed finite Hamiltonian must establish its visible spectral
type and replica collisions before entropy-based recurrence estimates are
licensed. A model satisfying `(7)` has fixed-resolution global return
density suppressed as
\[
 \exp[-c_\varepsilon(e^{S_{\max}}-1)].
                                                        \tag{14}
\]
This is a benchmark, not a theorem that gravitational Hamiltonians satisfy
`(7)`, not a black-hole calculation, and not a solution of information loss.

## Hostile Nature review

### Strongest editorial case

The paper would replace the decisive rational-independence assumption by an
exact theorem inside the most local nontrivial architecture: a static
one-dimensional degree-two chain. Existing work derives the
independent-phase and exponential laws once this hard premise is granted;
the new local theorem would establish the premise for almost every physical
coupling in the chain. It answers an explicit two-body resonance question
and explains prior recurrence results through one replica invariant.

### Current rejection reasons

1. The local maximal-rank theorem is paper-proved but lacks independent
   specialist review and unconditional formal proof.
2. Exact-object priority remains open in tensor-structured spectral Galois
   and quantum-control literature.
3. Abstract exact SFF moments, random-walk equivalence and the exponential
   independent-spectrum limit are prior results. Reject if the manuscript
   claims them as new.
4. The result is asymptotic in time. No two-sided finite-horizon crossover
   shows when a laboratory can see the independent-phase law.
5. The coupling family is the full inhomogeneous nearest-neighbour local
   space, not a translation-invariant or fixed-parameter model.
   The one-knob theorem fixes a generic background and interaction profile,
   but does not make a prescribed profile generic.
6. The thermodynamic statement uses the ordered limit
   \(T\to\infty\) before \(n\to\infty\).
7. The replica-operator formulation `(4)` still needs an exact formal
   spectral bridge; only the measure law is currently authorized.
8. Gravity relevance remains a diagnostic benchmark, not a derived
   prediction.
9. The singular weak-coupling/long-time law `(8b)`--`(8c)` is
   dependency-closed on paper but not yet formally closed; the manuscript
   may not claim it before that audit.

### Rejection triggers

Reject the paper if it:

- calls the classical collision identity alone the novelty;
- claims exact SFF moments, the independent-phase random-walk
  representation or its exponential limit as new;
- equates exact rational independence with a finite experimental mixing
  time;
- calls `(10)` random-matrix spectral statistics at finite physical times;
- reverses the limits in `(13)`;
- calls the pivot recurrence metric the optimal projective operator norm;
- claims real black holes satisfy the local-chain theorem;
- says formal verification contributes scientific novelty;
- retains unrelated water-clock, open-channel or local-completion sections
  that cannot be derived from the replica law.

## Exact falsifiers

The core is false if any of the following occurs:

1. the all-order collision identity `(RC)` fails for a probability spectrum;
2. a nontrivial finite energy-sum equality contributes no positive extra
   term to the corresponding moment with positive weights;
3. a positive-measure subset of the stated local path family has nonmaximal
   projective rank without an enforced symmetry;
4. the exact moment count `(10)` differs from the independent-phase count;
5. repeated-index patterns contribute at leading order in `(12)` for fixed
   \(m\);
6. a prior theorem already gives the same local generator and all-order
   extremal return law.

## Gate plan

1. Finish exact-object priority search for tensor-local spectral Galois
   theorems and all-order local spectral-form-factor plateaux.
2. Obtain or simulate independent specialist proof attack on the endpoint
   perturbation and symmetric relation-polynomial argument.
3. Audit the dependency-closed proof card
   `../2-fully-proven/local-interaction-replica-collision-extremality.md`.
4. Formalize the finite collision floor and equality classification.
5. Formalize the nearest-neighbour local generator theorem.
6. Formalize one-knob activation and the finite-horizon perturbation
   sandwich.
7. Formalize finite-size moment formula and iterated exponential limit.
8. Prove a two-sided finite-horizon activation theorem or state the exact
   impossibility boundary.
9. Rewrite the manuscript around `(RC)` and the local extremality theorem;
   delete every section that reads as an independent paper.
10. Run hostile specialist and Nature editorial reviews.
