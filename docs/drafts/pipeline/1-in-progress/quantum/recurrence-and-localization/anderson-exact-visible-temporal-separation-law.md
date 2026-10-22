# Anderson exact–visible temporal separation law

- **ID:** `anderson-exact-visible-temporal-separation-law`
- **Stage:** 1-in-progress
- **Type:** FROZEN CONJECTURE / ANDERSON LOCALIZATION / OBSERVER RECURRENCE
- **Status:** `[CONJECTURE] [GLOBAL-RANK ARM LEAN-PROVED] [ONE-SIDED LOCAL ARM BRIDGE] [TWO-SIDED ARM OPEN] [NATURE GATE CLOSED]`
- **Date frozen:** 2026-07-30
- **Parent paper:**
  `../4-publication-ready/universal-quantum-recurrence-anatomy/main-observer-localization.tex`

## Public discovery sought

> **Localization does not make quantum time simple. It separates the
> complexity that exists exactly from the complexity any local observer can
> resolve.**

The claim concerns observer-visible spectral recurrence, not spacetime
dimension, proper time, consciousness or an arrow of time.

## Frozen hunch

For a finite-volume Anderson Hamiltonian on a connected \(d\)-dimensional
graph with sufficiently regular independent disorder, two apparently
opposite statements can hold simultaneously.

1. The complete projective energy-gap module has maximal rational rank
   almost surely:
   \[
     \operatorname{rank}_{\mathbb Q}
     \operatorname{span}_{\mathbb Q}
     \{E_j-E_0:1\le j<D_\Lambda\}
     =D_\Lambda-1 .
   \]
2. In a rigorous localization regime, the recurrence target seen by a
   fixed site \(x\) has finite-resolution complexity controlled by
   localization volume rather than \(D_\Lambda\). At spectral-tail
   tolerance \(\delta\),
   \[
     M_{x,\Lambda}(\delta)
     \le
     C_d\,\xi^d
     \bigl[\log(C/\delta)\bigr]^d
   \]
   with constants uniform in total volume on the localization event.

Consequently exact global recurrence dimension can diverge with total
volume while local finite-resolution recurrence complexity stays
volume-independent.

The strongest desired two-sided form additionally proves a matching lower
bound for the local metric entropy or minimax recurrence clock, and a
delocalized scaling that is parametrically different at the same physical
resolution.

No proof route is part of this frozen conjecture.

## Exact invariant split

The conjecture keeps three quantities distinct.

1. **Exact arithmetic temporal rank:** every nonzero visible gap counts,
   independently of its amplitude.
2. **Finite-resolution local spectral complexity:** distant modes below the
   observer tolerance are charged as tail distortion.
3. **Fixed-system recurrence time:** depends additionally on energy scale
   and Diophantine arithmetic; rank or covering geometry alone does not
   determine it.

Anderson localization normally suppresses weights without making them zero.
It can therefore compress item 2 while leaving item 1 maximal. Equating the
two is false.

## Existing proved shadows

- `FiniteAndersonProjectiveGenericityLaw.lean` proves more than the first
  finite-volume arm: for every fixed finite Hermitian hopping matrix,
  maximally projective onsite potentials are dense, residual and
  full-Lebesgue-measure.
- `FiniteAndersonRecurrenceLocalitySeparationLaw.lean` and
  `FiniteAndersonSurvivalNonExitLaw.lean` prove that maximal projective rank
  can coexist, in the same nonzero-hopping Hamiltonian, with arbitrarily
  small off-diagonal transitions and site-survival loss throughout any
  prescribed finite horizon.
- `FiniteAndersonLocalizedSurvivalQuadraticLaw.lean` proves a deterministic
  finite-volume post-exit recurrence bound from explicit exponential
  spectral-weight decay and shell growth.
- `FiniteAndersonLocalizedResolutionScaleLaw.lean` proves the corresponding
  explicit resolution-scale deadline.
- `FiniteQuantumObserverGraphSharpness.lean` proves worst-spectrum finite
  observer exponents.
- `LBitObserverTimeDimensionLaw.lean` proves an exact layer-additive
  finite-resolution temporal-dimension law for scaled diagonal l-bit
  spectra.
- `ArithmeticTemporalRankInstability.lean` proves dense exact rational-rank
  strata and finite-horizon stability.

Thus the finite-volume global-rank arm is closed, and the one-sided
localization-volume recurrence certificate is closed once explicit
eigensystem decay and shell bounds are supplied. They do not prove a
single named infinite-volume Anderson ensemble theorem with uniform
localization data, a matching lower entropy law or phase-separating
delocalized scaling.

## Hostile attack and exact residue — 30 July 2026

**Verdict on the one-sided formulation:** `[REDISCOVERED]`.

The proposed upper bound is an effective-spectral-support corollary of
existing recurrence packing bounds once exponential localization is
inserted. The compact phase-group and weighted-covering mechanisms are
classical. Spatial return, survival probability, local density of states
and spectral-form-factor diagnostics are already standard localization
probes.

The sharp two-sided entropy form would require lower bounds on local
spectral weights throughout growing shells. Standard Anderson localization
supplies upper decay but not such uniform lower shell weights; rare small
amplitudes and nodal structure make the proposed lower hypothesis
physically unnatural in general. An engineered exponentially localized
unitary dressing can realize the desired entropy law, but that construction
is a dressed atomic model rather than a standard Anderson Hamiltonian and
does not survive the significance gate.

**Strongest positive survivor:** `[LOCAL-RESEARCH] [LEAN-PROVED]`.

Localization constrains finite-resolution observer geometry but does not
constrain exact recurrence arithmetic. This is proved in two complementary
classes:

1. finite Anderson matrices can have maximal exact projective rank while
   all site histories remain arbitrarily close to their initial values for
   any prescribed finite horizon;
2. exact all-order l-bit Hamiltonians can conserve every local charge and
   have zero configuration transport for all time while attaining temporal
   rank \(2^N-1\), with one countable quasi-local coefficient field
   attaining full rank on every finite restriction.

This survivor changes the correct interpretation but is not, by itself, a
new Anderson-localization theorem.

## Stronger replacement conjecture: noncommuting temporal limits

`[BRIDGE] [CORRECT UNDER UNIFORM DYNAMICAL LOCALIZATION] [NOT HEADLINE NOVELTY]`

The failure of the one-sided entropy bound as novelty suggests a stronger
statement about the singular relation between exact and visible time.
For a finite box \(\Lambda\), site \(x\), full projective phase orbit
\(G_{\Lambda,x}\) and its local survival metric \(d_{\Lambda,x}\), let
\[
 N_{\Lambda,x}(\varepsilon)
 =
 N_{\rm cover}(G_{\Lambda,x},d_{\Lambda,x},\varepsilon),
 \qquad
 \Theta_{\Lambda,x}(\varepsilon)
 =
 \frac{\log N_{\Lambda,x}(\varepsilon)}
 {(D_\Lambda-1)\log(1/\varepsilon)} .
\]
The normalization is the maximal projective small-scale covering exponent.

For a standard localized Anderson exhaustion with regular independent
disorder, the stronger hunch is that almost surely
\[
 \boxed{
 \lim_{|\Lambda|\to\infty}
   \lim_{\varepsilon\downarrow0}
     \Theta_{\Lambda,x}(\varepsilon)=1,
 \qquad
 \lim_{\varepsilon\downarrow0}
   \lim_{|\Lambda|\to\infty}
     \Theta_{\Lambda,x}(\varepsilon)=0 .}
\]

The first order resolves every nonzero local spectral weight before taking
the thermodynamic limit and therefore sees maximal exact temporal
dimension. The second holds detector resolution fixed while volume grows;
uniform localization leaves only a volume-independent effective head, so
the visible fraction of the maximal clock vanishes.

Public sentence:

> A localized quantum system can be maximally complex in exact time and
> asymptotically simple to every finite-resolution local observer; which
> statement is seen depends on whether resolution or system size is taken
> to infinity first.

This replacement is not killed by the absence of uniform lower shell
weights: the vanishing order needs an upper localization tail, while the
maximal order is a fixed-finite-volume small-scale statement. It would be
falsified by a localized full-rank model whose local phase metric loses
finite-volume dimension, by failure of uniform effective-head control, or
by a primary result proving the same normalized order-of-limits law.

### Hostile verdict

No primary paper located states the boxed normalized double limit verbatim,
but it is a routine corollary once its hypotheses are frozen:

1. full visible rational rank makes each fixed-volume orbit a smooth
   \((D_\Lambda-1)\)-torus at sufficiently fine scale;
2. uniform strong dynamical localization compresses every fixed-resolution
   orbit to \(O((\log(1/\varepsilon))^d)\) effective modes;
3. standard covering estimates then give a numerator independent of
   \(D_\Lambda\) at fixed \(\varepsilon\).

The same limit in the exact l-bit construction reduces to Boolean support
counting. If \(q(N,R)\) counts nonempty supports of diameter at most \(R\),
then
\[
 q(N,R)=(N-R+1)2^R-1\quad(R<N),
 \qquad
 q(N,R)=2^N-1\quad(R\ge N),
\]
so \(q(N,R)/(2^N-1)\) has the two iterated limits \(0\) and \(1\).
This is mathematically correct but scientifically a `[BRIDGE]`.

The claim is false if “localized” means only pure-point spectrum or
pointwise exponentially localized eigenfunctions; uniform dynamical
localization is load-bearing. It also does not transfer to generic
many-body localization, where interaction-induced dephasing prevents a
uniform-in-time finite local compression.

**Relentless-interrogation result:** no stronger Anderson statement survives
without importing one of the following genuinely new ingredients: a sharp
two-sided local spectral-weight law, a localized/critical/delocalized
converse with distinct scaling, or a finite-time observable that recovers a
mobility edge or critical exponent beyond existing survival, LDOS, IPR and
spectral-form-factor diagnostics. Standard localization theory does not
supply those ingredients, and adding them as assumptions would encode the
desired conclusion. Anderson locality therefore remains a supporting
application of the universal recurrence paper, not its novelty source.

## External priority boundary

The following are occupied and cannot be novelty claims.

- Anderson localization and quantum recurrence have been linked since
  Fishman–Grempel–Prange (1982).
- Survival probability, local revivals and return probability are existing
  localization and mobility-edge diagnostics.
- Pure-point phase motion, compact phase groups and Haar return statistics
  are classical almost-periodic/Kronecker theory.
- Effective-support post-exit recurrence bounds already imply the
  one-sided
  \(\log T=O((\log(1/\varepsilon))^{d+1})\) localization corollary.
- Compact-group covering/volume reciprocity is classical infrastructure.

Potential novelty is only the simultaneous exact–visible separation,
preferably with sharp two-sided scaling and an experimentally distinguishable
consequence.

## Hard falsifiers

1. a forced balanced integer eigenvalue relation in the claimed Anderson
   ensemble;
2. inability to make localization constants uniform in volume in any
   nontrivial rigorous regime;
3. local finite-resolution complexity growing with ambient volume despite
   uniform localization;
4. no matching lower bound under physically natural assumptions;
5. extended and localized regimes having indistinguishable finite-size
   complexity scaling after energy scale and detector resolution are fixed;
6. the exact–visible separation already appearing in primary literature;
7. every proposed experimental estimator reducing to known IPR, survival
   probability or spectral-form-factor diagnostics;
8. finite coherence preventing access to every parameter regime where the
   predicted separation is nontrivial.

## Lean obligations

1. formalize a finite random-potential model or an exact deterministic
   ensemble interface;
2. prove absence of every nonzero balanced integer eigenvalue relation in
   the stated domain;
3. define the observer metric-entropy/effective-support profile used in the
   theorem;
4. prove uniform localization-tail upper transfer;
5. prove a nontrivial lower bound or a precise impossibility theorem;
6. connect the same profile to both post-exit deadlines and return-window
   frequency without identifying minimax and fixed-spectrum clocks;
7. prove the global–local separation capstone;
8. run foreground compilation, axiom audit, formal lint and final module
   build.

## Nature gate

The route is rejected unless all hold:

- one named physical model, not only abstract localized coefficients;
- unconditional mathematical theorem in the stated model;
- sharp or phase-separating scaling, not only a one-sided certificate;
- finite-resolution, noise-robust measurement protocol;
- a prediction distinct from known localization diagnostics;
- primary-literature priority clearance;
- hostile reviewer agreement that the result changes a physical inference.

Until then Anderson locality is a supporting corollary, not the master
paper's novelty claim.
