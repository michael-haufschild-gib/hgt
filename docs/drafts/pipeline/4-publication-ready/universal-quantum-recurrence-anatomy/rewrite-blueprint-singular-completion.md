# Rewrite blueprint: singular completion of quantum recurrence

## Editorial status

Not Nature-ready yet. Mathematical spine is now coherent and formally
verified; external priority of the joined mechanism remains open. Nature's
published gate requires original research, outstanding scientific importance,
and a conclusion interesting across disciplines. Its editorial screen further
asks whether results are novel, arresting, and have immediate and far-reaching
implications. Technical correctness alone cannot pass.

## Public question and exact answer

**Question.** Can bounded-time quantum observations determine the dimension
and recurrence structure of the system's completed future?

**Answer.** No. From three levels onward, every finite spectrum is arbitrarily
close to spectra with different completed temporal dimensions. More strongly,
for every observation horizon, every tolerance, and every positive admissible
dimension, one can choose a nearby Hamiltonian of exactly that dimension whose
Heisenberg evolution stays within tolerance for every normalized probe
throughout the horizon. The completed recurrence order parameter is a
discontinuous wall indicator even though every finite-time reporter is
continuous. Its entire boundary layer is the universal sinc profile with
inverse-time width. Robust exceptions are exactly the relations annihilated by
all allowed perturbations.

## Proposed title

**A universal singularity law for quantum recurrence**

Alternative, more arresting but still defensible:

**The dimension of a quantum future is nowhere stable**

## One-sentence public result

An arbitrarily small change can switch a quantum system among every possible
positive dimension of its infinite-time phase motion while leaving every
bounded-time experiment arbitrarily unchanged.

For countably infinite pure-point systems, “every possible” is replaced by the
proved statement that one arbitrarily weak, self-adjoint, trace-class,
domain-preserving perturbation produces every finite temporal rank and a dense
full infinite projective future.

## Single mathematical mechanism

For a persistent finite spectral carrier indexed by `I`, let

\[
  D_E(k)=\sum_{i\in I}k_iE_i,
  \qquad \sum_i k_i=0,
\]

be the projective detuning map on balanced integer characters. The paper must
be organized around one formula:

\[
  \widehat\nu_{E,T}(k)
  =\operatorname{sinc}(T D_E(k))
  \longrightarrow
  \mathbf 1_{\ker D_E}(k).
  \tag{1}
\]

This is not one result among many. It is the mechanism.

- `ker D_E` is the exact projective recurrence-relation lattice.
- the image rank of `D_E` is completed temporal dimension;
- kernel rank plus image rank is projective spectral capacity;
- under linear controls, `D_E(k)` becomes an affine functional, so each
  recurrence character is protected everywhere, absent everywhere, or lives
  on one closed nowhere-dense wall;
- equation (1) makes finite-time dynamics continuous and completed recurrence
  discontinuous on every transverse wall;
- the scaled wall coordinate `x=x_0+xi v/T` produces the exact sinc boundary
  layer;
- character height is the first replica order carrying the wall;
- a `(2n+1)` phase grid per coordinate exactly recovers every order-`n`
  coefficient, and the one-coordinate threshold is worst-case sharp.

Persistence is the front end of this law, not a second headline. For every
probability energy spectrum, stationary fidelity retains only point-spectrum
mass and scales by its square. For every finite contraction, the raw return
history equals its peripheral carrier modulo late-time-vanishing histories;
the quotient class vanishes exactly when peripheral mass vanishes. The
detuning law acts only after this persistent carrier has been selected.

## Headline theorem package

The manuscript's main theorem should have four logically dependent parts.

1. **Persistent selection.** State precisely the arbitrary-spectrum closed
   law and finite-contraction quotient law. Do not claim arbitrary infinite
   open dynamics.
2. **Singular arithmetic completion.** State equation (1), exact kernel/image
   conservation, wall trichotomy, finite-time continuity, completed
   discontinuity and sinc scaling.
3. **Dense phase stratification.** For `d+1` levels, every rank
   `1 <= k <= d` is dense. From three levels onward, completed temporal
   dimension is nowhere continuous. Both rank-zero relation phase and
   positive relation-rank phase are dense.
4. **Operational impossibility and recovery.** Every target positive temporal
   dimension is compatible with every bounded-horizon normalized-probe record
   to arbitrary tolerance. Conversely, finite-grid phase cycling recovers a
   selected wall with exact height and resource law.

Countable trace-class saturation is the infinite-dimensional corollary, not a
separate paper: every countable pure-point Hamiltonian lies arbitrarily close
to a domain-equivalent Hamiltonian whose future tails are dense in the full
projective product torus, whose only exact global return is zero, and whose
finite windows realize every dimension.

## What old material survives

- Keep persistent threshold and arbitrary-spectrum collision law only as
  selection consequences.
- Keep recurrence protection, finite-horizon C-star bound, countable
  trace-class saturation, exact replica height and finite-grid readout.
- Move water-filling/rate-distortion deadlines to a corollary or separate
  paper. They do not follow from equation (1) closely enough for the main
  spine.
- Move observer coherence graphs to a short “observer restriction” corollary.
- Remove Anderson localization from this paper. It is a separate spatial
  question and previously made the narrative look assembled.
- Retain black-hole spectral form factors only as a disciplined implication:
  bounded-time or perturbative semiclassical agreement cannot certify an exact
  late-time recurrence phase. Do not claim a black-hole microstate model, an
  information-paradox solution, or a prediction of an astrophysical signal.

## Broad physics implication

The theorem separates two notions often conflated in quantum dynamics:

1. stability of every bounded-time experiment under a small Hamiltonian
   perturbation;
2. stability of the exact completed recurrence phase.

The first holds with a dimension-independent operator-norm estimate. The
second fails maximally: every positive temporal dimension is nearby, and the
completed order parameter jumps on dense arithmetic strata. This is not
ordinary chaos—trajectories need not diverge exponentially. The singularity
is created by completing time before taking the weak-perturbation limit.

For holographic spectral inference, the defensible conclusion is a no-go:
finite-time agreement of a semiclassical description cannot determine whether
the exact boundary spectrum belongs to a recurrent arithmetic phase or which
completed temporal dimension it has. Current black-hole spectral-form-factor
research already treats late-time discreteness and nonperturbative completion
as central; this paper supplies a model-independent mathematical obstruction
and exact crossover law, not a gravity model.

## Hostile reviewer attack

### Likely desk-rejection argument

“The ingredients are elementary or classical: Kronecker--Weyl, rational
independence, rank-nullity, sinc Fourier windows, generic nonresonance,
peripheral spectral theory and phase cycling. The paper repackages them with
new terminology. Exact arithmetic recurrence is measure-zero and physically
uncertifiable, so the claimed broad impact is semantic.”

### Required answer in the manuscript

The novelty claim must be the joined theorem, not any ingredient:

- all positive completed temporal dimensions occur arbitrarily close to every
  finite spectrum;
- any chosen dimension remains compatible with all normalized probes on any
  fixed horizon and at any positive tolerance;
- the completed order parameter is the pointwise limit of continuous physical
  reporters but is discontinuous at every transverse wall;
- the full crossover, minimum nonlinear order, and exact finite-setting
  recovery cost are determined;
- unrestricted perturbations have no protected nonzero recurrence character,
  while restricted families have an exact annihilator classifier;
- one trace-class direction realizes the infinite countable saturation with
  domain preservation.

If external literature already contains this joined statement or an immediate
specialization, the Nature claim fails. If only the component tools exist, the
paper must demonstrate why their conjunction changes a physical inference:
finite-time Hamiltonian validation cannot validate completed recurrence or
temporal dimension.

### Remaining rejection triggers

1. Calling projective rational rank “dimension of time” without an independent
   operational characterization. The completed phase ensemble and detector
   hierarchy must precede the interpretation.
2. Using “phase transition” without stating that parameter strata are dense
   arithmetic walls rather than thermodynamic phases.
3. Treating the unrestricted history-corona splice theorem as realizability by
   quantum Hamiltonians.
4. Claiming arbitrary infinite open-system coverage. Presently proved open
   coverage is every finite contraction.
5. Claiming experimental feasibility from a combinatorial setting count.
   Hardware noise and coherent control assumptions remain unstated.
6. Claiming a black-hole or cosmological discovery. Only an inference no-go is
   proved.
7. Hiding that exact recurrence is fragile. Fragility is the result, not a
   caveat.

## Nature gate assessment on 1 August 2026

- **Original research:** plausible for the joined singular-completion theorem;
  not yet cleared.
- **Outstanding importance:** plausible only if framed as a universal limit on
  inference of infinite-time quantum structure, with exact finite-time
  crossover and protection boundary.
- **Interdisciplinary conclusion:** understandable: no bounded experiment can
  determine a system's exact completed time dimension.
- **Arresting/surprising:** yes at statement level; must survive specialists'
  “classical ingredients” objection.
- **Immediate implications:** quantum-control certification and late-time
  spectral inference.
- **Far-reaching implications:** thermodynamic/large-system and holographic
  order-of-limits problems, stated as no-gos only.

Current honest verdict: stronger than prior manuscript and now a genuine
universal mechanism, but not yet entitled to “Nature-ready” until a primary-
source priority matrix clears the exact joined theorem and manuscript gives an
independent operational definition of temporal dimension.
