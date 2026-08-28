# Stationary recurrence bound-state mass law

- **ID:** `stationary-recurrence-bound-state-mass-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** quantum-recurrence corpus audit and literature-first frontier audit, 2026-08-28
- **Priority warning:** no absolute first claim is authorized.  The exact support-edge/inverse-law
  formulation was not found in searches below; its ingredients have classical Wiener--Eberlein,
  RAGE and almost-periodic ancestry.

## Frozen hunch

### Public sentence

The completed distribution of survival probability measures total bound-state weight exactly,
although no finite observation horizon can estimate that weight uniformly over all quantum
spectra.

### Universal statement

Let `mu` be any probability energy measure on `R`, let `p` be total mass of its pure-point part,
and let `R_mu` be weak limit of survival-fidelity laws under centered uniform time sampling.

1. Existing point-spectrum scaling gives

   `R_mu = (x |-> p^2 x)_* R_normalized-point-spectrum`.

2. **No-gap support conjecture.**  The topological support of `R_mu` is one closed interval
   `[rho_mu, p^2]`.  Its right endpoint is exactly `p^2`.  Equivalently:

   - `R_mu((p^2,1]) = 0`;
   - for every `q < p^2`, `R_mu((q,1]) > 0`.

   Hence `p = sqrt(max supp R_mu)`.  The lower edge `rho_mu` is the squared point mass times the
   least fidelity attained on the compact projective phase hull; it records phase relations and
   destructive-interference capacity.  This differs from Wiener mean
   `mean(R_mu) = sum_j w_j^2`: full distribution recovers `l1` atomic mass, while first moment
   recovers `l2` collision mass.

3. **Finite-horizon no-uniform-inference conjecture.**  For every finite `T > 0` and
   `0 < eps < 1`, there is an atomless probability energy law `nu` such that

   `|charFun nu t|^2 > 1 - eps` for every `|t| <= T`,

   while `R_nu = delta_0`.  The one-level pure-point law has fidelity identically one and
   stationary law `delta_1`.  Therefore finite-window survival data cannot uniformly distinguish
   pure-point mass zero from one, even though completed stationary law separates them maximally.

### Universal shadow

- Quantum spectral theory: total projection of initial state onto bound-state/pure-point sector.
- Harmonic analysis: Eberlein decomposition of Fourier--Stieltjes transform into almost-periodic
  and mean-square-null parts.
- Localization: exact asymptotic order parameter independent of absolutely-continuous versus
  singular-continuous subdivision.
- Inference: sharp separation between identifiability from completed distribution and absence of
  uniform finite-horizon identifiability.

### Compression target

The law should compress four existing theorem families into one statement:

1. stationary recurrence completion for arbitrary probability spectra;
2. point-spectrum scaling of every stationary fidelity moment and full law;
3. atomless stationary collapse;
4. finite-record non-identifiability.

### Risky consequences

- Two spectra can agree arbitrarily well on an arbitrarily long survival record while their
  stationary laws have disjoint supports `{0}` and `{1}`.
- Every completed return law has connected support even when its energy spectrum is infinite,
  highly degenerate, or has arbitrary rational relations.
- Total localized/bound-state weight is encoded by an extreme statistic of completed recurrence,
  not by mean return or an inverse participation ratio.
- No model-free experimental confidence interval for pure-point mass can depend only on a finite
  survival horizon; quantitative inference requires extra spectral regularity.

### Falsifiers

The conjecture fails if any of following occurs.

1. Normalized nonzero pure-point stationary fidelity law omits every neighborhood of fidelity one.
2. Continuous spectral contribution gives positive stationary mass above `p^2`.
3. A uniform finite-window estimator separates atomless and one-point spectra without spectral
   regularity.

## Corpus frontier

- `RHTower.stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum` already proves full
  point-spectrum scaling.  This is not new.
- `RHTower.stationarySpectralReturnProbabilityMeasure_eq_zero_of_noAtoms` already proves atomless
  collapse.  This is not new.
- Corpus search found no theorem identifying the complete stationary support as one interval or
  its right edge with squared total point mass.
- Corpus already contains stronger finite-horizon non-identifiability results than the proposed
  Gaussian witness, including finite positive spectra with nearly identical pre-return records and
  incompatible completed recurrence, and finite-horizon indistinguishability of temporal
  dimension.  Finite-horizon impossibility is therefore an existing component to be compressed,
  not a new claim of this card.
- `HTGeometry.CompactGroupAlmostPeriodic` supplies relative density of compact-flow returns.
- `RHTower.SummablePurePointSurvivalEscapeReturnLaw` supplies countable pure-point recurrence but
  not yet the stationary support-edge statement.
- `HTGeometry.SummableSpectrumScrewDistribution` proves that every summable screw observable has a
  limiting law with support exactly `[0,M]`, without simplicity or rational independence.  This is
  the decisive bridge: pure-point survival deficit is a screw observable on the ordered-pair gap
  spectrum.

## External frontier audit

- Wiener formula and Eberlein's 1955 theorem identify mean squared Fourier--Stieltjes transform
  with sum of squared atom masses.  They therefore recover `sum_j w_j^2`, not directly
  `(sum_j w_j)^2` as support edge of full survival-fidelity distribution.
- RAGE separates continuous and pure-point spectral subspaces through time-averaged compact
  observables.
- Aloisio--Carvalho--de Oliveira--Santana, *Slow dynamics for self-adjoint semigroups and unitary
  evolution groups*, JMAA 2024, DOI `10.1016/j.jmaa.2024.128236`, proves arbitrarily slow averaged
  return decay for continuous-spectrum unitary dynamics.
- Searches targeted `stationary survival distribution`, `support supremum`, `pure point mass`,
  `bound-state weight`, `Wiener`, `Eberlein`, `RAGE`, `finite-time distinction`, and
  `arbitrarily slow quantum return`.  No primary source was found stating exact support-edge
  inversion plus finite-horizon impossibility as one law.  This is absence evidence, not priority
  proof.

## Conjecture loop

### C0 -- stationary law depends only on point spectrum

**Status:** killed as new.  Already formalized by exact point-spectrum scaling theorem.

**Positive survivor:** invert scaling from stationary law itself by identifying its sharp support
edge.

### C1 -- mean stationary return determines total point mass

**Status:** false.  Mean is `sum_j w_j^2`; different atomic packets can have same collision mass
and different total point mass.

**Positive survivor:** use full law's right support edge, where simultaneous approximate recurrence
should force normalized pure-point fidelity arbitrarily close to one with positive stationary
mass.

### C2 -- support edge and no-uniform finite-horizon inference

**Status:** strengthened and split.  Finite-horizon impossibility already exists in stronger corpus
forms.  The genuinely open survivor is the no-gap stationary support law and its exact upper-edge
inverse.

### C3 -- stationary support is a single interval with upper edge `p^2`

**Status:** dependency-closed paper proof and Lean formalization complete.

**Frozen proof route:**

1. First take a probability energy law carried by a countable set `F`.  Index its atoms by
   `i : F`, set `w_i = mu({E_i})`, and form the ordered-pair packet

   `a_(i,j) = w_i w_j`, `Omega_(i,j) = E_i - E_j`.

   Countable carriedness gives `sum_i w_i = 1`; hence `a` is nonnegative, summable, and has total
   mass one.

2. Absolute convergence permits expansion of the survival amplitude.  The infinite Hilbert
   dispersion identity, applied to unit phases `exp(i t E_i)`, gives the exact identity

   `1 - |sum_i w_i exp(i t E_i)|^2
      = sum_(i,j) a_(i,j) (1 - cos(Omega_(i,j) t))`.

   Thus pure-point survival deficit is exactly a summable screw series, not merely bounded by one.

3. The relation hull of the gap flow is compact and connected because it is the closure of the
   continuous image of `R`.  The screw observable is continuous, nonnegative, and zero at the
   identity.  Its image is therefore exactly `[0,M_mu]`.  Full-support Haar measure on the hull,
   pushed through the screw observable, has support exactly this interval.

4. Centered uniform time sampling converges to that Haar pushforward.  Composing with the affine
   reflection `d |-> 1-d` and using the identity in step 2 identifies the canonical stationary
   survival law.  Therefore a countably carried probability spectrum has

   `supp R_mu = [1-M_mu, 1]`.

   The identity also forces `M_mu <= 1`, so this is an interval inside the physical fidelity
   carrier.

5. For arbitrary probability `mu`, let `p` be total point-spectrum mass.  Existing point-spectrum
   scaling gives `R_mu = (x |-> p^2 x)_* R_nu`, where `nu` is normalized point spectrum.  If
   `p=0`, existing atomless collapse gives `supp R_mu={0}`.  If `p>0`, `nu` is countably carried,
   so step 4 and injectivity of positive scaling give

   `supp R_mu = [p^2(1-M_nu), p^2]`.

   Both branches are one interval, and the right endpoint is unconditionally `p^2`.

6. Consequently `p = sqrt(sup supp R_mu)`.  Wiener--Eberlein's first stationary moment remains
   `sum_j w_j^2`; the new inverse uses the full law's support, not its mean.

**Dependency check:** every invoked object exists for an arbitrary probability measure; countable
carriedness is proved for normalized point spectrum and is not an added physical hypothesis.
Frequency simplicity, rational independence, finite support, decay, locality, and genericity are
not used.

## Proof obligations

1. **Closed.** Formalize exact ordered-pair screw identity for a countably carried probability spectrum.
2. **Closed.** Identify its canonical stationary law with affine reflection of `screwValueLaw`; transport the
   exact support theorem to `[1-M,1]`.
3. **Closed.** Prove normalized point spectrum is countably carried whenever point mass is nonzero.
4. **Closed.** Push interval support through exact scale map `x |-> p^2 x`, including `p = 0` by case split.
5. **Closed.** Package no-gap support, exact upper edge, maximum property, and inverse square-root law in one capstone.
6. Reuse existing stronger finite-horizon no-go theorems in manuscript synthesis; do not spend a
   novelty claim on the weaker Gaussian witness unless it materially simplifies exposition.

## Formal artifacts and audit

- Module: `GaloisForLFunctions.RHTower.StationaryRecurrenceSupportIntervalLaw`.
- Closed capstone:
  `RHTower.universalStationaryRecurrenceNoGapBoundStateMassLaw`.
- Countably carried support law:
  `RHTower.stationarySpectralReturnProbabilityMeasure_support_of_countablyCarried`.
- Arbitrary-spectrum interval law:
  `RHTower.exists_stationarySpectralReturnProbabilityMeasure_support_Icc`.
- Exact maximum and inverse:
  `RHTower.pointSpectrumFidelityScale_one_is_stationarySupportMaximum` and
  `RHTower.pointSpectrumMassReal_eq_sqrt_stationarySupportEdge`.
- `lake env lean GaloisForLFunctions/RHTower/StationaryRecurrenceSupportIntervalLaw.lean` passes
  without warnings.
- Targeted `lake build GaloisForLFunctions.RHTower.StationaryRecurrenceSupportIntervalLaw` passes.
- Axiom audit of nine load-bearing declarations reports only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axioms or placeholders.
- Module is imported by `GaloisForLFunctions.RHTower`.  No umbrella build was run.
- Project lint finds no defect in this module; it still reports unrelated un-wired modules created
  elsewhere in dirty shared worktree.

## Lean discipline

- Final capstone quantifies over every probability energy measure; no spectral regularity premise.
- Positivity conditions on requested horizon/resolution are quantified inputs, not scientific
  assumptions.
- No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.
- Check with foreground `lake env lean <file>`; final audit only targeted
  `lake build <module>`; wire module into `RHTower.lean` without building umbrella.
