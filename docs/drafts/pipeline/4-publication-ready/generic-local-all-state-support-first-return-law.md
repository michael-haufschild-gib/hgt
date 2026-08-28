# Generic local all-state support first-return law

- **ID:** `generic-local-all-state-support-first-return-law`
- **Stage:** 4-publication-ready
- **Type:** THEOREM (paper) / LOCAL MANY-BODY RECURRENCE / STATE-SUPPORT STRATIFICATION
- **Date:** 2026-08-28
- **Status:** `[LITERATURE-FIRST] [PAPER-PROVED] [LEAN-CLOSED] [TARGETED BUILD PASSED] [AXIOM-AUDITED] [PUBLICATION-INTEGRATED] [PDF-VERIFIED]`

## Goal

Close the cyclic-state loophole in the generic nearest-neighbour physical first-return theorem.
The desired theorem must classify every normalized initial state for one common conull set of
static local Hamiltonians, rather than choose a new exceptional set after the state is chosen.

## Gates

- [x] 0 → 1 in-progress: well-posed, corpus gap confirmed, literature frontier checked first
- [x] 1 → 2 fully-proven: complete dependency-closed paper proof below
- [x] 2 → 3 formalized: unconditional closed Lean capstone, targeted source/build and axiom audit
- [x] 3 → 4 publication-ready: theorem, proof, experiment and exact priority boundary integrated;
  final PDF compiled and affected pages visually verified

## Public sentence

For a typical static nearest-neighbour quantum chain, the long-time price of returning is fixed not
by total Hilbert-space dimension but exactly by how many energy levels the prepared state actually
occupies—and one Hamiltonian obeys that rule for every state at once.

## Theorem

Let `n,q >= 2`, `D=q^n`, and let `V_{n,q}` be the full real coefficient space of arbitrary
Hermitian onsite terms and arbitrary Hermitian nearest-neighbour two-site terms on the open
`n`-site `q`-level path.  Fix any nonempty preconnected open subset `U` of the simple-spectrum
locus.  There is a conull subset `G_U` of `U` such that the following holds simultaneously for
every `H in G_U`, every normalized pure state `psi`, and every cutoff `t0>0`.

Write `phi_1,...,phi_D` for an energy eigenbasis ordered by increasing energy and define the exact
spectral support

\[
 S_H(\psi)=\{j:\langle\phi_j,\psi\rangle\ne0\},\qquad
 s_H(\psi)=|S_H(\psi)|.
\]

For the physical survival-fidelity first return

\[
 T_{H,\psi}(\delta)=\inf\{t\ge t_0:
 1-|\langle\psi,e^{-itH}\psi\rangle|^2<\delta\},
\]

one has

\[
 \boxed{
 \lim_{\delta\downarrow0}
 \frac{\log T_{H,\psi}(\delta)}{\log(1/\delta)}
 =\frac{\max\{s_H(\psi)-2,0\}}2.}
\]

Thus eigenstates and two-level superpositions have exponent zero, while every state occupying
`s>=3` distinct eigenlevels has exact fidelity-deficit exponent `(s-2)/2`.  The exceptional
Hamiltonian set is independent of the state, its weights and the cutoff.

## Proof

### 1. One common Diophantine-good set for every support

On `U`, write the ordered simple eigenvalues as

\[
 E_1(H)<\cdots<E_D(H).
\]

Fix `s` with `3<=s<=D` and an increasing injection
`j:{1,...,s}->{1,...,D}`.  Use `E_{j(1)}` as phase anchor and
`E_{j(2)}-E_{j(1)}` as physical clock.  The selected projective gap-ratio map is

\[
 R_j(H)=\left(
 \frac{E_{j(k)}(H)-E_{j(1)}(H)}
      {E_{j(2)}(H)-E_{j(1)}(H)}
 \right)_{k=3}^{s}\in\mathbb R^{s-2}.
\]

The full onsite-plus-edge path family escapes every nonzero balanced real spectral relation.
Consequently no nontrivial real affine combination of coordinates of `R_j` is constant on `U`.
The ordered spectrum and hence `R_j` are analytic on `U`; the denominator is nonzero because the
spectrum is simple.  Kleinbock--Margulis extremality therefore gives

\[
 \operatorname{vol}\{H\in U:R_j(H)\text{ is very well approximable}\}=0.
\]

There are only finitely many pairs `(s,j)`.  Remove the finite union of their null exceptional
sets.  The complement `G_U` is conull, and every selected support of every size at least three is
simultaneously non-very-well-approximable for every `H in G_U`.  This finite-support reduction is
why an uncountable quantifier over states costs only a finite intersection over spectral supports.

### 2. Spectral support compression is exact

Fix `H in G_U` and a normalized state `psi`.  Put

\[
 p_j=|\langle\phi_j,\psi\rangle|^2.
\]

Parseval gives `p_j>=0` and `sum_j p_j=1`, so support `S=S_H(psi)` is nonempty.  Spectral
decomposition gives the exact identity

\[
 1-|\langle\psi,e^{-itH}\psi\rangle|^2
 =1-\left|\sum_{j\in S}p_j e^{-itE_j(H)}\right|^2.
\]

After increasing enumeration of `S`, retained weights are strictly positive and still sum to one.
Zero-weight levels disappear identically; this is equality of the complete return function, not an
approximation or effective-support estimate.

### 3. Supports of size at least three

Suppose `s=|S|>=3`.  The selected ratio vector belongs to the simultaneous good set from Step 1.
Dirichlet approximation gives the upper first-return exponent `s-2` in phase radius.  Non-very-
well-approximability gives the matching lower exponent.  Because survival-fidelity deficit is
quadratic in projective phase displacement and every retained weight is positive, the physical
fidelity-deficit exponent is exactly half the phase-radius exponent:

\[
 \lim_{\delta\downarrow0}
 \frac{\log T_{H,\psi}(\delta)}{\log(1/\delta)}=\frac{s-2}{2}.
\]

Weight values affect finite multiplicative constants but not the logarithmic exponent.

### 4. One- and two-level boundary strata

If `s=1`, evolution changes `psi` only by global phase.  The fidelity deficit is identically zero,
so `T_{H,psi}(delta)=t0` for every `delta>0`, and the logarithmic exponent is zero.

If `s=2`, let occupied energies be `E_a<E_b` and put
`R=2*pi/(E_b-E_a)>0`.  Every integer multiple of `R` is an exact projective return.  Choose one
multiple `mR>=t0`.  For every `delta>0`,

\[
 t_0\le T_{H,\psi}(\delta)\le mR.
\]

The numerator `log T_{H,psi}(delta)` is therefore bounded while `log(1/delta)` tends to infinity,
so the exponent is zero.  Since normalized states have nonempty support, these cases exhaust the
boundary.  Combining Steps 3 and 4 proves the displayed formula.  □

## Hostile audit

1. **Uncountably many states.** No uncountable intersection of conull sets is taken.  Recurrence
   arithmetic depends on a state only through one of finitely many exact support subsets; all
   positive weights on one support share the same exponent.
2. **Arbitrary noncontiguous support.** Each support is increasingly enumerated inside the globally
   sorted simple spectrum.  The genericity theorem accepts arbitrary distinct anchor, clock and
   tail indices; contiguity is irrelevant.
3. **Very small nonzero weights.** They may destroy uniform finite-resolution constants across
   states, but each fixed positive weight supplies a positive lower metric constant.  Claim is an
   exact asymptotic exponent, not a state-uniform deadline.
4. **Degeneracy.** Excluded explicitly by `U` being a simple-spectrum chart.  The theorem does not
   claim this stratification on spectral-collision walls.
5. **Two occupied levels.** Projective dynamics is periodic for every nonzero gap, so exponent zero
   is exact and requires no genericity.
6. **Eigenstates.** They never leave projective origin.  Positive cutoff makes first-return
   functional equal to cutoff rather than zero; exponent remains zero.
7. **Generic local versus every local Hamiltonian.** Result is conull on every open simple chart of
   full static path coefficient family.  It is not a worst-case theorem for every local model.
8. **First return versus completed density.** Proof controls actual first return after fixed
   positive cutoff.  No Kac-type inverse-density substitution is used.

## Literature frontier checked first

- Gupta--Short (2026) prove deterministic continuous-time uniform recurrence upper bounds with
  exponent controlled by number of distinct energies, simultaneously for all states.  They do not
  give a state-by-state exact lower exponent, spectral-support stratification, generic local-family
  equality or one-Hamiltonian/all-states classification.
- Kotowski--Oszmaniec (2026) prove deterministic arbitrary-state upper bounds, sharpen them by
  effective spectral support, and show lower behavior for random diagonal Hamiltonians and selected
  states.  They explicitly leave tight recurrence bounds for physical local noncommuting dynamics
  open.  They do not prove exact almost-everywhere equality for every state of one local
  Hamiltonian.
- Standard shrinking-target/Diophantine theorems supply the metric exponent of a fixed torus flow
  or analytic family.  They do not identify physical spectral support, prove spectral
  nondegeneracy for the full nearest-neighbour many-body family, or establish the simultaneous
  all-state quantum statement.

Permitted priority claim after formal closure: **exact almost-everywhere spectral-support
classification of physical survival-fidelity first-return exponents, simultaneously for every
pure state, in the full static one-dimensional onsite-plus-nearest-neighbour Hamiltonian family.**

## Formal closure

Source: `formal/GaloisForLFunctions/HTGeometry/AllStateSpectralSupportRecurrenceLaw.lean`.

- `supportIndex`, `supportEnergy`, `supportWeight`, `spectralWeightSupport`: canonical finite
  support restriction.
- `spectralReturnAmplitude_support`, `spectralReturnDeficit_support`,
  `fidelityReturnTime_support`: exact support compression.
- `hasPositiveProjectiveReturn_fin_one`, `hasPositiveProjectiveReturn_fin_two`: exact periodic
  boundary strata.
- `tendsto_log_fidelityReturnTime_supportCard`: arbitrary finite packet law.
- `ae_all_supportGapRatio_not_vwa`: one finite-intersection conull event for every support.
- `ae_tendsto_log_orbitFidelityReturnTime_supportCard_sortedSpectrum`: all normalized physical
  states simultaneously on an escaping Hermitian chart.
- `quditPathAllStateSupportRecurrenceLaw_of_two_le`: full local path coefficient family.
- `universalQuditPathAllStateSupportRecurrenceLaw`: unconditional shifted-parameter capstone.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/AllStateSpectralSupportRecurrenceLaw.lean` passed
  without warnings.
- `lake build GaloisForLFunctions.HTGeometry.AllStateSpectralSupportRecurrenceLaw` passed.
- Scratch `#print axioms` for packet, conull, physical-chart, local-path and unconditional
  capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Source contains no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration.
- Module imported by `GaloisForLFunctions.HTGeometry`; no full umbrella build run.

## Log

- 2026-08-28 — corpus audit identified exact cyclic-state frontier and reusable selected-gap
  infrastructure.
- 2026-08-28 — primary literature checked before proof; no matching all-state local equality found.
- 2026-08-28 — theorem survived boundary audit; dependency-closed paper proof completed.
- 2026-08-28 — unconditional Lean capstone closed, targeted source and module checks passed,
  axioms audited, and module wired into umbrella without full umbrella build.
- 2026-08-28 — central manuscript theorem upgraded from cyclic-only to all-state support law;
  abstract, public summary, proof, experiment, synthesis, literature boundary and audit ledgers
  updated; 49-page PDF compiled without reference or overflow warnings and affected pages visually
  verified.
