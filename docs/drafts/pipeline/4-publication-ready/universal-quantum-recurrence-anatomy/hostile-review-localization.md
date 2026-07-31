# Hostile review: localization--recurrence law

**Editorial posture:** Nature desk review, presumption against publication  
**Date:** 2026-07-31  
**Material reviewed:** theorem blueprint, claim trace, formal theorem cards,
and current Anderson/MBL priority audit

## Decision

**Reject in present form.**

The package now contains a coherent exact recurrence--locality law, an
all-time finite fixed-hopping separation theorem, an infinite same-field
fixed-time/all-time quantifier separation, and a same-boundary
dimension--mass budget. It still does not show that the law controls a
recognized microscopic localized material, produces a robust finite-time
observation, or resolves an open question at Nature's required breadth.

## Anderson-merger update

The manuscript now contains a direct localization-to-recurrence theorem,
not merely a coexistence construction.  Exponential decay of the spectral
weight seen at one site and controlled shell growth imply
\[
 n\le(Q+1)^{|S_R|-1},\qquad
 1-S_x(n)\le
 4\beta_R+2\left(\frac{2\pi}{Q+1}\right)^2 .
\]
Thus the guaranteed local return exponent is set by localization volume
rather than ambient spectral dimension.  A countably infinite pure-point
version replaces the discarded complement by a certified summable-tail
error and retains the finite visible-head exponent.  Both have a
non-vacuous never-exits/post-exit-return form.

This is the strongest honest Anderson merger in the current corpus.  It is
still a deterministic interface: the paper does not prove the localization
certificate for a named random ensemble.  The recurrence step is a sharp
composition of localization tails with finite-dimensional phase
synchronization, but its ingredients are classical enough that priority and
breadth remain unearned.

The finite onsite-plus-hopping theorem is now all-time, not finite-horizon:
for every finite Hermitian hopping matrix and every positive off-diagonal
spatial envelope, one onsite potential produces maximal projective spectral
rank while every transition amplitude remains below the assigned envelope
for every real time. The same phase flow is Haar on the full projective
torus. This eliminates the objection that exact spatial--recurrence
separation is only an artefact of a diagonal l-bit model.

The infinite theorem gives the more informative classification. In one
explicit absolutely summable interacting l-bit field,
\[
 \|[\tau_t(X_x),X_y]\|
 \le \min\{2,4K|t|2^{-|x-y|}\}
\]
for every fixed time, while
\[
 \sup_t\|[\tau_t(X_x),X_y]\|_{\mathrm{op}}=2
 \qquad(x\ne y).
\]
The explicit saturation time obeys
\[
 2\le4Kt_{xy}2^{-|x-y|}.
\]
Thus every distance is exponentially delayed but no pair is permanently
isolated. This sharply separates fixed-time quasi-locality from the
time-uniform spatial decay defining Anderson dynamical localization.

The same field also closes the former disjoint-packet defect. Crossing one
boundary doubles exact local-flip recurrence dimension from \(D\) to
\(2D\), and the identical \(D\) new coefficients obey
\[
 2D\sum_S|b_S|\le K,\qquad
 2D\delta N_\delta\le K.
\]
Complete coefficient-level resolution forces \(2\delta D^2\le K\).

These results do not change the editorial decision. The finite Anderson
construction is existential, near the atomic limit and not volume-uniform.
The infinite field is deliberately engineered, origin-dependent and acts
on continuous amplitudes in the uniform norm rather than a selected
microscopic Hilbert-space model. Its qualitative log-cone and spectral-tree
physics already exists in the literature. Current classification remains
`[BRIDGE]` with one potentially new exact boundary law, not a validated
headline discovery.

## What is new enough to retain

The exact theorem spine is:

\[
  \tau(H_J)=
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{J_S:S\ne\varnothing\},
  \qquad
  \tau(H_J)+\operatorname{rank}_{\mathbb Q}
  L_{E_J}^{\mathrm{proj}}=2^N-1.
\]

Its strongest synthesis is a separation principle:

> Zero off-diagonal configuration transport does not bound projective
> recurrence rank.

Within exactly diagonal l-bit dynamics, the noninteracting one-body
endpoint has rank \(N\), finite commuting range \(R\) has an
\(O(N2^R)\) ceiling, and absolutely summable all-range tails can attain the
finite-window maximum \(2^N-1\). Exact spatial symmetry is an obstruction:
a coefficient-preserving permutation that moves a support prevents maximal
rank.

The spectral-jet theorem adds an exact resolution law:

\[
  \tau_r=\sum_{m<r}\operatorname{rank}_{\mathbb Q}
  \{J_S:w(S)=m\}.
\]

This is mathematically stronger than a bare ultimate-rank statement. It
still concerns jet resolution, not elapsed laboratory time.

The infinite extension adds two exact results worth retaining:

1. fixed-time exponential locality coexists with exact all-pairs eventual
   commutator saturation;
2. the boundary packet that doubles recurrence dimension is exactly the
   packet charged to the locality mass, giving the quadratic full-resolution
   law \(2\delta D^2\le K\).

The first is a sharp form of qualitatively known interacting l-bit
propagation. External novelty of the second is not yet established.

## Desk-reject objections

1. **Model scope.** The central theorem is for an exactly diagonal l-bit
   fixed point. No result transfers it to a standard random-field XXZ,
   Anderson--Hubbard, or other microscopic Hamiltonian throughout a
   rigorous localized regime.

2. **Priority collision.** Interaction-induced dephasing, suppressed
   localized revivals, logarithmic activation scales and growth of
   effective frequencies are established MBL themes. The paper must claim
   only its exact relation-lattice and layer-rank classification.

3. **Operational discontinuity.** Exact rational rank can jump under an
   arbitrarily small irrational perturbation and cannot be certified by
   finite noisy data. The spectral-jet law does not by itself provide a
   stable experimental invariant.

4. **Finite-time generality.** An exact elapsed-time wall crossing is now
   proved for the ideal monomially scaled l-bit family. No theorem yet gives
   uniform finite-coupling remainder bounds for a general analytic or
   microscopic localized family.

5. **Microscopic state preparation.** The uniform l-bit product state now
   provably sees every gap direction, but the physical preparation is
   unknown when the microscopic l-bit dressing unitary is unknown.

6. **Measurement cost.** Full-cube Walsh isolation has replica height
   \(2^{N-1}\). The ideal calibrated separation theorem is not a
   device-feasibility or noise-robustness result.

7. **Infinite-system scope.** The countable construction gives continuous
   energy and a strongly continuous isometric multiplication group on
   \(C(X)\), plus exact all-pairs saturation in its induced uniform norm. It
   is not a Hilbert-space unitary, quasi-local \(C^*\)-dynamics, GNS
   construction, or global recurrence theorem. Its envelope is explicitly
   origin-dependent.

8. **Conceptual threshold.** Walsh inversion plus rank--nullity may be
   judged elegant repackaging. Exact all-pairs saturation strengthens the
   package, but local constants of motion were already known to imply
   arbitrary-distance information propagation. The paper still needs a
   consequence inaccessible to established dephasing, OTOC, spectral-tree
   or spectral-statistics methods.

9. **Threshold interpretation.** The quadratic boundary law is stated in
   terms of coefficient magnitude. No theorem equates that threshold to
   laboratory resolvability under finite time, noise and constrained
   observables.

## Claims that cause immediate rejection

- “Anderson localization has exponential recurrence rank.”
- “Generic MBL systems attain maximal recurrence rank.”
- “Time has observer-dependent dimension.”
- “The rank staircase is observed as laboratory time increases.”
- “The infinite construction is a thermodynamic-limit Hilbert-space
  quantum unitary.”
- “Fixed-time exponential locality is Anderson localization.”
- “Every interacting localized material eventually reaches maximal
  all-pairs influence.”
- “The full-cube response is a scalable tomography protocol.”
- “Localization freezes all information transport.”
- Any black-hole, cosmology, arrow-of-time or fundamental-observer claim
  derived only by analogy.

## Minimum promotion gate

Send to external review only after all four requirements below are met:

1. **Microscopic or engineered physical realization:** either a theorem for
   a recognized disordered Hamiltonian in a proved localized regime or an
   explicit engineered commuting platform with honest simulator scope.

2. **Finite-time operational theorem:** extend the exact monomial support
   response to a bounded-height/resolution invariant with explicit
   finite-\(g\), finite-\(T\), detuning, remainder and measurement errors.

3. **Physical state-observable realization:** translate the proved uniform
   l-bit product-state result through a known microscopic dressing and
   specify a measurable return observable.

4. **Priority and feasibility audit:** comparison with l-bit dephasing,
   Loschmidt echo, DEER/Ramsey, Hamiltonian learning and polyspectral
   methods, including measurement scaling and device noise.

## Current honest headline

**Exponential quasi-locality permits maximal eventual influence and
recurrence rank**

Public-language form:

> Quantum influence can be exponentially delayed across every distance
> without being permanently stopped, while each resolved boundary doubles
> the number of phases governing return.

This headline is defensible only for the explicit exactly diagonal l-bit
field and its uniform-norm dynamics. It is not yet a Nature-level claim
about Anderson-localized matter.
