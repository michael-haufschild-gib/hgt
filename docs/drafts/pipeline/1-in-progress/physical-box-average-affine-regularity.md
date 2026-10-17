# Actual box averaging and quantitative affine regularity

- **ID:** physical-box-average-affine-regularity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** continuum-coprime-shear; physical-affine-commutator-producers
- **Statement:** Construct physical L² box averages with exact variance loss, actual derivative, and an unconditional affine commutator bound that vanishes with the gap.

## Goal

The full-space affine commutator has maximal norm at every nonzero gap.
Seek an explicit producer of regular velocities that restores small-gap
control without assuming Sobolev membership, translation regularity, or
an integral estimate. For s∈ℝ put h=exp(s)>0 and propose

    M_s q(t) = (F_q(t+h)−F_q(t))/h,
    D_s q = (τ_h q−q)/h.

Construct M_s as an actual bounded operator on physical L² and prove that
its displayed representative has actual almost-everywhere derivative D_s q.
Target contraction and exact positive variance identity:

    ‖M_s q‖ ≤ ‖q‖,
    ‖q‖²−‖M_s q‖²
      = (1/(2h²)) ∫₀ʰ∫₀ʰ ‖τ_u q−τ_v q‖² du dv.

For C_(a,b)=A_aτ_b−τ_bA_a, seek the unconditional producer estimate

    ‖C_(a,b)(M_s q)‖
      ≤ 2√|a| min(1, |b(a−1)|/h) ‖q‖.

All inputs are arbitrary real parameters and actual physical L² states.
The positive smoothing scale is constructed, not an analytic admission
premise. Audit the constants and all signs on paper before Lean. Also
investigate strong approximation M_s q→q as s→−∞; do not assert operator
norm convergence or regularity for unrestricted unsmoothed states.

## Approach and gates

- [x] Initial corpus query and existing compact-source averaging inspected.
- [x] Primary-source audit and complete paper proof, including actual L²
  membership, joint measurability, finite variance integrals and derivative.
- [ ] Formalize the exact paper theorem, with serial direct leaf checks,
  all-public axiom audit, principal signatures, umbrella/index/lint review.
- [x] Identify how the constructed range couples to the established
  primitive/compact-source graph calculus without importing admission premises.

Use norm-continuous Bochner orbits for membership, inner-product functionals
for variance, endpoint differences for the derivative, and oriented interval
cancellation for the commutator bound. The paper proves these mechanisms.
Classical Steklov averages and convolution are parent theories. Contribution
is the actual field operator/producer/defect coupling. Six leaves assigned
below; uncounted until formal certification.

## Corpus evidence and limits

Query `physical box average Steklov smoothing translation regularity
commutator`, BiScaleUncertainty filter, --any,60-second budget. All20
candidate statements and20 source-argument statements inspected; no proof
ideas or ingredient sets returned. Own package18 drafts were indexed during
checking and do not constitute independent certification. Other hits include
continuous primitive commutator resistance bounds, compact-source translated
Gram packets and annular source regularity. The actual sources
AnnularCorrelationSource.lean and AnnularSourceRegularity.lean were read:
they already construct compact continuous averages, their C¹ derivatives,
energy contraction and exact source remainder. Reuse their mathematical
lessons; the proposed general physical L² operator is a separate obligation.

Search partial=true; text/source retrieval interrupted, deadline/reranking
unfinished, generation1447449 pending, refresh incomplete/background indexer.
Evidence: /tmp/physical-affine-next-search.json. No absence or external
novelty conclusion. Reaudit before selecting the formal scope.

## Boundaries

Remain on continuum coprime shear and additive/multiplicative regularity.
Full physical translations do not imply half-line invertibility or completed
divisor-domain invariance. No RH task, numerical experiment, added axiom,
receiver-only equivalence, or pre-floor counterterm subtraction. Trap10
requires actual producers and unconditional errors. Field README is read-only.


## Active proof scope

Dependency-closed paper proof completed before field Lean code:
docs/reports/BiScaleUncertainty/PhysicalBoxAverageAffineRegularity.md.
Use the strongly continuous L² translation orbit and Bochner interval
averages. Exact interval cancellation replaces the proposed kernel-L¹
argument; it gives the same coefficient for arbitrary real gaps. Include
actual continuous representative, a.e. derivative and strong orbit derivative,
one- and two-fold variance losses, strong approximation and compact graph
commutator energy control. Six planned leaves: PhysicalTranslationContinuity,
PhysicalBoxAverage, PhysicalBoxProfile, PhysicalBoxVariance,
PhysicalBoxAffineRegularity, PhysicalBoxGraphControl. No certified increment
until serial leaves, axioms, API, umbrella, index and lint gates. Count18/100.

Current query all20 candidates inspected; no source arguments or ideas.
partial=true, text/source interrupted, deadline/vector-proof incomplete,
generation1447551 pending, refresh incomplete. Primary mathlib continuous
pullback and Demkowicz Energy Spaces references inspected and linked in paper.
No absence or external novelty claim. update_plan unavailable; this card
records the plan. No subagents authorized or used.

All six planned leaves are written. PhysicalTranslationContinuity,
PhysicalBoxAverage, PhysicalBoxProfile, PhysicalBoxVariance and
PhysicalBoxAffineRegularity pass serial direct checks without diagnostics.
PhysicalBoxGraphControl is checking in owned session94354; no second owned
Lean process. All-public audit and integration gates are pending. Correct MemLp congruence API is
MemLp.ae_eq; final combined audit includes it. No certified increment.

Next uncounted conjecture is recorded in
../0-backlog/compact-physical-box-producers.md: actual compact logarithmic
states require a zero-integral compensator, not just compact velocity.
Two corpus queries inspected all20 candidates and20 source statements each;
the candidate card records partial coverage and exact proposed bounds.
