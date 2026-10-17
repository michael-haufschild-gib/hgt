# Actual box averaging and quantitative affine regularity

- **ID:** physical-box-average-affine-regularity
- **Stage:** 0-backlog
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
- [ ] Primary-source audit and complete paper proof, including actual L²
  membership, joint measurability, finite variance integrals and derivative.
- [ ] Formalize the exact paper theorem, with serial direct leaf checks,
  all-public axiom audit, principal signatures, umbrella/index/lint review.
- [ ] Identify how the constructed range couples to the established
  primitive/compact-source graph calculus without importing admission premises.

Use Jensen/Fubini for membership and variance, endpoint differences for the
derivative, and the exact L¹ difference of translated interval kernels for
the commutator bound. These are proposed mechanisms, not completed proofs.
Classical Steklov averages and convolution are parent theories. Contribution
must be the actual field operator/producer/defect coupling, not a renamed
classical inequality. No Lean file assigned; uncounted.

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
