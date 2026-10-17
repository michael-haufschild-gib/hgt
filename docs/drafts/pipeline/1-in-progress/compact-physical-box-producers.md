# Compact logarithmic states from compensated physical producers

- **ID:** compact-physical-box-producers
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** continuum-coprime-shear; physical-box-average-affine-regularity
- **Statement:** Construct compact logarithmic primitive states from arbitrary physical velocities using interval truncation, explicit zero-integral compensation and box smoothing, with quantitative errors and compact-source graph convergence.

## Goal

The physical box producer has an actual continuous representative and L²
derivative, but its output need not have compact support. A further obstacle
is coordinate-specific: even a compact physical velocity can have nonzero
total integral, leaving a constant tail in F_q(exp x). Compact physical
velocity alone therefore does not supply a compact logarithmic state.

For n∈ℕ put r=n+1, α=exp(−r), β=exp(r), L=exp(2r), h=exp(−2r).
Let P₊q denote actual restriction to the positive half-line. Propose

    m_n=∫_α^β q,
    v_n=1_[α,β]q−(m_n/L)1_[β,β+L],
    w_n=M_(−2r)v_n,
    f_n(x)=F_(w_n)(exp x).

The explicit compensator should have L² norm at most exp(−r/2)‖q‖ and
cancel the total integral. Since α−h>0, smoothing should leave w_n supported
in [α−h,β+L], with zero integral. This should construct f_n as an actual
compact C¹ logarithmic state, with the correct weighted Dirichlet velocity.

Target quantitative approximation:

    ‖w_n−P₊q‖ ≤ ‖1_(0,α)q‖ + ‖1_(β,∞)q‖
                 +exp(−r/2)‖q‖+‖M_(−2r)(P₊q)−P₊q‖.

Every term should tend to zero. Negative-half-line velocity is invisible to
the logarithmic primitive; prove that exact nullspace statement when
transferring convergence to jumpEnergy(w_n−q) for every compact source.
Transfer the explicit affine producer bound using
‖v_n‖≤(1+exp(−r/2))‖q‖. The target closes a field source/energy approximation
gap, not merely a renamed cutoff-density theorem. No claim of approximating
the negative physical component by positive-supported velocities.

## Gates

- [x] Initial corpus audit and exact source-text search.
- [x] Reaudit applicable source declarations and primary parent theories.
- [x] Complete paper proof of actual restrictions, compensator, preservation
  of zero integral under smoothing, compact logarithmic support, derivative,
  all limits and graph coupling.
- [ ] Formalize only the audited theorem; serial leaf checks, all-public
  axiom audit, principal/API checks, umbrella/index/lint review.

## Corpus evidence and boundaries

Query `physical compact regularization cutoff box average derivative graph
core`, BiScaleUncertainty filter, --any,60-second budget. All20 candidate
statements and20 source-argument statements inspected. Existing parents
include compact-source graph admission/coercivity, annular source averages,
rough logarithmic derivatives and current physical box drafts. Those drafts
are not independent certification. No proof ideas or ingredient sets returned.
partial=true; deadline/reranking unfinished, generation1447717 pending,
refresh incomplete/background indexer. Evidence:
/tmp/physical-box-next-search.json. No absence or external novelty claim.

Second query: `compact logarithmic primitive zero total integral compensating
tail physical velocity`. All20 candidate and20 source-argument statements
inspected, including negativePhysicalVelocity, its exact norm/orthogonality,
actual logarithmic primitives and weighted derivatives. No proof ideas or
ingredient sets. partial=true, deadline/semantic coverage incomplete;
inventory73830 complete, coverage snapshot1447809/current1447810 older than
the live generation, retrieval generation1447801; compiler mostly pending
or source-only, refresh incomplete. Result path:
/tmp/compact-log-primitive-next-search.json. No absence conclusion.

Useful proof mechanism to audit: the exact primitive formula for M_s may
prove vanishing tails directly. Since h<α, the second primitive at h is zero;
the zero-integral compensator makes the original primitive zero above β+L.
This could avoid a separate global Fubini argument for compact support.

Unproved and uncounted; no Lean assigned. The physical box package is now
certified as contribution19/100. Remain on continuum coprime shear. Do not infer
full uncut SourceGraph closure, completed divisor-domain preservation, or
operator-norm convergence from this proposed local approximation. No RH
work, numerical experiments, analytic admission premises, or pre-floor
counterterm subtraction. Field README remains read-only.

## Active proof scope

Previous goal turn classified as progress: package19 current artifact check
passed at this turn's initialization. Attachment and all260 README lines
read; README remains read-only. Relevant Serena memory read, architecture
and testing docs remain absent. No subagents; update_plan unavailable, this
card records the plan. Certified count remains19/100.

Prove the entire proposed producer construction, plus an explicit bound for
source mass so convergence controls source mass and jump energy together.
Use K(ψ)=∫ψ(x)²exp(x)dx and the unconditional primitive bound
|F_q(exp x)|²≤exp(x)‖q‖² to bound sourceMass(ψ,q,0) by K(ψ)‖q‖².
Approximate zero-anchored states F_q(exp x); do not claim global physical
energy approximation of arbitrary added constants. Complete paper proof
before field Lean; then serial leaf, axiom, API, umbrella, catalog and lint
audits. No new field Lean is written yet.

Current semantic query returned no candidates or source arguments;
partial=true, deadline/vector-statement unfinished, generation1447962
pending, refresh incomplete. Broadened to lexical exact existing objects.
No absence inference. Evidence /tmp/compact-physical-current-search.json.

Dependency-closed paper proof now written before field Lean:
docs/reports/BiScaleUncertainty/CompactLogarithmicPhysicalProducers.md.
It includes exact compensator energy m_n²/L, orthogonal compensated energy,
the stronger norm factor sqrt(1+exp(−r)), explicit compact C¹ source and
weighted derivative, visible-component approximation, affine bounds, and
the whole compact source-mass-plus-jump form estimate and convergence.
The input remains an arbitrary actual physical L² vector; no added analytic
admission premise. Count remains19/100 until formal certification.

Lexical query returned14 declarations (36 total lexical matches under the
default per-module cap), no candidate/source-argument sections or semantic
coverage metadata. All14 returned declarations inspected; applicable source
definitions read. Existing negativePhysicalVelocity, primitive/box APIs,
sourceMass and compact jump bounds are parents. Online mathlib indicator
docs and Demkowicz translation/regularization arguments inspected; local
source governs API signatures. No absence or external novelty claim.
