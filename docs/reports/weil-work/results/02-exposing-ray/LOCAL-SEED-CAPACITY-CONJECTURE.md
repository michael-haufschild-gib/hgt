# Local-seed variance completion: source-capacity audit

Status: FORMALIZED in cycle 12. See LOCAL-SEED-CAPACITY-PROOF.md and WeilWorkExposingRayLocalCapacity.lean; complete scratch and final installed leaf audits pass. The original proposal and its audit trail follow below. Generic ingredients are classical; external scientific novelty remains unestablished. Follow-up to the geometric completion gap. Main WP02 universal lower inequality and opposite-ray producer remain OPEN.

## Exact candidate

Let a=log(2)/2. For any finite family of actual C2 polar sources g_j supported in [-a,a], nonnegative real weights alpha_j with M=sum alpha_j>0, and real translations x_j, set

    F = sum_j alpha_j * g_j(.-x_j),
    R_j = M*g_j(.-x_j)-F.

Conjecture the exact lower bound

    (pi/(5*log(2)))*|paperFT(F)(0)|^2
      <= archEnergy(F)+sum_j (alpha_j/M)*archEnergy(R_j).

This is a structural statement about a fully specified completion, not an assumed energy inequality. The seeds may differ and all cross terms must remain. The same candidate bound should hold with any real frequency tau in place of zero, since the Fourier phase has unit modulus; the zero-frequency specialization is enough for the literal source application. The intended positive survivor is a source-capacity invariant of the whole local-seed variance class.

## Proposed proof and novelty gate

The exact finite variance identity, followed by integration, makes total energy equal to M*sum alpha_j*archEnergy(g_j). Translation preserves archEnergy. The C2 half-log-two bridge gives E(g_j)>=(pi/5)*integral |g_j|^2. Cauchy–Schwarz on an interval of length log(2) bounds |paperFT(g_j)(0)|^2 by log(2)*integral |g_j|^2. Weighted Cauchy–Schwarz bounds the squared zero-frequency value of F by M*sum alpha_j*|paperFT(g_j)(0)|^2. These steps suggest the displayed constant with no approximation limit.

This algebraic capacity mechanism is classical Cauchy–Schwarz plus the corpus's ground gap. A generic wrapper alone is BRIDGE/REDISCOVERED, not a research breakthrough. Decide whether its literal exposing-source application adds enough information before writing new Lean.

## Actual exposing-source target

The finite-realization source is literally

    F_(L,k)(u) = (polarRiemannDifferenceReal L (1/(k+1)) u : Complex).

For k=0, the zero-frequency factor is 1-2*polarWeight(1)>0; the cutoff Riemann kernel has a positive integral bounded below for all sufficiently large L. Therefore the proposed capacity bound predicts a fixed positive total-energy floor for every local-seed variance completion of this actual source, even when seed count, weights, positions and profiles depend on L. The finite exposing mixture retains the k=0 term with fixed positive weight. If verified with the exact normalizations, this would exclude vanishing-total-energy completion by that entire mechanism at the literal exposing source, rather than only at the auxiliary Fejer source.

[OPEN CORE] Verify the exact finite variance identity for unequal seeds, all support/polar conditions, the complete Fourier normalization, and the actual truncated Riemann source's zero-frequency lower bound. Then compare with the opposite-ray energy/tail budget without dropping any integer residual. This does not exclude arbitrary repairs that lack this local-seed representation.

## Current evidence

Deep query on small-aperture polar source, zero-frequency evaluation, energy coercivity and finite translates completed with partial=true (reranking deadline). All 20 candidate lemmas, 20 source arguments and the proposed ingredient set were inspected. File inventory complete for 68,449 entries, with substantial source-only/stale compiler data and background refresh incomplete. It found existing Fourier evaluation interfaces and small-aperture ground results; the proposed ingredient set does not prove the completion bound. No absence or novelty claim follows.

The next audit must revalidate the exact mixed-seed capacity and literal exposing-source application against any fresh matching source, then verify the actual source interfaces in Lean. Do not replace that work by another RH receiver, another generic positive-definite representation, or a numerical experiment.

Actual source definitions checked: `polarRiemannDifferenceReal` and `paperFT_polarRiemannDifference` in WeilPositivityMajorantRigidity, `truncatedRiemannKernelReal` in WeilFullConeRiemannKernelRigidity, and the exact finite-realization source/weight normalization in WeilWorkExposingRayFiniteRealization. The initial k=0 source weight in the energy normalization is 1/(2*pi), not an unspecified probability weight. No source regularity or transform convention is inferred from an abstract analogy.

Follow-up deep query restricted to Weil completed partial=true (local semantic deadline). All returned candidates/source arguments and the proposed ingredient set inspected; 68,452 files inventoried, compiler freshness partial, background refresh incomplete. It recovered the actual polar source, owned equal-modulus variance identity, and existing near-radical energy limits. The generated ingredient set conflates near-radical error with a small-aperture completion and does not close the candidate. Exact source inspection found `norm_paperFT_real_le` in WeilFullConeSpectralConsistency and `bulkCutoff_eq_one` in TruncatedRiemannKernelWeilEnergy as relevant parents. No matching mixed-seed capacity producer is established by these hits; no absence or novelty claim.
