# Prime-log Gibbs joint compact-open and jet limit

- **ID:** prime-log-gibbs-joint-compact-open-jet-limit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [BRIDGE] Gapped low-temperature Lehmann response and causal spectral-response holomorphy; Essler--Konik, arXiv:0907.0779; Sarkar--Mallik--Nyffeler, arXiv:hep-th/0010062; existing uniform `log 2` prime gap
- **Statement:** The explicit Hermitian prime-log Gibbs responses converge locally uniformly, and therefore through every holomorphic derivative, when inverse temperature and the finite-prime subsystem tend to infinity simultaneously.

## Goal

Upgrade the pointwise joint limit to the compact-open topology used by the analytic and Cauchy-jet corpus.  This removes any separate derivative-convergence or normal-family hypothesis for the prime-log Gibbs family and makes the physical realization usable by all-order jet consumers.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

On every closed upper strip `η ≤ Im z`, the reverse-transition resolvents satisfy `‖(log p + z)⁻¹‖ ≤ η⁻¹`.  The existing prime-gap estimate therefore becomes uniform in both the finite prime set and `z` on that strip, with error at most `exp (-β log 2) η⁻¹` times the total prime mass.  Every point of the upper half-plane has a neighborhood contained in such a strip.  Add this locally uniform vanishing error to the existing locally uniform thermodynamic convergence of the directed carrier, then apply the established holomorphic jet-return theorem.

## Proof

`[PROVED HERE]` Fix `η > 0`.  On the closed strip `η ≤ Im z`, the elementary resolvent estimate used by the pointwise Gibbs bound improves to

`‖G_{P,β}(z) - H_P(z)‖ ≤ exp (-β log 2) η⁻¹ M(u)`,

where `M(u)` is the total prime mass.  The right-hand side is independent of both the finite subsystem `P` and `z`, is nonnegative, and tends to zero as `β → ∞`.  Hence the reverse-transition error tends uniformly to zero on the strip for the genuine product filter `atTop` on `Finset Nat.Primes × ℝ`.

For any `z` in the upper half-plane, take `η = Im z / 2`; the open neighborhood `η < Im w` lies inside the closed strip.  Thus the error tends locally uniformly to zero.  The finite directed carriers already tend locally uniformly to the thermodynamic prime-log Herglotz carrier, so addition gives the joint compact-open Gibbs limit.

Each finite Hermitian Gibbs carrier is a finite sum of resolvents whose poles lie on the real axis; it is therefore holomorphic throughout the upper half-plane.  The existing holomorphic jet-return theorem now applies to the compact-open limit and yields convergence of every iterated complex derivative.  Rewriting the carrier by the exact finite KMS response identity transfers both conclusions to the physical response itself.

Finally, uniqueness of locally uniform limits identifies the compact-open response limit with an oriented prime limit exactly when the orientation is all-positive.  This is equivalent to the earlier pointwise joint selector, but now carries every holomorphic jet and specializes directly to `CanonicalConstraintOrientationLimit`.

## Lean certificate

- `finitePrimeLogHermitianGibbsCarrier_sub_bound_of_im_ge`
- `finitePrimeLogHermitianGibbsCarrier_sub_tendstoUniformlyOn_upperStrip`
- `differentiableOn_finitePrimeLogHermitianGibbsCarrier_upperHalfPlane`
- `finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint`
- `finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint`
- `iteratedDeriv_finiteHermitianGibbsResponse_tendsto_joint`
- `universalPrimeOrientationHermitianGibbsJointCompactOpenLimit_iff`
- `canonicalConstraintOrientationLimit_primeCarrier_is_HermitianGibbsJointCompactOpenLimit_iff`

## Log

- 2026-07-14 — Created after auditing thermal, reflection-positive, and Fisher modules.  Generic thermal Hankel positivity, Liouvillian sum rules, and virial identities are already present or active; the missing direct consumer-strength upgrade is joint compact-open convergence.
- 2026-07-14 — Proved the uniform strip estimate, joint compact-open limit, all-order response-jet convergence, and canonical-orientation selector in `PrimeLogGibbsJointCompactOpen.lean`.  Targeted and full `HTGeometry` builds pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passes.
