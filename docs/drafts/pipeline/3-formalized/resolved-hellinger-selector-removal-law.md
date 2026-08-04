# Resolved Hellinger selector-removal law

- **ID:** `resolved-hellinger-selector-removal-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/static-local-complexity-law.md` · O4 Hellinger transfer
- **Statement:** A parameter-dependent selected-target event is bounded by one positive reciprocal Hellinger certificate uniform over every target in the same parameter fibre.

## Goal

Replace an invalid target-by-target union bound by one exact positive
selector-aware inequality.  In static Hamiltonian complexity, parameter is
Hamiltonian and target fibre is full low-circuit class.  The theorem is a
bridge, not the missing exponential estimate.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack identified
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: `resolvedHellinger_selectorRemoval`
- [ ] 3 → 4 publication-ready: use only after Lean formalization and novelty audit

## Theorem

Let `(Theta,eta)` be a probability space, let `(Omega,mu)` be an observation
space, and let `C` be an arbitrary target type.  For every `theta` and `c`,
let `p_theta` and `q_(theta,c)` be nonnegative integrable densities.  Let
`f_theta>0` be a reciprocal certificate and define

\[
 \operatorname{Aff}(\theta,c)=
 \int_\Omega\sqrt{p_\theta q_{\theta,c}}\,d\mu,qquad
 h(\theta)=\int_\Omega f_\theta p_\theta\,d\mu.
\]

Suppose an integrable function `r(theta)` satisfies

\[
 \int_\Omega q_{\theta,c}/f_\theta\,d\mu\le r(\theta)
 \qquad(\theta\in\Theta,\ c\in C).
\]

Let `selector : Theta -> C`, let `A` be measurable, and suppose for one
`alpha>0` that

\[
 \theta\in A\Longrightarrow
 \alpha\le\operatorname{Aff}(\theta,\operatorname{selector}(\theta)).
\]

Then

\[
 \eta(A)\le {\mathbb E_\eta h+\mathbb E_\eta r\over2\alpha}. \tag{1}
\]

## Proof

`[PROVED HERE]` Pointwise weighted arithmetic--geometric mean gives

\[
 2\sqrt{p_\theta q_{\theta,c}}
 \le f_\theta p_\theta+q_{\theta,c}/f_\theta.
\]

Integrate over `Omega` and use uniform reciprocal bound:

\[
 2\operatorname{Aff}(\theta,c)\le h(\theta)+r(\theta).
\]

Apply this to `c=selector(theta)` on `A`.  The local affinity lower bound
gives `2 alpha <= h(theta)+r(theta)`.  Integrate on `A`, then use
nonnegativity of both costs to enlarge to all `Theta`.  Division by
`2 alpha>0` proves `(1)`.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.ResolvedHellingerSelectorRemoval`
- **Capstone:** `resolvedHellinger_selectorRemoval`
- **Helpers:** `two_mul_sqrt_mul_le_weighted_sum`,
  `two_mul_hellingerIntegral_le_weighted_integrals`,
  `resolvedHellinger_selector_event_measure_le`
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Wiring:** imported by `GaloisForLFunctions.HTGeometry`

## Hostile audit

- Hamiltonian/parameter label must remain resolved.  Erasing it
  would allow a mixture from one parameter fibre to imitate another.
- Reciprocal bound is fibrewise and uniform over circuit target; no
  interchange of `sup` and expectation occurs.
- The theorem does not supply a small right-hand side.  That requires an
  independently constructed positive barrier with the desired exponential
  rate.
- Taking `f` to encode distance from the low-circuit set merely renames the
  original problem and is not progress.  A valid application must derive
  `f` from separate physical structure, for example a proved transported
  parent-Hamiltonian energy barrier.

## Novelty status

No novelty claimed.  Components are classical Hellinger affinity and
arithmetic--geometric mean.  New value here is exact parameter-resolved
selector formulation for static-complexity frontier.
External priority audit remains required before any publication claim.

## Log

- 2026-08-04 — Derived from Hellinger/label-retention audit; dependency-closed paper proof completed.
- 2026-08-04 — Exact continuum theorem proved in Lean and wired into `HTGeometry`.
