# Receiver energy growth at the zero abscissa

- **ID:** receiver-energy-growth-at-the-zero-abscissa
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** review-2610 W7(viii), B3.2; actual Abel-escape dominance premise
- **Statement:** For every positive damping ε and κ > max(0, 2Θ − 2ε − 1), the actual damped Möbius receiver satisfies Eε(T) ≤ Cε,κ (T+1)^κ, where Θ is the actual zeta zero abscissa.

## Goal

Discharge the energy-growth premise in the actual-source Abel atom and capacity
laws at every attained rightmost zero. No zero-free strip, simplicity,
residue-summability, or energy bound is assumed to obtain the upper bound.
Simplicity remains a restriction of the existing simple-pole atom formula.
This does not prove RH or resolve escape at infinite height.

## Gates

- [x] 0 → 1: precise actual-source statement; existing subpower reciprocal-zeta input located.
- [ ] 1 → 2: dependency-closed paper proof.
- [ ] 2 → 3: exact Lean theorem, individual `lake --old env lean` check, transitive axiom audit, umbrella import.

## Existing inputs and novelty audit

`InvZetaAbscissaSubpolynomial` proves subpower bounds for the actual reciprocal
zeta right of Θ. `TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa`
and `AdmissionBelowHalfDampingAboveTheZeroWidth` use these to prove admission
when ε > Θ − 1/2. The exponent upper bound below that admission threshold was
not found in the corpus search. `TheAbelEscapeAtomsOfZetaAreItsDominantZeros`
still takes polynomial energy bounds as explicit hypotheses.

## Approach

For σ > max(1/2, Θ − ε), prove square integrability of
u ↦ exp(−σu) Aε(floor(exp u)). Its Laplace transform is the pole-cleared
function ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s. Convexity for ζ and the subpower bound
for its reciprocal give a square-integrable majorant on vertical lines.
Paley–Wiener and Laplace uniqueness identify the Hardy datum with the actual
receiver. Positive log-cell weights then give Eε(T) = O((T+1)^(2σ−1)).

The value at s=1 must be regularized explicitly; Lean's value of ζ at its pole
cannot be used as an analytic continuation. The discrete receiver is centered
at integers, so the existing Mellin-cell formula includes the centering term
−mε ζ(s), not −mε/(s−1).

## Status

Conjectural until all analytic identification and cell comparisons are proved.
No credited contribution yet.
