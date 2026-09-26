# Exact first-atom tail audit

- **ID:** RH-FIRST-ATOM-TAIL-AUDIT-ROOT-20260926
- **Stage:** 1-in-progress
- **Type:** [OBSTRUCTION TEST]; full theta and RH remain open
- **Owner:** root
- **Parent:** `rh-nonlocal-tail-root-2026-09-26.md`

## Frozen C7 after C6

Question: can the exact first atom retain negative directions that every fixed
asymptotic correction misses? First test: f(x)=thetaCuspSourceTerm x 1 has
negative full-line center energy `integral 2x*f(x)^2 < 0`.

Derived paper certificate, frozen before Lean: existing Wigner Mellin formulas
at sigma=1/2 and 3/2 predict

`integral exp(2x)*f(x)^2 = [75/(44*pi)]*integral f(x)^2`.

The denominator energy is strictly positive. Since 75<44*pi, the pointwise
inequality 2x<=exp(2x)-1 implies negative center energy. This uses complete
integrals of the exact first atom; no numerical approximation or finite scan.
The positive survivor is an exact normalized scale moment, not only a sign.

Define the bare-atom tail diagonal `D(x)=integral_(t>x) 2t*f(t)^2`.
Integrability implies D(x) tends to the negative center energy as x tends to
negative infinity. Thus the bare-atom kernel is not globally PSD. This alone
does NOT prove a negative direction at arbitrarily large positive nodes.

## Conditional continuation to audit, not yet a result

Corpus `AnalyticKernelUniquenessRegion` preserves finite negative dimensions
on every accumulating sampling set for a bounded Hermitian form with a total
weakly analytic section family. The exact Krein channel construction suggests
an L2 realization of the bare-atom tail kernel on a complex strip. If all
analyticity/majorant obligations close, its negative index would survive on
any positive tail, excluding uniform first-atom-only positivity. That
specialization is unproved and is not assumed in C7's initial sign test.

## Whole route

C6 closes an all-rank corrected-model producer. C7 tests whether this can be
transferred through the exact first atom before attempting the complete
source. Full theta has even-source center cancellation, so the bare-atom
obstruction cannot be assigned to it. Any no-go must retain its exact scope.

## Plan

1. Verify exact normalized scale moment and center sign in Lean.
2. Extract the sharp moment invariant and bare-tail diagonal consequence.
3. Audit analytic negative-index locality on the literal first-atom sections.
4. Return to a complete-source uniform comparison with the surviving invariant.

## C7 initial attack formalized and audited

Exact scale moment, strict negative center energy, incoming diagonal limit,
and failure of global bare-atom PSD are Lean-closed and audited. Positive
survivor and complete paper proof:
`../5-failed/rh-first-atom-global-tail-psd-root-2026-09-26.md`.
Named build and all 13 public theorem axiom reports pass. Index refreshed;
final `lint --check-generated` passes. All owned jobs exited. The positive-tail analytic-locality
specialization remains open; do not silently strengthen the diagonal result.

## Next dependency audit: exact paths, no assumed applicability

- `AnalyticHermitianClosedSpanRealization` constructs a total realization by
  compressing a bounded Hermitian form to its analytic section span.
- `AnalyticKernelUniquenessRegion.hasFiniteGramNegativeDimensionOn_accumulationSet_iff`
  is the already-proved negative-index transport theorem. It requires weak
  complex analyticity of every Hilbert pairing, not merely real smoothness.
- `ThetaCuspComplexStrip` supplies the actual complex source terms, their
  differentiability, and strip majorants. For the first atom one may specialize
  the term bound at n=1. A proposed section is
  `g_plus/minus(z,s)=(z+s+/-1)*thetaCuspComplexTerm(z+s,1)` in the two-copy
  L2 space on s>0. Its bounded sign form is diag(+1,-1)/2. On real nodes its
  kernel should equal C7's exact first-atom kernel by finite algebra.
- `SuzukiShiftedXiAnalyticKernelRealization` illustrates the compression
  pattern, but its Hardy sections are a different carrier and cannot simply
  be reused as the theta sections.
- Retrieved `HTGeometry.L2DominatedDerivative.hasDerivAt_toLp_two_of_dominated`
  has a REAL parameter, so it does not directly discharge complex analyticity.
  The needed weak complex pairing/under-integral argument remains to prove.

These are source-audited construction ingredients, not a closed locality
specialization. No negative first-atom Gram direction on positive nodes is
claimed yet.

## Frozen C7b: first-atom negativity in every positive tail

[BRIDGE] Derived from the C7 negative diagonal and retrieved analytic locality,
not a primary universal conjecture. Exact target: for every R, there are
finitely many real nodes x_i>R and real coefficients a_i with
`sum_ij a_i*a_j*K_f(x_i,x_j)<0`.

Paper mechanism: on the strip |Im z|<pi/4 use the two L2 sections
`g±(z,s)=1_(s>0)*(z+s±1)*thetaCuspComplexTerm(z+s,1)`.
Their difference Gram form divided by 2 is the bare-atom kernel on real nodes.
On each compact parameter ball they are bounded by C*exp(-|s|/2), which is L2.
For any L2 vector w, the scalar pairing is therefore locally dominated by
C*|w(s)|*exp(-|s|/2), an integrable function. The retrieved theorem
`HTGeometry.CauchyDominatedIntegralHolomorphy.differentiableAt_integral_of_cauchy_dominated`
provides its holomorphy without estimating all parameter derivatives.
Compression to the section span and the existing accumulation-set negative-index
theorem then transport C7's negative direction to every real tail. Real kernel
values split complex coefficient energy into two real coefficient energies.
All local domination and exact carrier identities remain explicit Lean obligations.

**Whole-route test:** if C7b closes, even the exact first atom cannot supply a
uniform all-rank tail sign. The complete theta correction, although pointwise
small in the far tail, is then essential at some growing ranks. C6 remains an
exact positive model, but its remainder cannot be ignored through fixed-order
asymptotics. The complete-source sign remains the goal.

## C7b proof closed in scratch

The exact finite real packet statement and `not_tail_posSemidef` now pass Lean.
No numerical experiment was used. The L2 realization, strip envelope, dense
sampling argument, finite coefficient extraction, and real coefficient split
are all checked; no analytic bridge remains assumed. Final leaf audit pending.

Positive survivor: the source realization preserves every finite negative
dimension on every real tail. Complete theta satisfies the same hypotheses,
with its complete infinite sum retained. This is sign locality, not a theta
positivity proof.

Whole-route decision: stop seeking positivity of the exact first atom at all
ranks. Revisit the complete-source comparison using its reflection completion;
fixed-order or fixed-rank far-tail expansions cannot settle this obstruction.
