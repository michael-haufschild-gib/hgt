# PM: actual signed damping covariance below half damping

- **ID:** pm-signed-damping-covariance
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, PM; corpus searches listed below.
- **Statement:** The actual Bézout-corrected relative damping loss has a horizon-uniform signed integral bound from cofinally small positive damping to one half.
- **Status:** OPEN. Reorientation and failed-inference analysis; no new mathematical bound or Lean theorem claimed.

## Goal and exact hard problem

Continue route PM/FZZ-P through actual Möbius energy admission. Write

`Aε(n) = pmPowerDampedCenteredDivisorPrefix ε n`,
`Dε(n) = dampedChebyshevError ε n`,
`Eε(T) = Σ_(1≤n≤T) Aε(n)^2/(n(n+1))`,
`Rε(T) = Σ_(1≤n≤T) (Aε(n)-1)^2/(n(n+1))`,
`Vε(T) = Σ_(1≤n≤T) (Aε(n)-1)Dε(n)/(n(n+1))`.

Prove, from the actual arithmetic source, with no admission premise:

`∀ δ>0, ∃ a, 0<a<min(δ,1/2) ∧ ∃ L, ∀ T,`
`  ∫_(a..1/2) -2Vε(T)/(1+Rε(T)) dε ≤ L`.

The upper endpoint is already admitted. The exact RH equivalence is
`ArithmeticCompensationTheory.riemannHypothesis_iff_cofinal_bezoutCorrected_loss`
in `ConstructingAnArithmeticCorrector.lean`. This equivalence is a receiver,
not a proof of the displayed arithmetic bound. Constants may depend on a;
no bound uniform as a tends to zero is required.

## What the new corpus already settles

1. Admission threshold equals zeta zero width. Half-damping admission,
   compact operator tails and right operator-norm continuity are established;
   none extends admission to a fixed damping below half.
2. `bezoutCorrectedEnergy = 1+R`, comparable within factor three to `1+E`.
   Its derivative is `2V`. Integrated relative loss is the exact endpoint
   logarithmic ratio. Comparable correctors alter that ratio by bounded
   endpoint terms; their existence with the required budget is itself
   equivalent to admission (`TheAdaptedEnergyIsExactlyAdmission.lean`).
3. Scalar work `W-V` is paid on each compact positive damping interval.
   Pointwise or positive-part loss bounds can demand more than admission.
   The signed integral is the calibrated target.
4. `TheNormalizedReceiverBlowUpProfile.lean` classifies the alternative:
   at fixed `0<ε<1/2`, unbounded energy yields unit-energy profiles escaping
   every fixed window and concentrating beyond growing sub-horizons.
   Exact inversion retains the full forcing defect and all cofactor terms.
   Pointwise homogeneous convergence is not global energy convergence.
5. Two-scale scalar compensation and relative transverse-energy summability
   are established. Absolute source energy and connection terms remain.
   The compensated Bézout interior equals the source energy plus a bounded
   remainder with coefficient one; strict contraction is still unproved.

These source statements were read, not freshly compiled in this batch.
No claim of a new dependency audit is made.

## Concrete proof input and attack

`DampingWorkAsArithmeticMarkovBoundaryFlux.lean` gives the actual finite
downward generator G, with departure rate `log n`, and, for `vε(n)=Aε(n)/n`,

`∂ε Eε(T) = B_T(vε) - J_T(vε) - 2m(ε) F_T(vε)`,
`F_T(v) = Σ_(1≤n≤T) n/(n+1) v(n)`,
`m(ε) = dampedReadout ε`, `J_T(v)≥0`.

Here B is the counting-measure boundary flux. The pronic measure is not
invariant. `TheDampingChainInReceiverCoordinatesAndHTransform.lean` already
integrates this full identity and proves
`mem_receiverDampings_iff_integral_markovWork_bound`; this integration is
finished work, not the next theorem to duplicate.

The arithmetic attack is the signed finite residue Gram expression for the
same v, retaining the constant boundary defect. For modulus cutoff D≥T,

`vε(n) = Σ_(1≤d≤D) μ(d)d^(-ε)(floor(n/d)/n - 1/d) + δε(D)`

for positive n≤T, where `δε(D)=Σ_(d≤D) μ(d)d^(-1-ε)-density(ε)`.
Both linear and quadratic defect terms are compulsory after squaring or
differentiating. Existing exact declarations include
`normalizedCenteredPrefix_eq_residuePartialPrefix_add_boundaryDefect` and
`orbit_partial_energy_eq_residueGram_add_boundaryDefect`.

Next proof attempt must bound the complete signed damping-integrated Gram
expression using μ(d)μ(e), including mixed entries and defect terms. Taking
absolute values termwise restores the half-damping obstruction. Merely
integrating `(de)^(-ε)` returns the already-known endpoint energy identity;
the missing step is an independent arithmetic inequality on the combined sum.

## Conjecture / proof-attempt log

### 2026-10-24: reorientation

- Stronger trial conjecture: `Vε(T)≥0` throughout `0<ε≤1/2`, all T. This
  would imply the desired bound, but no proof or counterexample was found.
  Actual first-cell positivity near zero and escaping positive residual work
  do not establish its all-horizon sign. Keep it unproved, not falsified.
- Failed proof step: infer backward energy control from nonnegative Markov
  jump energy. In the exact derivative, J enters with a minus sign; backward
  continuation needs a lower bound on total work. Boundary flux and density
  forcing remain. Dropping either does not give the required estimate.
- Failed proof step: infer exclusion of normalized escape from half-damping
  compactness. Compactness can send weakly escaping unit profiles to zero;
  no bounded inverse is supplied. The full inversion-defect pairing must be
  controlled on moving horizons, not only at fixed cells.
- These are failed inferences, not retired routes or new no-go theorems.
  Their surviving exact identities and classifications are already in Lean.
  No additional wrapper or generic countermodel is being formalized as a
  substitute for the actual signed covariance estimate.

## Search provenance and contribution assessment

Used `scripts/formal_tools.py research` directly, ten corpus-only searches:
route-PM frontier; normalized escape; half-damping chain; two-damping tangent
sign; semigroup interpolation; corrected signed loss; Markov flux; two-scale
compensation; residual-work monotonicity; generator/adjoint boundary flux.
All completed with `partial=false`, no reported errors/index warnings and
no generated proof-idea or ingredient groups. Candidate and source statements
were inspected; decisive statements were checked in source. No mathlib search
was needed. No web search or novelty check followed the user's prohibition.

Prior leading prime-current compensation is genuine but controls only a
relative leading term. Newer scalar compensation already goes further; the
absolute signed remainder is still unpaid. This reorientation advances target
selection, not the hard mathematical frontier. The next useful success must
be an actual-source signed covariance bound or an arithmetic exclusion of
the normalized escape alternative. More endpoint identities, scalar rate
improvements and conditional RH wrappers would not discharge this gap.

No Lean changes, builds or numerical experiments in this reorientation batch.
RH and its negation remain unproved here; the overall goal remains active.

## 2026-10-24: signed Gram and complete dilation attempts

The replacement goal supplied in
`/Users/michael/.codex/attachments/4c5bbddf-7584-4f53-911d-93a2febe1afc/pasted-text-1.txt`
was read. Success now explicitly means an unconditional Lean proof of RH.
The PM section of the frontier map and relevant entries in
`docs/reports/rh-killed-routes.md` were checked. New criteria, no-gos and
numerical improvements are not the requested deliverable.

**Previous-turn classification:** progress in selecting the attack from newer
corpus evidence, but no progress on the required arithmetic estimate.

### Signed Gram attempt

The existing residue diagonal estimate is `G_T(d,d)≤2/d`. Thus, for fixed
positive ε, the diagonal with weights `μ(d)^2 d^(-2ε)` is bounded independently
of both cutoffs. The hard sum is genuinely the complete mixed Gram expression
and its boundary correction, not the diagonal or coefficient square sum.

Attempted proof by prime pairing does not close: each opposite-sign pair has
a favorable mixed term because the residue Gram entries are nonnegative,
but the norm of the sum of such pairs includes all interactions between
different pairs. No estimate on that complete interaction was proved.
The existing Bessel estimate replaces this structure by `Σ d^(-2ε)` and
therefore supplies no below-half admission. A local-pair inequality cannot
be silently promoted to an inequality for the complete actual source.

No actual-source counterexample was established. No new no-go was pursued.

### Dilation forcing attempt

Read the exact normalized self-improvement and cofactor-energy sandwich in
`TheNormalizedReceiverBlowUpProfile.lean`, including the remaining inversion
defect. The known pointwise bound `ρ(n)/√E_T≤n/√E_T` does not control its
pairing over the energy-carrying moving horizon. The individual deep-cofactor
vanishing theorem does not justify interchanging a growing cofactor sum with
the limit; its norm weights meet `Σ j^(-ε-1/2)`.

A continuous-source completion was examined on paper. Let
`Cε(x)=Σ_(k≤x) cε(k)`, `mε=1/ζ(1+ε)`, and
`Fε(t)=Cε(1/t)-mε/t` for t>0. The proposed complete identity is

`Σ_(j≥1) j^(-ε) Fε(jt) = floor(1/t)-1/t`.

Its algebraic mechanism is finite raw-prefix convolution
`(μ(d)d^(-ε)) * (j^(-ε)) = δ₁`, together with
`mε Σ_(j≥1)j^(-1-ε)=1`. The raw terms vanish for j>1/t; the remaining
mean tail is absolutely summable for ε>0. The existing
`RHTower.dilationCenteredSource_ofReal` in `FermiDilationMeanInversion.lean` identifies the
continuous source with the discrete prefix minus the within-cell mean term.

This cancels the artificial large forcing only by retaining the complete
mean tail and within-cell correction. It does not supply an energy ceiling:
pairing the identity with Fε on a truncated physical horizon still leaves
the full signed proper-cofactor covariance. The half-damping obstruction
reappears if that covariance is bounded by individual dilation norms.
This is an unfinished proof attempt, not a new frontier theorem; no Lean
module is being added for an identity that leaves the required bound open.

### Search and verification record

Seven further direct corpus searches covered signed residue Gram cancellation,
prime-paired modes, centered-prefix signs, Abel smoothing, the exact normalized
identity, deep-cofactor boundary moments, and continuous floor-source inversion.
The Abel-smoothing query returned a partial result with a semantic runtime
deadline error and no candidates; no mathematical inference used that absence.
Other hybrid queries completed without reported errors or warnings; the
known-name normalized-identity lookup used lexical mode. Retrieved candidate
and source statements were inspected, and the decisive modules were read.

No mathematical obstacle was solved in this batch. No Lean source was changed,
no build was run, and no numerical computation, web search or novelty check was
performed. The next successful step must control the complete actual signed
covariance; neither pairwise signs nor the completed forcing identity does so.
