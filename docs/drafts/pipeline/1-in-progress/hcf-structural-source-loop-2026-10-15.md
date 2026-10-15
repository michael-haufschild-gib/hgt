# HCF structural source conjecture loop

Status: active research; no new theorem claimed.

Objective: overcome a structural obstacle in route HCF with an unconditional,
dependency-closed theorem. Improved bounds and repackaged RH criteria do not meet
the objective. No numerical experiments, external search, or literature audit.

Plan:
1. Establish current frontier from Lean corpus search and declarations.
2. Form exact conjectures; attack each and record what failure teaches.
3. Complete paper proof before formalization; audit actual dependencies.
4. Formalize a qualifying survivor, wire its umbrella, run focused Lean audit and lint.

Corpus evidence inspected:
- XiGaussianHeatRouteScaleCapstone: growing heat-window constants are exactly RH.
- XiGaussianHeatWindowThresholdLaw: sharp transfer between heat windows and
  restricted Weil positivity; the converse currently uses positive ground energy.
- XiGaussianHeatWindowConditioning: large windows have extremely small Rayleigh
  quotients, so numerical or coarse coercivity continuation is unsuitable.
- XiGaussianHeatRetentionObstruction: no degree-uniform inverse retention over a
  fixed heat step.

Next investigation: native source identities and cross-corpus mechanisms for
positivity transport, including whether a structural null-space or boundary law
can replace impossible uniform retention.

Conjecture/attack ledger:
1. Fixed-step retention could convert native dissipation to relative phase control.
   FALSE: XiGaussianHeatRetentionObstruction proves collapse in every nonzero
   polynomial principal ideal, including pole cancellation. Survivor already in
   corpus: exact absolute channel transfer, not a relative sign mechanism.
2. Strict aperture decrease might eliminate a flat zero-energy interval.
   ALREADY PROVED: CCMRestrictedWeilPolarStrictDomain proves strict decrease and
   the RH-or-unique-zero-aperture alternative. It does not select the RH branch.
3. A small positive real-channel fraction might be easier than Hankel positivity.
   CIRCULAR AS A SUBSTITUTE: XiGaussianFixedTimePhaseThreshold shows any uniform
   positive fraction is exactly RH; off-line localization reaches the negative
   native-energy endpoint at every positive time.
4. Compact completion or finite coordinate truncation might control the sign.
   INSUFFICIENT: PaperHeatHankelOperator is compact unconditionally, while
   PaperHeatHankelCompletion retains the full RH-equivalent sign question.
5. Full inertia convergence of critical heat windows to the restricted even Weil
   form is a possible structural extension of XiGaussianHeatWindowSpectralIdentity.
   NOT A QUALIFYING RESULT YET: no dependency-closed proof; a transfer theorem alone
   does not supply the missing arithmetic sign. Do not count this as success.

Search provenance: deep corpus searches report complete inventory (~72,400
files), but semantic coverage is unmeasured and most declarations have source-only
or pending compiler status. Search suggestions are leads, not proof certificates.
Serena symbol lookup rejects Lean paths as ignored; use direct Lean source reads
for these modules. No Lean files changed and no Lean result claimed.

Constraints: preserve other worktree changes; no full builds, no new premises,
no added axioms, no heartbeat increases. Use foreground focused builds and final
`lake env lean` audit. Read no historical research markdown beyond requested
HCF frontier entry.
