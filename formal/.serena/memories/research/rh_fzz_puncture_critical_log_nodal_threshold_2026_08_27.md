# FZZ-P critical logarithmic nodal threshold (2026-08-27)

Closed module `GaloisForLFunctions.RHTower.FZZCigarPunctureCriticalLogNodalThreshold`.

At pure-power wall α=1/2, source `v_β(x)=x^(1/2)(1-log x)^(-β)1_(0,1)` has unique formal state `-x^(-1/2)(1-log x)^(-β)1_(0,1)` ae. A nonzero L² point mode exists iff β>1/2. Premise-free boundary witnesses exclude β=1/2 and realize β=3/4. Change x=e^-u turns state energy into `(1+u)^(-2β)`. Correct local invariant is `v/x∈L²`, not integer Taylor order; critical square-root nodes survive with stronger-than-half log damping.

Verification: direct Lean passed; targeted build 11598/11598; axioms only propext/Classical.choice/Quot.sound; umbrella wired. Lint blocked only by six unrelated concurrent unwired modules. Stage3 card `docs/drafts/pipeline/3-formalized/fzz-puncture-critical-log-nodal-threshold.md`; active FZZ card and frontier updated.

Next loop: universal arbitrary measurable-source classification, then apply to literal FZZ/GFZZ source object or isolate its exact absence.