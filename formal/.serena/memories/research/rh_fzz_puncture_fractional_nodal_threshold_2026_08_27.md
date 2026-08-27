# FZZ-P sharp fractional nodal threshold (2026-08-27)

Closed module `GaloisForLFunctions.RHTower.FZZCigarPunctureFractionalNodalThreshold`.

For target-centered source `v_α(x)=x^α 1_(0,1)(x)`, every L² solution of `x f + v_α=0` equals `-x^(α-1)1_(0,1)` ae. A nonzero embedded point mode exists iff `α>1/2`. Premise-free boundary witnesses exclude `α=1/2` and realize `α=3/4`. Therefore earlier first-order node was sufficient but not sharp; exact local FZZ occurrence burden is more-than-half-order vanishing. Any α above threshold works in every target chart, so local occurrence remains nonselective; global winding dynamics must derive node locations and strength.

C9 finite-exponential-type density conjecture failed unconditionally: corpus gives only implication to a linear simple-critical-zero envelope, while available unconditional critical-line census is logarithmic; no contradiction.

Verification: direct Lean passed; targeted build 11557/11557; axioms only propext/Classical.choice/Quot.sound; umbrella wired. Lint blocked only by five unrelated concurrent unwired modules. Stage3 card `docs/drafts/pipeline/3-formalized/fzz-puncture-fractional-nodal-threshold.md`; active FZZ card and frontier updated.

Next loop frozen in active card: logarithmically corrected critical germs `x^(1/2)(log(1/x))^(-β)` and literal FZZ/GFZZ source regularity.