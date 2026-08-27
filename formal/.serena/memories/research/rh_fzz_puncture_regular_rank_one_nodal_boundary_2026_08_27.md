# FZZ-P regular rank-one no-go and nodal survivor (2026-08-27)

Module `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureBoxRankOneNoGo.lean` proves premise-free route results for every real target E:

- Unit box form factor v_E=1_(E,E+1) is L2.
- Any L2 representative equation `(x-E)f + alpha v_E = 0` forces alpha=0 and f=0 a.e.; nonzero alpha creates nonintegrable inverse-square pole.
- No nonzero embedded point mode and no completeness of nontrivial FZZ/zeta divisor by these rank-one modes.
- Sharp survivor: nodal factor w_E=(x-E)v_E and state g_E=-v_E; g_E is nonzero L2 and solves `(x-E)g_E+w_E=0` pointwise.

Meaning: regular rank-one occurrence nonzero at target is terminal. Viable regular occurrence needs source-derived collective form-factor node at every target; fitting nodes to Xi zeros is circular. Next loop should classify multichannel collective nodal cancellation and source faithfulness.

Verification: direct Lean passed; targeted build 11554/11554; axiom audit only propext/Classical.choice/Quot.sound; umbrella wired. Formal lint rerun was blocked only by unrelated concurrent unwired `ThetaCuspLikelihoodFourthSixthSpectralDomination`. Cards: `docs/drafts/pipeline/3-formalized/fzz-puncture-box-rank-one-no-go.md`, active FZZ card and frontier appended.