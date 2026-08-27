# FZZ universal weighted-source classification (2026-08-27)

Formalized `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureWeightedSourceClassification.lean` and wired `RHTower.lean`.

Main theorem `fzzPunctureWeightedSourcePointMode_iff`: for arbitrary `E : ℝ`, `v : ℝ → ℂ`, scalar equation `(x-E)f+v=0` has a nonzero `L²` solution iff canonical quotient `-v/(x-E)` is `MemLp 2 volume` and `v` is nonzero ae. Every solution is canonical quotient ae. Fractional and critical-log occurrence laws are corollaries.

Direct Lean passed; targeted build passed 11599/11599; axioms only `propext`, `Classical.choice`, `Quot.sound`. Stage-3 card `docs/drafts/pipeline/3-formalized/fzz-puncture-weighted-source-classification.md`.

Meaning: scalar local occurrence fully closed; no more fitted local germs. Remaining core is literal coefficient-faithful FZZ/GFZZ source/operator and global zeta-selective landing.