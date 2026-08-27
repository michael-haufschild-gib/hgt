# FZZ-P two-channel Plücker classification (2026-08-27)

Formalized module:
- formal/GaloisForLFunctions/RHTower/FZZCigarPunctureTwoChannelPluckerClassification.lean
- wired into formal/GaloisForLFunctions/RHTower.lean
- card moved to docs/drafts/pipeline/3-formalized/fzz-puncture-two-channel-plucker-classification.md
- frontier map remained read only

Exact result:
For nonzero internal row (p,q), a nonzero amplitude in its kernel carries an affine-channel FZZ puncture point mode iff q*c0-p*c1=0 and q*d0-p*d1≠0. Reverse witness is (q,-p). If slope row is aligned, no mode exists. Canonical rows (1,0),(1,0),(0,1) realize a mode at every E, proving arbitrary two-channel matrix mixing is not zeta-selective.

New burden:
Physical GFZZ/Feshbach dynamics must derive energy-dependent rows whose on-shell Plücker minor vanishes and slope minor stays nonzero exactly at zeta-zero energies. Abstract matrix fitting cannot do this.

Verification:
- direct lake env lean passed
- targeted lake build GaloisForLFunctions.RHTower.FZZCigarPunctureTwoChannelPluckerClassification passed
- five theorem #print axioms: only propext, Classical.choice, Quot.sound
- scratch files removed

Novelty audit:
Corpus had affine channel and rank-one classifications but no internal-row/Plücker theorem. Primary literature searches (Friedrichs threshold arXiv:math/0604277; two-channel Feshbach arXiv:cond-mat/0601542; structured continuum arXiv:0802.3808) found no exact FZZ analogue; priority provisional.