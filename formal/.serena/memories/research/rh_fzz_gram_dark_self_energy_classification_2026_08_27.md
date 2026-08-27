# FZZ-P Gram-dark self-energy classification (2026-08-27)

Formalized:
- formal/GaloisForLFunctions/RHTower/FZZCigarPunctureGramDarkSelfEnergyClassification.lean
- wired into formal/GaloisForLFunctions/RHTower.lean
- card docs/drafts/pipeline/3-formalized/fzz-puncture-gram-dark-self-energy-classification.md
- frontier map remained read only

Exact new route-level law:
- For bounded K between complete complex Hilbert spaces, ker(K†K)=ker K.
- On K-dark sector, ((A-K†K)x=0) iff Ax=0; positive Gram/Feshbach return cannot create or remove its own dark mode.
- In two-channel affine FZZ with on-shell source row equal to coupling row (p,q), internal-dark point mode iff row nonzero and slope minor q*d0-p*d1≠0.
- Fixed nonzero row and transverse slope yield point modes for every real target energy.

Surviving FZZ burden:
Derive an energy-dependent common-kernel law ker A(E) ∩ ker K(E) != {0} exactly at required zeta energies while keeping transverse jet, or derive dynamics beyond bounded positive Gram return. Coupling-sourced nodality itself is automatic and energy-blind.

Verification:
- direct lake env lean passed
- targeted lake build module passed
- four exported theorems use only propext, Classical.choice, Quot.sound
- scratch files removed

Novelty:
General ker(K†K)=ker K is standard; corpus and primary literature audit found no exact FZZ-puncture common-kernel/no-creation consequence. Compared arXiv:2109.02939, arXiv:1608.06833, arXiv:math/0604277. Priority provisional.