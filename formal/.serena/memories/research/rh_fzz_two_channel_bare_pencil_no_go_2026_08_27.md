# FZZ-P fixed two-channel bare-pencil no-go (2026-08-27)

Formalized:
- formal/GaloisForLFunctions/RHTower/FZZCigarPunctureTwoChannelBarePencilNoGo.lean
- wired into formal/GaloisForLFunctions/RHTower.lean
- card docs/drafts/pipeline/3-formalized/fzz-puncture-two-channel-bare-pencil-no-go.md
- frontier map read only

Results:
- Exact dark eigenmode classifier for fixed A0=[[a,b],[c,d]] and nonzero row (p,q): canonical vector (q,-p) must satisfy a*q-b*p=E*q and c*q-d*p=-E*p.
- Fixed dark line supports at most one real eigenenergy, with no self-adjointness assumption.
- Coupling-sourced affine FZZ mode adds exactly transverse slope q*d0-p*d1 != 0.
- Defined fixed-pencil XiC completeness and proved it false for all coefficients, using corpus theorem exists_two_distinct_positive_real_XiC_zeros from HardyTheorem.

Route closure:
Fixed two-channel A0-EI with fixed coupling cannot cover even two unconditional Hardy zeros. Viable FZZ producer needs nonlinear/meromorphic A(E), moving K(E), or infinite-dimensional dark sector, and still owes exact common-kernel incidence plus transverse jet.

Verification:
- direct lake env lean passed
- targeted lake build module passed
- five theorem axiom audit: only propext, Classical.choice, Quot.sound
- scratch removed

Novelty audit:
Corpus had ingredients but no joined FZZ dark-pencil/Hardy no-go. Literature compared multilevel Friedrichs arXiv:quant-ph/0510058, emitter-array BIC arXiv:1904.13004, self-energy arXiv:2109.02939. No exact analogue found; route-level priority provisional.