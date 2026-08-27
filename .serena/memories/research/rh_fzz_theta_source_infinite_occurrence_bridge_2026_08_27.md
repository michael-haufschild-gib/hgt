# FZZ theta-source infinite-occurrence bridge (2026-08-27)

Formalized `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureThetaSourceInfiniteOccurrenceBridge.lean`, wired into `RHTower.lean`.

Result:
- centered coordinate `z(rho)=(rho-1/2)(-i)`, with `Re z=Im rho` and `Im z=1/2-Re rho`;
- source-pencil occurrence iff `xi rho=0` iff nontrivial FZZ-labelled Mellin zero;
- every occurrence yields a nonzero eigenvector of fixed Hedenmalm theta kernel operator with eigenvalue `-z(rho)⁻¹`;
- real-energy FZZ-labelled mode iff noninvertibility of fixed theta-source pencil at that real energy;
- FZZ completeness iff all occurrence coordinates are real iff fixed theta operator nonzero spectrum is real.

Classification: route F1 retired as circular, because `fzzCigarContinuumMellinDivisor` is definitionally `riemannZeta`. This is a dependency-closed cross-route compatibility survivor, not independent FZZ production. Failed-route card: `docs/drafts/pipeline/5-failed/fzz-puncture-theta-source-infinite-occurrence-bridge.md`.

Surviving open core: source-first complex continuation and occurrence operator from literal FZZ/GFZZ coefficients, with divisor comparison proved without defining object using zeta/xi/XiC/zero enumeration.

Verification:
- direct Lean passed;
- targeted module build passed;
- key axioms only propext/Classical.choice/Quot.sound;
- scoped checks clean;
- global lint failures only concurrently-owned unreachable modules.