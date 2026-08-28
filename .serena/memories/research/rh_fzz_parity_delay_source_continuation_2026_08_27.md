# FZZ parity-delay source continuation (2026-08-27)

Formalized `formal/GaloisForLFunctions/RHTower/FZZCigarParityDelaySourceContinuation.lean`, wired into `RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/fzz-cigar-parity-delay-source-continuation.md`.

New source law:
- Literal FZZ Bose delay `B(t)=1/(exp t-1)`.
- Dyadic parity subtraction `P(t)=B(t)-2B(2t)=1/(exp t+1)` for `t>0`.
- `P(t)` is exactly the alternating supertrace of literal FZZ charge delays: sum `(-1)^n exp(-(n+1)t)`.

Define source-first `fzzCigarParityMellin(s)=Mellin(P)(s)`, containing no zeta/Xi/zero enumeration. Proved:
- holomorphic on `Re s>0`;
- in `0<Re s<1`, zero iff zeta zero iff xi zero;
- at `s=1/2+iE`, source mode iff prior FZZ-labelled horizon mode;
- source-mode completeness by real horizon energies iff RH.

This closes FZZ-P independent continuation/divisor landing and repairs old circular endpoint where divisor was definitionally zeta. It does not prove dynamical orientation; remaining open theorem that every source zero has Re=1/2 is exactly RH.

Literature: Ashok–Troost 1101.1059 supplies FZZ spectral asymmetry; González–Negrín 2604.15396 supplies Salem Fermi-mode RH criterion; no searched primary source joins them. Components are classical individually; exact FZZ parity-supertrace/Salem identification is corpus-new and literature-unlocated.

Verification: direct Lean passed, targeted module build passed, key axioms only propext/Classical.choice/Quot.sound, scoped checks clean, global lint only unrelated unreachable modules.