# Signed prime–Hodge integral–nuclear homotopy defect

Lean module: `formal/GaloisForLFunctions/RHTower/PrimeHodgeHistoryIntegralNuclearHomotopyDefect.lean`, wired after `ThetaMellinSixIntegralNuclearFormation` in RHTower umbrella.

Definition:
[
T(t)=0quad(t=0),qquad
T(t)=operatorname{sgn}(t),T^+_{|t|}quad(t
e0),
]
where (T^+_d) is the existing positive literal kernel on (ell^2(mathbb N	imesmathrm{Primes})).

Lean proves:
- (T(-t)=-T(t));
- (T(t)in S_1) for every real (t);
- (operatorname{Tr}T(t)=operatorname{sgn}t);
- (|T(t)|_1=|operatorname{sgn}t|), hence unit nuclear norm off wall;
- positive orientation for (t>0), negative orientation for (t<0);
- every same-history cross-prime entry is nonzero for (t
e0);
- (T(1)) is the prior closed unit-aperture object;
- signed diagonal equals theta Mellin-six flux times coefficient-faithful unsquared prime density.

Capstone: `primeHodgeHistoryIntegralNuclearHomotopyDefect_closed`.
Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
Targeted module build passed; no umbrella build.
Paper/status updated. Chamberwise trace-norm continuity remains paper-only; Xi completion-to-horizon transport remains open.