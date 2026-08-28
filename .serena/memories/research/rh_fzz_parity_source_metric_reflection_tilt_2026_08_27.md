# FZZ parity source-metric reflection tilt (F9)

Route F9 is retired with a formalized positive survivor.

For every beta>0, the literal parity/Fermi source coefficients p=P(beta), q=P(2 beta), r=P(4 beta) satisfy p>r>0. The canonical source-metric conjugate swap is J_beta(u1,u2)=(a conj(u2), a^-1 conj(u1)), a=sqrt(r/p). Lean proves J_beta^2=id and B_beta(Ju,Jv)=conj(B_beta(u,v)).

On centered dyadic Mellin carrier (1,chi(rho)), its affine projective ratio is (p/r)*chi(1-conj rho), so bare metric reflection never equals functional-equation reflection. Its fixed locus is exactly Re rho = 1/2 + log(p/r)/(2 log 2), strictly right of critical line. No critical-line carrier is fixed.

Strongest replacement law: unique complex scalar correcting the projective action to functional-equation reflection is r/p=P(4 beta)/P(beta), even if equality is required on only one Mellin carrier. Any surviving interacting FZZ/GFZZ mechanism must independently produce this exact inverse diagonal factor or equivalent operator correction.

Lean module: formal/GaloisForLFunctions/RHTower/FZZCigarParitySourceMetricReflectionTilt.lean. Umbrella import added. Direct Lean and targeted module build pass. Key axioms only [propext, Classical.choice, Quot.sound]. Authoritative lint has no issue in module; global failure is unrelated unreachable concurrently owned modules. Failed-route card: docs/drafts/pipeline/5-failed/fzz-parity-source-metric-reflection-tilt.md. Frontier map was not edited.