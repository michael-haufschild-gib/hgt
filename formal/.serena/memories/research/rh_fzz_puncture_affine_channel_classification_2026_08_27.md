# FZZ-P finite affine-channel classification (2026-08-27)

Closed module `GaloisForLFunctions.RHTower.FZZCigarPunctureAffineChannelClassification`.

For finite complex affine channels `v_i(x)=(c_i+(x-E)d_i)1_(E,E+1)(x)` with amplitudes `a_i`, collective source factors as `(C+(x-E)D)1_(E,E+1)` where `C=Σa_i c_i`, `D=Σa_i d_i`. A nonzero embedded L² mode exists iff `C=0 ∧ D≠0`; every solution equals `-D1_(E,E+1)` ae. Premise-free unit nodal channel realizes mode at every E, while unit regular channel never does. Thus local finite-channel occurrence is nonselective; FZZ producer must globally derive coefficient-faithful `C(E)=0`, `D(E)≠0` at divisor ordinates without zero fitting.

Verification: direct Lean passed; targeted build 11555/11555; axioms only propext/Classical.choice/Quot.sound; umbrella wired. Lint blocked solely by unrelated concurrent unwired `ThetaCuspLikelihoodFourthSixthSpectralDomination`. Stage3 card `docs/drafts/pipeline/3-formalized/fzz-puncture-affine-channel-classification.md`; active FZZ card and frontier updated.

Next corpus-driven loop: test globally fixed finite exponential-polynomial/finite-oscillator source families against superlinear zeta-zero density; extract infinite-channel/order-growth boundary.