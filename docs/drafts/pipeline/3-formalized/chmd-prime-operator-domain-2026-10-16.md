# CHMD: the full arithmetic generator is a bounded perturbation

Status: formalised and directly audited in Lean. RH remains unproved. Parent investigation: `../1-in-progress/chmd-operator-core-and-synthesis-2026-10-16.md`.

## Structural contribution

Every vector in the actual theta-cosh mass L2 space admits the literal complete prime difference. The prime generator is an everywhere-defined bounded positive selfadjoint operator. The full and archimedean closed form graphs are isomorphic by the identity on sources. More strongly, their actual generator domains coincide and their generator graphs differ by the bounded invertible change `(u,v) -> (u,v-Pu)`.

This removes the infinite arithmetic part from both domain problems. It does not prove the remaining archimedean compact operator-core theorem, spectral synthesis, Weil positivity, or RH.

## Paper proof

Let mu have density Theta(x) cosh(x/2), and kappa_p be the sum over n>=2 of the pushforwards of `Lambda(n)/sqrt(n) Theta(x) Theta(x+log n) dx` to `(log n,x)`. Chebyshev's existing square-root prefix estimate bounds the a(n)=Lambda(n)/sqrt(n) mass of n<=Y by 34 sqrt(Y).

Choose C>=0 with Theta(t)<=C exp(-4|t|). For any fixed x and finite prime set, partition by k=floor(|x-log n|). Each kth shell has a-mass <=34 exp((x+k+1)/2), and theta factor <=C exp(-4k). Summing the geometric majorant proves convergence of the whole row and bounds it by K exp(x/2). Reflection gives the opposite row K exp(-x/2).

The left and right endpoint marginals of kappa_p have densities Theta times these two rows. Both are <=2K mu, because exp(+-x/2)<=2cosh(x/2). Endpoint pullbacks are therefore L2 maps for every mass vector, including nonsmooth noncompact sources. The literal difference is everywhere defined. Its graph is closed by the existing nonsingular-endpoint graph theorem; the open mapping theorem gives a bounded inverse to the prime graph's source projection. Thus Dp is bounded, and P=Dp*Dp is bounded, positive and selfadjoint.

L2 admission for the full edge measure kappa_arch+kappa_p is exactly archimedean admission. The same-source map T between the full and archimedean closed graphs is linear and bijective. Its graph is the closed source-equality locus, so T and its inverse are continuous. Integration over the sum of measures gives exactly

`||p||full^2 = ||Tp||arch^2 + <P source(p),source(p)>`.

Polarization gives the corresponding bilinear identity. Let R be the existing full arithmetic Riesz resolvent, and Ra=S_arch S_arch* the actual archimedean graph Riesz resolvent. Riesz uniqueness gives

`Ra(w-P Rw)=Rw`, and `R(w+P Ra w)=Ra w`.

These identities prove equality of the resolvent ranges, hence equality of generator domains. They also give `R(u+v)=u iff Ra(u+v-Pu)=u`, with a bounded invertible triangular change of graph coordinates.

## Lean scope and verification

Five new leaves, 701 lines, 76 explicit declarations, namespace `RHTower.CHMDDoobGraph`:
- CHMDPrimeRowBound: full arithmetic row summability/control.
- CHMDPrimeDomain: both endpoint marginals, automatic literal admission, exact form-domain equality.
- CHMDBoundedPrimeGenerator: actual bounded difference and positive selfadjoint generator.
- CHMDArchimedeanDomain: source-preserving complete graph isomorphism and exact energy/inner-product identities.
- CHMDPrimeOperatorDomain: actual resolvent identities, exact operator-domain equality, bounded invertible generator-graph change.

Validation completed:
- Targeted `lake --old build GaloisForLFunctions.RHTower.CHMDPrimeOperatorDomain` passed, compiling every new dependency; no full or umbrella build.
- Final plain `lake env lean` passed for each of the five source files, all with empty diagnostic logs.
- All 76 declarations audited with `#print axioms` from a /tmp scratch file; exactly 76 outputs, no missing entries, only propext, Classical.choice and Quot.sound.
- 44 toolchain API probes passed.
- Every new leaf wired exactly once into the RHTower umbrella.
- Source SHA256 values match before and after final direct audits.

SHA256:
- CHMDPrimeRowBound: 1a304f3f5e9374b5fc940dd48311e75951562b68bde9fce6a6d280e101bc4068
- CHMDPrimeDomain: fe1962177a3e686ecde97aee4a38f93af9a321aaf0d1312108283e4477aad493
- CHMDBoundedPrimeGenerator: 17d66535d2cca54e1e16ce1c9294f1cba3def50ba4d285107102b93e16cfa155
- CHMDArchimedeanDomain: f01528d726ea5f2624e46a47103f3b5dac896ceba94f525538db53748a653264
- CHMDPrimeOperatorDomain: f214bdf873df1a594c780576c864d8a2cd48300bb3b555365cf406c7fa0f9afb

Global lint was rerun after concurrent edits removed the two in-progress sorries. The final gate reports exactly six unrelated unwired modules: CHMDPointwiseGenerator, CHMDThetaHarmonicIdentity, DeningerMeyerConvolutionTraceClass, DeningerMeyerFaithfulConvolution, DeningerMeyerHilbertConvolution, and DeningerMeyerHilbertConvolutionJets. It reports no proof debt. These files are not dependencies of this contribution and were left to their ongoing work. No computation, external search, extra axiom, RH premise, or assumed domain theorem is used. The finite-prime strong-limit observation on the parent card is a paper follow-up, not part of this formalised claim.

Cleanup: all 19 owned scratch/search/log files removed after their terminal tool results; no owned build, check, or search remains active. No commit or push.
