Mission: derive a genuine Hawking/Teukolsky nonlinear RH producer, avoiding classic-route proxies.

New modules:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingDarbouxHorizonPhaseMixingOpticalLaw.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTotalThirdOrderCausalCut.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedHorizonAffineProjectiveSeparation.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedHorizonSturmOpticalForm.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer.lean
All imported by formal/GaloisForLFunctions/RHTower.lean.

Main results:
1. Total retarded-minus-advanced ++- Schur causal cut cancels the common direct third Einstein jet C exactly. Any nonzero cut comes from a ++ or +- response-map jump.
2. At BM mixed frequency c=-N, N=2n+2k+2, Frobenius recurrence fixes log coefficient
   (-1)^N (a)_(N+1)(b)_(N+1)/(N!(N+1)!).
   On real momentum it is strictly positive; for complex momentum it is nonzero whenever Re chi != 0.
3. Actual Xi BM angular momentum has Re chi = Im rho/2 != 0, so complex mixed-horizon monodromy never vanishes on any Xi fibre. It is even under chi -> -chi, hence radial monodromy is shadow-blind.
4. Physical mixed BM projective boundary response is real, so its conjugation cut is zero. Nonzero causal monodromy lives in affine horizon-normalization fibre, killed by projectivization.
5. On real-momentum slice mixed BM operator has exact positive Sturm form p=sqrt(1-z)/z^N, w=p/(z(1-z)), potential |a|^2>0, with local optical law J'=w Im(conj(y) f).
6. Exact horizon source projection is eta(q) times actual BM ingoing Green coefficient times nonlinear Einstein carrier. Its norm square is horizon orthogonal-helicity flux.
7. Actual Xi causal optical section = nonzero complex BM monodromy * that horizon Gram, hence zero iff Re rho=1/2. Under mixed response incidence and Einstein-Green reciprocity, total retarded section equals advanced section iff critical line. Direct C cannot repair off-line asymmetry.

Hostile limits:
- Real-chi positivity cannot be used off the Xi line; actual chi is complex. Only nonvanishing/zero-locus survives there.
- Projective boundary Jost ratio cannot carry causal monodromy.
- Remaining hard core is actual gauge-fixed Einstein-Teukolsky angular cyclic Green pairing on BM modes (hreciprocity) plus dynamics deciding retarded/advanced section equality. Do not claim full RH until derived.
- Local same-fibre ++- frequency is not a BM QNM; causal time convolution/residue incidence must be treated when evaluating actual cokernel.

Validation:
- All six new modules compiled with targeted lake env lean.
- Key #print axioms outputs only propext, Classical.choice, Quot.sound.
- Targeted forbidden-token scan clean.
- Global formal_tools lint still fails only on pre-existing unrelated unreachable umbrella modules.
- No git, endpoint doc, or route ledger touched. Scratch cleaned.