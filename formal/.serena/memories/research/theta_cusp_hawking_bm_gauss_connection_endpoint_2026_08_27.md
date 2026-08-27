# BM second-harmonic Gauss/connection endpoint — 2026-08-27

Lean-verified corpus additions:

- `RHTower/ThetaCuspHawkingBMSecondHarmonicGaussContiguousTransport.lean`: exact coefficient coboundaries and infinite `(a,c)` / `(b,c)` contiguous transport.
- `RHTower/ThetaCuspHawkingBMSecondHarmonicGaussCoefficientAsymptotics.lean`: exact GammaSeq coefficient identity, Gamma quotient limit, absolute summability for `Re(c-a-b)>0`, tail decay.
- `RHTower/ThetaCuspHawkingBMSecondHarmonicGaussEulerSummation.lean`: Euler-integral Gauss theorem in positive chamber.
- `RHTower/ThetaCuspHawkingBMSecondHarmonicGaussSummation.lean`: global nonresonant Gauss theorem for positive Gauss gap via explicit natural shifts and finite contiguous descent.
- `RHTower/ThetaCuspHawkingBMSecondHarmonicGaussEndpoint.lean`: BM `++` endpoint value equals literal forbidden-boundary Gamma coefficient.
- `RHTower/ThetaCuspHawkingBMSecondHarmonicGaussConnectionCoefficient.lean`: one-sided Abel continuity plus exact AdS basis limits identify Wronskian-defined forbidden/source Cramer coefficient with literal BM Gamma coefficient.

Verification: targeted build completed `11157/11157`; key `#print axioms` outputs only `propext`, `Classical.choice`, `Quot.sound`; scoped forbidden-marker and whitespace checks clean.

Exact open core: identify `d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient` with `d4BMCausalDecayingBoundaryCoefficient = Gamma(c) Gamma(-1/2)/(Gamma(a)Gamma(b))`. Best corpus-led route: use normalized coefficient theorem at fixed gap `1/2` to obtain `sqrt(n)*(n+1)t_(n+1) -> Gamma(c)/(Gamma(a)Gamma(b))`; apply `HTGeometry.CentralBinomialAbelTransfer.tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul` componentwise to derivative series; use one-sided L'Hopital on `(R(x)-R(1))/sqrt(1-x)` to get `Gamma(-1/2)` edge coefficient; compare with exact AdS connection phase. After this connection landing, hardest remaining task is physical phase-normalized augmented causal-source projection and source-global RH selection law.