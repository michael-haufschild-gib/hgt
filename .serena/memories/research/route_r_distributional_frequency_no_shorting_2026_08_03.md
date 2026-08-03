Route R frontier movement on 2026-08-03.

Formalized a class-complete no-go for scalar distributions after modular-frequency separation.

New module:
formal/GaloisForLFunctions/RHTower/GammaSignedDistributionalOrbitNoShorting.lean

Main unconditional theorems:
- isolatedSpectrum_coeff_eq_zero
- xiGammaEulerCanonicalCrossPrimeFrequency_isolated
- xiGammaEulerCanonicalCrossPrime_distributional_noShorting
- xiGammaEulerCanonicalCrossPrimeCooriented_distributional_noShorting

Core math: if sum'_j c_j phi(lambda_j)=0 for every smooth compactly supported test function and each lambda_i is isolated, a bump supported in an isolating neighbourhood extracts c_i. Canonical lambda_(p,e;q,f)=log(p^(e+1)q^(f+1)) is isolated because exp maps it injectively to positive integers; exp^-1((N-1/2,N+1/2)) isolates log N. Actual cooriented amplitude is positive.

Interpretation: Route R's phrase "distribution-valued" cannot mean an ordinary scalar distribution after frequency separation. Survivors must be genuinely pre-frequency/operator-valued with unavailable/discontinuous full test evaluation, use a justified ordering/renormalization not represented by unordered scalar distribution, or couple coefficients to Xi-divisor provenance before spectral separation. This does NOT prove RH or arithmetic annihilation.

Docs:
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-distributional-frequency-no-shorting.md
frontier map appended with scalar distributional frequency closure.

Verification:
- direct lake env lean module: PASS
- scripts/formal_tools.py lint: PASS
- lake build GaloisForLFunctions.RHTower.GammaSignedDistributionalOrbitNoShorting: PASS
- axioms: only propext, Classical.choice, Quot.sound.
Umbrella import added to formal/GaloisForLFunctions/RHTower.lean.

Hostile novelty: isolated Dirac distribution independence is classical; new content claimed only for exact canonical prime/depth application and frontier closure. External sources audited: Encyclopedia of Mathematics Dirac delta and support of generalized function.