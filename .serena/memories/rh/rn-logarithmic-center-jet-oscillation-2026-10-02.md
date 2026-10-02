# RN: cofinal two-sign logarithmic center jets

Completed and wired `formal/GaloisForLFunctions/RHTower/ThetaCuspLogJetOscillation.lean`, namespace `RHTower.ThetaLogJet`.

Unconditional public theorems `logJet_cofinal_positive` (line 403) and `logJet_cofinal_negative` (line 391): for every N, an m≥N has respectively positive/negative `iteratedDeriv (2*m) thetaCuspLogSource 0`. No conjectural source assumptions. `radius_lt_strip` (342) and coefficient cofinality (377,384) also audited.

Proof: actual imaginary source zero ζ=i*t with 0<t<π/4 has finite positive analytic order n. Euler logarithmic germ g(z)=z*φ'(z)/φ(z) has residue ζ*n≠0. Meromorphic germ propagation forces canonical Taylor radius below π/4. g is analytic at every real point. Strip-local Vivanti–Pringsheim after finite polynomial subtraction forbids either eventual coefficient sign. Odd coefficients vanish; even coefficients are positive multiples of even log jets. This concerns log source, distinct from existing source-square native-center oscillation.

Scratch proof/API checks, targeted `lake --old build GaloisForLFunctions.RHTower.ThetaCuspLogJetOscillation`, /tmp axioms audit of five public theorems, and final `lake env lean GaloisForLFunctions/RHTower/ThetaCuspLogJetOscillation.lean` all passed. Only propext/Classical.choice/Quot.sound. Lint failed on 11 unrelated unwired modules, recorded in working log; no own leaf issue. No numerical experiments, new axioms, heartbeat increase or umbrella build.

Failed branch + complete survivor paper proof: `docs/drafts/pipeline/5-failed/theta-logarithmic-one-sign-curvature.md`. RN frontier map updated. Working log: `docs/drafts/pipeline/1-in-progress/rn-singular-weight-conjecture-loop-2026-10-01.md`, RN-P-7a.

RH remains unproved/unrefuted; RN-P-7 higher Schur residual sign law is NOT falsified by this theorem. With actual leading block M and c=M⁻¹h, A=k_y-uᵀc, B=y*k_y-vᵀc, S'=−2AB. Exact projected-score system A'=W+βA+αB, B'=C+(1+γ)A+βB. Backward first-exit barriers would require W+αB<0 at A=0,B>0 and C+(1+γ)A<0 at B=0,A>0. Those actual-source estimates and simultaneous-zero control remain unproved; don't assert global residual monotonicity or write another conditional RH wrapper.

Current corpus `ThetaCuspAllRankNativeTail.nativeShiftedMatrix_posDef_eventually` only gives native shifted Hankel positivity at each fixed rank/shift on a rank-dependent cofinal ray, not full kernel compact positivity or a uniform rank threshold.