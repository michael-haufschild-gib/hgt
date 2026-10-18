# Two-prime deletion closes complete third band (2026-10-18)

Seventh contribution to ongoing all-horizon radical sawtooth/defect research. Goal active. New formulation of classical prime Euler-factor algebra, complementary-divisor splitting and discrete polarization. No external novelty claim.

Source: formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TwoPrimeDeletionAndFullThirdBandEnvelope.lean
SHA256: 74b5080b021d4dbee345046d41aa37b137b21c7aa5219678cc7c7b3675782399
19 public theorems, 1 public definition dampedPrimeDeletionFactor, 1 private helper zero_damping_weight; 21 closures.

Exact theorem: c(u)=μ(u)u^(-ε), τ(u)=Σ_{d|u}c(d), F_p(u)=1 if p|u, otherwise 1-p^(-ε). For distinct primes p,q, all ε and natural u, A=F_p(u)F_q(u):
τ(pqu)-c(pqu)-c(qu)-c(pu)=Aτ(u)+(1-A)c(u).
Works even when p or q already divides u, including repeated valuations. Proof uses p|qu iff p|u, τ(pu)=F_p(u)τ(u), c(pu)=(F_p(u)-1)c(u).
For ε>=0, A in[0,1]. For u>=2 the existing τ(u)+|c(u)|<=1 mass bound gives absolute response<=max(A,1-A)<=1. The max bound is not claimed globally sharp.

This closes the previous missing third-band case 2|k and3|k: for 3N<k<=4N, k=2*3*u has u>=2 and complementary quotients are1,2,3. Together with old single-prime and <=3N results:
|s_N(cε,k)|<=1 for EVERY 2<=k<=4N, ε>=0, without parity or coprimality exclusions.
- Every positive power k^m of such a base inherits the envelope.
- Every observation with R_N(k)<=4N inherits the envelope, regardless of observation size.
- Prefix M>=1 with R_N(M+1)<=4N has 2D_N(M;cε)<=-E_N(M;cε)<=0.
- Hence all M+1<=4N and all k^m-1 with2<=k<=4N,m>=1 qualify.
- Rough-start short windows have the same energy inequality when right endpoint's radical representative<=4N; includes full4N short windows. No arbitrary-start claim.
- ε=0 specializes to literal moebiusReal for full range, powers, and radical fibers.

Paper/card: docs/drafts/pipeline/3-formalized/thim-two-prime-deletion-full-third-band.md.
Ledger: logs/thim-radical-sawtooth-knowledge.md (contains exact facts and verification).
Corpus searches partial=false, complete inventory74228, zero pending inventory, generations1453857/1453865; compiler metadata mixed/source-only. All candidate/source-argument lists inspected; exact APIs and full proof compiled in scratch before source.

Verification: final actual source lake --old env lean -o <leaf.olean> <leaf.lean>, exit0 no warnings. Axiom audit exit0, all21 exactly {propext, Classical.choice, Quot.sound}. Fresh .olean. Required dependency hashes revalidated: SecondAndThirdBandRenormalizedDefectCalculus=3390b32ba3798dd2e5ff7649d3d86203ac4d01834259382eae68a6998318bb8f; ShortWindowCorrelationDefectAndIsoStateClassification=e090ac704457c67f228ff7e36e8dee4696f1cfb24516ee44cf93f80ffead6f9c. Artifact audit logs/thim-two-prime-audit.json passed all21closures,20baseline/API entries, hashes/freshness, unique umbrella import, MainTheorems reachability, whitespace and forbidden declarations. Evidence logs/thim-two-prime-{lean,axioms,index,lint}.txt. Global lint exits1 with4 unrelated structural errors: ArithmeticPositivityTheory FactorialCollarIrrationalityAndSpacing, RankOnePoleReadoutAndZeroNullspace, SourceRelativeSchurMarginAndPerturbationCalculus unwired; existing THIM root registration. No new-leaf, forbidden-declaration or stale-generated-file error. All owned jobs terminal; six scratch files deleted. No full builds, computations/numerical experiments, added axioms, heartbeat changes, README edits, commits or push.

Next conjecture (NOT verified5N): in fourth band complementary quotients1,2,3,4 occur. If4|k, k=4u, squarefree support kills c(4u) and c(k/3) when3|k; the pair c(2u)+c(u) might reduce the response to F_2(u)(τ(u)-c(u)), a known single-prime contraction. If4 does not divide k, the three-channel response may already be covered after handling u=1 separately. Search current corpus again before pursuing. No assertion beyond4N.

Related: `mem:trans-horizon/second-third-band-defect-calculus` (its missing-six case is now CLOSED), `mem:trans-horizon/all-horizon-radical-sawtooth-defect`, `mem:trans-horizon/radical-state-defect-normal-form`, `mem:trans-horizon/nonnegative-endpoint-order-calibrated-defect`.
