# HCF: exact analytic separation of finite and escaping admissions

Status: formalized; all three direct Lean source audits and thirteen axiom audits pass. Umbrellas wired. Repository-wide lint has seven unrelated umbrella-reachability errors, listed below.

## Starting frontier

The corpus already constructs every universal escaping residue as a unique analytic scaled root branch and proves simultaneous separation. It does not yet give an exact analytic finite factor or identify its contact fibre with the regular-head admission. A complete factorization would exclude any additional intermediate escape scale and retain finite-root multiplicities through arbitrary contacts.

## Conjecture loop

1. Formal power-series Hensel factorization is available, but by itself does not certify convergence in the actual real heat parameter. Do not replace the desired analytic theorem with a formal receiver.
2. Conjecture: if analytic-coefficient S and E satisfy S=ED on a punctured neighborhood, E has nonzero constant coefficient at the contact, and D is monic of fixed degree there, then D admits a monic analytic coefficient extension. Low-coefficient triangular division proves this without a coprime-factor or simple-finite-root assumption.
3. For the actual admission, let epsilon=t-a, let S be the known analytic extension of epsilon^k P_N, and let E=product_z(epsilon X-r_z(t)). Existing branches give E(a) a nonzero constant and exact divisibility away from a. Apply triangular division; comparing leading coefficients at the contact forces the finite factor to equal P_n(a), where n is the canonical preceding head.
4. The triangular quotient-coefficient extension and monic fixed-degree extension passed focused Lean builds. Their proofs require only the constant coefficient of E to be nonzero, not a complete factorization or a simple root at the finite head.
5. The abstract escaping factorization passed a focused Lean build: distinct branch roots divide the admission, their product is monic of degree k, and undoing the common scale gives a divisor to which triangular division applies. The scaled identity holds on a full neighborhood, including the contact.
6. The actual-source capstone passed: canonical block coverage supplies every input, and the contact coefficient comparison gives exactly F(a)=P_n(a). Its only external parameters are positive time and rank. No finite-head root simplicity is needed.
7. The exhaustive root-partition corollary passed. Every nearby admission root belongs to F or equals a known escaping branch. The earlier branch construction therefore extends to a complete local factorization, including finite multiplicities and the analytic identity through the contact.

## Closed paper proof

Writing S_i, E_i, D_i for coefficients, the identity S=ED gives E_0 D_i = S_i − sum_(j=1)^i E_j D_(i−j). Since E_0(a) is nonzero, induction extends each D_i analytically. For a monic quotient of fixed degree n, use these lower coefficient extensions with the leading coefficient fixed to one. This gives an everywhere monic degree-n F agreeing with D on a punctured neighborhood. Coefficient continuity extends S=EF to the contact.

For HCF, the k branches already proved in the corpus give E(t)=product_z((t-a)X-r_z(t)). Their distinctness gives exact polynomial divisibility away from a. At a, E is a nonzero constant, while S(a)=C P_n(a), C=(d−1).descFactorial(k)≠0. Hence C P_n(a)=E(a)F(a). Both P_n and F are monic of degree n, so comparison of degree-n coefficients gives E(a)=C, and cancellation gives F(a)=P_n(a). This keeps finite collisions inside an analytic monic factor and removes the possibility of additional root escape hidden below the universal 1/(t-a) scale.

## Proven capstones

Only positive time and rank as inputs. Produce canonical n,k, an analytic monic degree-n finite factor F and the known k escaping branches, with exact P_N=F product_z(X-r_z/epsilon) on one punctured neighborhood and F(a)=P_n(a). Prove the analytic scaled identity including the contact. No bounds, RH equivalence, source-sign premise, numerical experiments, new axioms, heartbeat increases, full/umbrella builds, web or novelty searches.

Lean artifacts:

- `formal/GaloisForLFunctions/HTGeometry/AnalyticPolynomialDivisionGerm.lean`: `analytic_quotient_coeff_germ`, `analytic_monic_factor_extension`.
- `formal/GaloisForLFunctions/HTGeometry/AnalyticEscapingFactorization.lean`: `analytic_finite_factor_of_escaping_roots` and the exact escaping/scaled factor API.
- `formal/GaloisForLFunctions/RHTower/XiGaussianHeatFiniteFactor.lean`: `heat_normal_block_scaled_admission_polynomial`, `hcf_heat_admission_finite_factor`, `hcf_heat_admission_root_partition`.

## Validation

Each module passed a focused `lake --old build +GaloisForLFunctions.<area>.<module>:olean`, then its final `lake env lean GaloisForLFunctions/<area>/<module>.lean` audit from `formal/`. The final source audits returned exit 0 with no output. Sequential builds/audits only; no full or umbrella builds. Both theorem-area umbrellas import the new modules.

A separate `/tmp` scratch audit checked the Mathlib APIs used, printed axioms for all thirteen public theorems, and checked both actual capstone signatures. It passed; every printed axiom list is exactly `[propext, Classical.choice, Quot.sound]`. Scratch artifacts were removed after validation.

`scripts/formal_tools.py lint` ran and returned seven errors, all unrelated unfinished modules unreachable from the RHTower umbrella: `CHMDPrimeWindowTail`, `DeningerMeyerHorizontalInterpolation`, `DeningerMeyerStripCardinal`, `DeningerMeyerStripJetLocalization`, `DeningerMeyerStripSeries`, `DeningerMeyerUnitZeroGeometry`, `EvenSectorCompactBoundaryRigidity`. No new HCF module was reported. `git diff --check` passed for this work.

## Frontier change and remaining obstacle

Before: analytic scaled branches constructed k escaping roots, while coefficientwise cancellation identified only a projective finite limit. After: the entire actual polynomial has an exact factorization, and the finite quotient extends analytically to precisely the regular-head admission. This closes the local finite/escaping separation problem without assuming simple finite roots. The source-derived no-transition/sign-selection problem remains open; this result does not assert RH or rank-uniform positivity.

## Corpus leads

HeatEscapeSimpleRoots, AnalyticMonicRootGerm, XiGaussianHeatEscapingBranches, XiGaussianHeatAdmissionContinuation, PowerSeriesFactorization. Research searches cover analytic factorization, actual heat singular roots, and analytic inverses. The first two deep searches reported complete results and inventory; the inverse search reported partial results with complete inventory. Candidate applicability was checked in Lean. The finite triangular recurrence avoids relying on a formal-to-convergent bridge.
